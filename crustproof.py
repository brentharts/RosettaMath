#!/usr/bin/env python3
r"""crustproof.py -- the bridge from Crust's contracts to the micro-kernel.

Crust already parses contracts.  `shivyc/extensions.py` lifts

    int calc_sum(int *ptr, unsigned int len)
    assert len(ptr) >= 64
    assert not len(ptr) % 4
    { ... }

out of a C function header and hands `{'ptr': {'len>=': 64, 'div-by': 4}}`
downstream, where four whole-program passes consume it.  Each pass decides for
itself what the dict means:

    contracts._violates(length, bound)      -- a call site is an error
    simd_contracts._satisfies(count, bound) -- the scalar tail may be dropped

Two hand-written readings of one contract, and they do not agree.  `_violates`
returns on the first key it finds, so for `{'len>=': 64, 'div-by': 4}` a length
of 70 clears `len>=` and the `div-by` is never looked at: the call compiles,
while `simd_contracts` -- which conjoins every bound -- correctly refuses to
prove it.  The contract in `SIMD_CONTRACTS.md` is that contract, and 70 is the
length its own worked example uses.

That is the argument for this file.  A contract is a proposition, and a
proposition has one meaning.  Here it is turned into a term of the calculus of
constructions and settled by `lean4.py`, so both passes ask the same question
and get an answer that came with a proof.

    >>> cert = check(70, {'len>=': 64, 'div-by': 4})
    >>> cert.holds
    False
    >>> cert.statement
    'andb(dvdb(4)(70))(leb(64)(70))'

Nothing here is trusted.  The verdict is `normalize`, and when it is `true` a
proof term is built and handed to `type_check`, which is the same kernel that
checks every other theorem in this repository.
"""

import functools
import os
import sys
import threading

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import lean4 as L
import hoare as H
from hoare import BOOL, NAT, app, numeral
from lean4 import App, Lambda, Var, arrow, normalize, readable, type_check

# A contract's meaning, one clause per bound Crust knows how to parse.  The
# key is the spelling `extensions.py` produces; the value turns a bound and
# the length in question into a Bool term.
CLAUSES = {
    'len>=': lambda k, n: app('leb', numeral(k), n),
    'len<=': lambda k, n: app('leb', n, numeral(k)),
    'div-by': lambda k, n: app('dvdb', numeral(k), n),
}


class UnknownBound(H.ContractError):
    """A contract key this bridge has no reading for.

    Raised rather than ignored.  A bound that is silently dropped is a
    contract that silently does not hold, which is the failure this file
    exists to remove.
    """


def predicate(bounds):
    r"""A contract, as a term of type `Nat -> Bool`.

    Every bound is conjoined -- all of them, not the first one that matches.
    Taking the length as an argument rather than a list keeps this cheap: a
    call site with a 4096-element buffer needs a numeral, not a 4096-long
    term to walk.
    """
    unknown = set(bounds) - set(CLAUSES)
    if unknown:
        raise UnknownBound(
            f"no reading for contract bound(s) {', '.join(sorted(unknown))}; "
            f"this bridge knows {', '.join(sorted(CLAUSES))}")
    if not bounds:
        raise UnknownBound("an empty contract says nothing; there is no "
                           "proposition to prove")
    n = Var('n')
    parts = [CLAUSES[key](bounds[key], n) for key in sorted(bounds)]
    body = parts[0]
    for part in parts[1:]:
        body = app('andb', body, part)
    return Lambda('n', NAT, body)


class Certificate:
    """What was asked, what the answer was, and the proof when there is one."""

    def __init__(self, length, bounds, holds, statement, proof=None,
                 reason=''):
        self.length = length
        self.bounds = dict(bounds)
        self.holds = holds
        self.statement = statement
        self.proof = proof
        self.reason = reason

    def as_dict(self):
        """A form a compiler pass can log or write out."""
        return {'length': self.length, 'bounds': self.bounds,
                'holds': self.holds, 'statement': self.statement,
                'checked_by': 'lean4.py', 'reason': self.reason}

    def __str__(self):
        if self.holds:
            return (f"proved: {self.statement} at length {self.length}, "
                    f"checked by lean4.py")
        return (f"not proved: {self.statement} at length {self.length} "
                f"computes to false")

    def __repr__(self):
        return f"<certificate {'holds' if self.holds else 'fails'}>"


def _deep(work):
    """Run on a thread with room: a numeral is as deep as it is large."""
    out = []
    thread = threading.Thread(target=lambda: out.append(_guard(work)))
    thread.start()
    thread.join()
    if not out:
        raise H.ContractError("the proof check did not finish")
    result, error = out[0]
    if error is not None:
        raise error
    return result


def _guard(work):
    try:
        return work(), None
    except BaseException as exc:            # carried back to the caller
        return None, exc


threading.stack_size(512 * 1024 * 1024)
sys.setrecursionlimit(300000)


@functools.lru_cache(maxsize=4096)
def _check(length, items):
    bounds = dict(items)
    # Substituted here rather than left as `(lam n. ...) 64`.  Normalising an
    # application normalises the function first, which means walking into the
    # contract with `n` still a variable and unfolding every definition it
    # mentions -- the exact work the literal has been supplied to avoid.
    claim = L.instantiate(predicate(bounds).body, numeral(length))
    statement = readable(claim)

    def work():
        value = normalize(claim, H.PRELUDE_ENV)
        if value != Var('true'):
            return Certificate(length, bounds, False, statement,
                               reason=f"computes to {readable(value)}")
        goal = App(Var('Holds'), claim)
        proof = app('refl', BOOL, Var('true'))
        actual = type_check(H.PRELUDE_ENV, proof)
        if not L.definitionally_equal(goal, actual, H.PRELUDE_ENV):
            raise H.ContractError(
                f"the kernel would not accept the proof of {statement}")
        return Certificate(length, bounds, True, statement, proof)

    return _deep(work)


#: `Nat` is unary, so the term for a length has that many nodes.  Reducing it
#: is now constant time -- the accelerators see a numeral and do arithmetic --
#: but *building* one is still linear, and past a million nodes the recursive
#: walk that hashes it runs out of stack.  This is the representation showing
#: through, and the honest place to say so is here rather than in a traceback.
NUMERAL_LIMIT = 200_000


def check(length, bounds):
    """Settle a contract at a known length, and say how it was settled."""
    if length < 0:
        raise H.ContractError("a length is a Nat; there is no negative one")
    if length > NUMERAL_LIMIT:
        raise H.ContractError(
            f"length {length} is past what a unary numeral can be built for "
            f"({NUMERAL_LIMIT}); the term would have that many nodes")
    return _check(length, tuple(sorted(bounds.items())))


# ------------------------------------------------ what the passes ask for

def satisfies(length, bounds):
    """Does a known length meet the contract?  The reading `_satisfies` wants."""
    return check(length, bounds).holds


def violates(length, bounds):
    """Does it break the contract?  The reading `_violates` wants."""
    return not check(length, bounds).holds


def explain(length, bounds):
    """A line a compiler can put in a report."""
    return str(check(length, bounds))


# ------------------------------------------------------------- self test

def selftest():
    """Including a differential test against Crust's own two readings."""
    checks = [0, 0]

    def ok(label, condition):
        checks[0] += 1
        if condition:
            checks[1] += 1
        else:
            print(f"  FAILED: {label}")

    def refuses(label, thunk, fragment):
        checks[0] += 1
        try:
            thunk()
        except (H.ContractError, L.KernelError) as exc:
            if fragment in str(exc):
                checks[1] += 1
            else:
                print(f"  FAILED: {label}: wrong reason: {exc}")
            return
        print(f"  FAILED: {label}: accepted what it should refuse")

    simd = {'len>=': 64, 'div-by': 4}
    ok("the SIMD contract holds at 64", satisfies(64, simd))
    ok("and at 128", satisfies(128, simd))
    ok("not at 60 (too short)", not satisfies(60, simd))
    ok("not at 66 (not a multiple of 4)", not satisfies(66, simd))
    ok("not at 70 (both readings' disagreement)", not satisfies(70, simd))
    ok("violates is the negation", violates(70, simd) and not violates(64, simd))

    ok("len<= alone", satisfies(3, {'len<=': 8})
       and not satisfies(9, {'len<=': 8}))
    ok("div-by alone", satisfies(12, {'div-by': 4})
       and not satisfies(13, {'div-by': 4}))
    ok("a range", satisfies(8, {'len>=': 4, 'len<=': 16})
       and not satisfies(2, {'len>=': 4, 'len<=': 16}))
    ok("zero length", satisfies(0, {'div-by': 4})
       and not satisfies(0, {'len>=': 1}))

    cert = check(64, simd)
    ok("a passing check carries a proof", cert.proof is not None)
    ok("a failing check carries none", check(70, simd).proof is None)
    ok("and says why", 'false' in check(70, simd).reason)
    ok("the certificate names its checker",
       cert.as_dict()['checked_by'] == 'lean4.py')
    ok("the statement conjoins every bound",
       'dvdb' in cert.statement and 'leb' in cert.statement)

    refuses("an unknown bound is refused, not dropped",
            lambda: check(64, {'align': 16}), "no reading for contract bound")
    refuses("an empty contract is refused",
            lambda: check(64, {}), "says nothing")
    refuses("a negative length is refused",
            lambda: check(-1, simd), "no negative one")

    # -- the differential test ---------------------------------------------
    # Not a formality.  Run first, it found that Crust's two passes read one
    # contract two ways; `shivyc/proofs.py` is the single reading that came out
    # of it, and this is what keeps them together.
    crust = _find_crust()
    if crust is None:
        print("  (crust not found; skipping the differential test)")
    else:
        from shivyc.contracts import _violates
        from shivyc.simd_contracts import _satisfies
        grid = [{'len>=': 64}, {'len<=': 8}, {'div-by': 4},
                {'len>=': 64, 'div-by': 4}, {'len>=': 4, 'len<=': 16},
                {'len>=': 8, 'len<=': 64, 'div-by': 8}]
        lengths = list(range(0, 130))
        cases = [(b, n) for b in grid for n in lengths]
        ok("the kernel agrees with simd_contracts._satisfies on every case",
           all(satisfies(n, b) == _satisfies(n, b) for b, n in cases))
        ok("and with contracts._violates on every case",
           all(violates(n, b) == _violates(n, b) for b, n in cases))

        # the reading that was there before, kept as a regression: it stopped
        # at the first clause present, so a length could clear that one and
        # break another without the compiler ever looking
        def first_clause_only(length, bound):
            for key, broken in (("len<=", lambda k: length > k),
                                ("len>=", lambda k: length < k),
                                ("div-by", lambda k: length % k != 0)):
                if key in bound:
                    return broken(bound[key])
            return False

        missed = [(b, n) for b, n in cases
                  if violates(n, b) and not first_clause_only(n, b)]
        ok("the old first-clause reading missed violations", bool(missed))
        if missed:
            counts = sorted({tuple(sorted(b)) for b, _ in missed})
            print(f"  the reading Crust had missed {len(missed)} of "
                  f"{len(cases)} cases, all multi-clause: {counts}")
            bound, length = missed[0]
            print(f"  first: {bound} at length {length} -- broken, and it "
                  f"compiled")

    print(f"{checks[0]} checks, "
          f"{'all passed' if checks[0] == checks[1] else f'{checks[0]-checks[1]} FAILED'}")
    return checks[0] == checks[1]


def _find_crust():
    """Crust, if it is sitting somewhere obvious."""
    candidates = [os.environ.get('CRUST_DIR'),
                  os.path.join(os.path.dirname(os.path.abspath(__file__)),
                               '..', 'crust'),
                  os.path.expanduser('~/crust')]
    for path in candidates:
        if path and os.path.isdir(os.path.join(path, 'shivyc')):
            full = os.path.abspath(path)
            if full not in sys.path:
                sys.path.insert(0, full)
            return full
    return None


if __name__ == '__main__':
    sys.exit(0 if selftest() else 1)
