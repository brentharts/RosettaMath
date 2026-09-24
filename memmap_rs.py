#!/usr/bin/env python3
r"""memmap_rs.py -- LeanOS's founding theorems, about the Rust region list.

`memmap_eq.py` proves what LeanOS rests on about a model of
`leanos/memmap.py` typed out by hand:

  regions_pairwise_disjoint   regions_disjoint == 1  ->  for every j < k,
                              region j ends at or before region k begins
  region_of_unique            region_of says 1 for at most one owner

This file proves the same two, stated identically, about `leanos/memmap.rs`
in the crust tree -- the functions `shivyc/rustproof.py` lifts from the
Rust, not a copy of them.  Nothing is transcribed.

Most of the argument is about a *specification*, `ordered_prefix` over
`in_order_at`, and names no model: that consecutive positions in order make
every pair in order (`ordered_guard_at`, `regions_adjacent_disjoint`,
`regions_pairwise_disjoint`), and that two positions holding one address are
one position (`contains_unique`).  Those are `memmap_eq.py`'s own proofs,
run here unchanged.  What is new is the bridge from the Rust to the
specification, and it is where the port's differences are met:

  regions_disjoint_ordered    the lifted checker says 1  ->  ordered_prefix
                              at len(bases).  Proved through the lifted loop
                              by `hoare.by_loop`, with the loop's invariant
                              strengthened by `ordered_prefix` at the
                              counter.  The Rust tests `bases[i] <
                              bases[i-1] || bases[i] - bases[i-1] <
                              sizes[i-1]`, which never forms the sum; the
                              specification's guard is `bases[i] <
                              bases[i-1] + sizes[i-1]`.  Over the naturals
                              the two agree, and `add_le_of_le_sub_r` is
                              the step between them.
  region_index_found_rs       the Rust contract on `region_index`, proved by
                              `tools/rustprove.py` too: the index returned is
                              owned by `who` and holds `addr`, in the
                              checked form `addr - base < size`.
  region_index_found          the same, in the specification's form
                              `addr < base + size`, by `lt_add_of_sub_lt`.

and `region_of_unique` is then `memmap_eq.py`'s composition proof, run
unchanged over the Rust's `region_of`, `region_index` and `regions_disjoint`
-- they have the Python's names and argument order, which is all it asks.

Every theorem is checked by the kernel here and, with Lean 4 on PATH, by
Lean from the one exported file.

    python3 memmap_rs.py              # prove, write MemMapRs.lean, run lean
"""
import os
import shutil
import subprocess
import sys

import lean4 as L
import hoare as H
import memmap_eq as M
from lean4 import Var, Pi
from hoare import app, NAT, BOOL, BYTES

HERE = os.path.dirname(os.path.abspath(__file__))
CRUST = os.environ.get('CRUST_DIR') or os.path.join(HERE, '..', 'crust')

THEOREMS = ['region_of_unique', 'regions_pairwise_disjoint',
            'regions_disjoint_ordered', 'region_index_found',
            'region_index_found_rs', 'contains_unique',
            'regions_adjacent_disjoint', 'ordered_guard_at', 'ordered_step']


def _crust():
    for p in (CRUST, os.path.join(CRUST, 'tools')):
        if p not in sys.path:
            sys.path.insert(0, p)
    import rustprove
    from shivyc.rustproof import lift_all, signatures
    return rustprove, lift_all, signatures


def build():
    """The environment: the specification and its lemmas, the lifted Rust,
    and every theorem above, each checked as it is defined."""
    rustprove, lift_all, signatures = _crust()
    env = H.prelude()
    facts = {}

    # -- the specification, and what follows from it -- no model named ------
    M.define_spec(env)
    M._prove_pairwise(env, facts)
    M._prove_unique(env, facts)

    # -- the Rust, lifted ------------------------------------------------------
    unit, own = rustprove.load_unit(os.path.join(CRUST, 'leanos',
                                                 'memmap.rs'))
    lifted, refused = lift_all(unit)
    assert not refused, refused
    kinds = {'Nat': NAT, 'Bool': BOOL, 'Array': BYTES}

    def sig_of(fn, extra=None):
        out = {n: ([kinds[t] for t in args], kinds[ret])
               for n, (args, ret) in signatures(fn).items()}
        out.update(extra or {})
        return out

    b, s, o = Var('bases'), Var('sizes'), Var('owners')
    one = L.numeral(1)

    # -- the bridge: the lifted checker decides the specification --------------
    fn = lifted['regions_disjoint']
    text = rustprove._strengthened(fn.source, [
        "(not _returned) or (_return_value == 0)",
        "(_returned) or (ordered_prefix(bases, sizes, i))"], guarded=True)
    proc = H.read_procedure(text, env, sig_of(fn, {
        'ordered_prefix': ([BYTES, BYTES, NAT], BOOL)}), fn.ensures)
    stmt = Pi('bases', BYTES, Pi('sizes', BYTES, app('Holds', app(
        'orb', app('notb', app('eqb', app('regions_disjoint', b, s), one)),
        app('ordered_prefix', b, s, app('len', NAT, b))))))
    pf = H.by_loop(env, proc, goal=stmt, unfolding={'regions_disjoint'},
                   steps={'ordered_prefix'})
    L.define(env, 'regions_disjoint_ordered', stmt, pf)

    # -- the witness: region_index vouches for the index it returns -------------
    fn = lifted['region_index']
    found = [e for e in fn.ensures if 'owners' in e]
    assert len(found) == 1, fn.ensures
    text = rustprove._strengthened(fn.source, [
        "(not _returned) or (%s)"
        % rustprove._renamed(found[0], 'result', '_return_value')],
        guarded=True)
    proc = H.read_procedure(text, env, sig_of(fn), found)
    pf = H.by_loop(env, proc, unfolding={'region_index'})
    L.define(env, 'region_index_found_rs', proc.obligation, pf)

    # the same, in the specification's form: addr < base + size
    w, addr = Var('who'), Var('addr')
    r = app('region_index', b, s, o, w, addr)
    nth = lambda xs, i: app('nth', NAT, L.numeral(0), xs, i)
    spec_found = app('orb', app('eqb', r, app('len', NAT, b)), app(
        'andb', app('andb', app('eqb', nth(o, r), w),
                    app('leb', nth(b, r), addr)),
        app('ltb', addr, app('add', nth(b, r), nth(s, r)))))
    params = [('bases', BYTES), ('sizes', BYTES), ('owners', BYTES),
              ('who', NAT), ('addr', NAT)]
    stmt = app('Holds', spec_found)
    for name, ty in reversed(params):
        stmt = Pi(name, ty, stmt)
    rs = L.type_of(env, 'region_index_found_rs')
    for name, _ in params:
        rs = L.instantiate(rs.body, Var(name))
    pf = H.by_bounds(env, stmt, facts=[(rs, app(
        'region_index_found_rs', *[Var(n) for n, _ in params]))])
    L.define(env, 'region_index_found', stmt, pf)

    # -- region_of, and the founding rule over it -------------------------------
    fn = lifted['region_of']
    H.read_procedure(fn.source, env, sig_of(fn), ['result == result'])
    M._prove_owner_unique(env, facts)
    return env


# Stated identically to memmap_eq.py's: the same term, not a paraphrase.
SAME_AS_HAND = ['region_of_unique', 'regions_pairwise_disjoint',
                'regions_disjoint_ordered', 'region_index_found',
                'contains_unique']


def checks(env):
    """What a run re-establishes, beyond the proofs themselves:

      * each theorem in SAME_AS_HAND has, here and in `memmap_eq.py`, the
        same statement, term for term -- only the model under it differs;
      * `regions_disjoint` here is the Rust: its loop forms
        `bases[i] - bases[i - 1]` and never `bases[i - 1] + sizes[i - 1]`;
      * a Rust with the size check deleted -- overlapping regions pass -- is
        refused at the bridge, and only because `ordered_prefix` is not
        kept: without it, the same loop proves.
    """
    out = []
    hand, _facts, _model = M.build()
    for name in SAME_AS_HAND:
        out.append(('%s is stated as memmap_eq.py states it' % name,
                    L.type_of(env, name).key() == L.type_of(hand, name).key()))
    pass1 = H.readable(L.value_of(env, 'regions_disjoint.pass1'))
    out.append(('regions_disjoint is the Rust: the checked subtraction',
                'sub(nth(Nat)(0)(bases)' in pass1
                and 'add(nth(Nat)(0)(bases)' not in pass1))
    out.append(('a Rust without the size check: the bridge is refused',
                _bridge_on(_without_size_check(), with_prefix=True) is False))
    out.append(('... and only for ordered_prefix: without it, it proves',
                _bridge_on(_without_size_check(), with_prefix=False) is True))
    return out


def _without_size_check():
    with open(os.path.join(CRUST, 'leanos', 'memmap.rs')) as fh:
        text = fh.read()
    cut = ('            if bases[i] - bases[i - 1] < sizes[i - 1] {\n'
           '                return 0;\n'
           '            }\n')
    assert text.count(cut) == 1, 'the size check moved; update this check'
    return text.replace(cut, '')


def _bridge_on(source, with_prefix):
    """True if the bridge's loop proof goes through on `source`."""
    rustprove, lift_all, _ = _crust()
    lifted, _ = lift_all(source)
    fn = lifted['regions_disjoint']
    extra = ["(not _returned) or (_return_value == 0)"]
    if with_prefix:
        extra.append("(_returned) or (ordered_prefix(bases, sizes, i))")
    env = H.prelude()
    M.define_spec(env)
    proc = H.read_procedure(
        rustprove._strengthened(fn.source, extra, guarded=True), env,
        {'ordered_prefix': ([BYTES, BYTES, NAT], BOOL)}, ['result <= 1'])
    try:
        H.by_loop(env, proc, unfolding={'regions_disjoint'},
                  steps={'ordered_prefix'})
        return True
    except (H.TheoremError, L.KernelError):
        return False


def lean_source(env):
    import leanexport as X
    slow = H.prelude(fast=False)
    values = {n: L.value_of(slow, n) for n in H.ACCELERATED}
    src, _ = X.export(env, THEOREMS, values,
                      ['#print axioms %s' % t for t in THEOREMS])
    return src


def find_lean():
    return shutil.which('lean') or next(
        (p for p in (os.path.expanduser('~/.local/lean/bin/lean'),
                     os.path.expanduser('~/.elan/bin/lean'))
         if os.path.exists(p)), None)


def main():
    env = build()
    for name in THEOREMS:
        print('proved %s' % name)
    failed = 0
    for label, ok in checks(env):
        print('%s %s' % ('ok  ' if ok else 'FAIL', label))
        failed += not ok
    path = os.path.join(HERE, 'MemMapRs.lean')
    with open(path, 'w') as fh:
        fh.write(lean_source(env))
    lean = find_lean()
    if lean is None:
        print('wrote %s (lean not found)' % path)
        return 1 if failed else 0
    run = subprocess.run([lean, path], capture_output=True, text=True)
    free = [t for t in THEOREMS if "'RM.%s' does not depend on any axioms"
            % t in run.stdout]
    print('Lean 4: %s, %d of %d theorems depending on no axioms'
          % ('accepted' if run.returncode == 0 else 'REJECTED',
             len(free), len(THEOREMS)))
    if run.returncode != 0:
        print(run.stdout[-3000:] + run.stderr[-2000:])
    return 0 if run.returncode == 0 and len(free) == len(THEOREMS) \
        and not failed else 1


if __name__ == '__main__':
    import threading
    threading.stack_size(512 * 1024 * 1024)
    sys.setrecursionlimit(300000)
    rc = []
    t = threading.Thread(target=lambda: rc.append(main()))
    t.start()
    t.join()
    sys.exit(rc[0] if rc else 1)
