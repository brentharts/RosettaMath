#!/usr/bin/env python3
r"""elfcheck_eq.py -- the CrustOS ELF validator, modelled and proved.

`crustos/elfcheck.py` in the crust tree is what the loader asks before it maps
an ELF: are the loads in order and disjoint, is the entry inside one, is the
register hint one the scheduler can size.  It is rpython, and it decides
rather than dereferences, so every function in it is over Nat and lists of
Nat -- the fragment `hoare.py` reads.

This file is that validator again, statement for statement, in the dialect
`read_procedure` compiles, with the theorems the loader wants:

  reg_class_sized   an accepted register class is <= 3, which is the domain
                    of `elf_regs_for_class`, whose bound `<= 23` was already
                    lifted from the kernel and accepted by Lean.  Together:
                    an accepted image has a bounded save/restore.
  accept_sized      the same, through `accept_image`: whatever `reg_class_ok`
                    guarantees, an accepted image has.

Both are chains of guards, so both are settled by `by_every_bool`: split each
`ite` and compute.  The two loop functions, `loads_ordered` and
`entry_in_load`, each carry `result <= 1` through their loop by
`early_return_bound`.  What they do not yet carry -- that an accepted
image's loads do not overlap, that its entry is inside one -- is quantified
over positions in a list, and waits on the `allb` primitive described in
`memmap_eq.py`.

The paraphrases between this and the rpython, each forced by the encoding:

  * `'Array'` for `list[int]`.  Same type, the kernel's name for it.
  * `assert invariant(...)` / `assert variant(...)` in each loop.  The
    kernel states neither; the lowering needs both.
  * `vaddrs[i]` past the end is 0 here and an IndexError there.  The
    length check at the top of each function keeps every read in range,
    so neither side ever sees the difference; the test corpus includes the
    short-list case to say so.

tests/test_elfcheck_model.py in the crust tree runs the rpython and *these
compiled terms* over one corpus and requires them to agree.
"""
import inspect
import textwrap

import lean4 as L
import hoare as H
from lean4 import App, Lambda, Pi, Var
from hoare import app, procedure, NAT, BYTES

SOURCES = {}


def remember(func):
    SOURCES[func.__name__] = textwrap.dedent(inspect.getsource(func))
    return func


# The loop annotations are read by the lowering, never run.
def invariant(*_):
    return True


def variant(*_):
    return True


def build(verbose=False, env=None, facts=None, model=None):
    """The validator model from the prelude up, every proof checked.

    Given an environment, builds into it: LeanOS's loader wants the
    validator and the region list in one place."""
    env = H.prelude() if env is None else env
    facts = {} if facts is None else facts
    model = {} if model is None else model

    # -- the guard chains ----------------------------------------------------
    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'])
    def reg_class_ok(cls: 'Nat') -> 'Nat':
        if cls <= 3:
            return 1
        return 0

    # -- the loops -----------------------------------------------------------
    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'])
    def loads_ordered(vaddrs: 'Array', memszs: 'Array') -> 'Nat':
        if len(memszs) < len(vaddrs):
            return 0
        end = 0
        i = 0
        while i < len(vaddrs):
            assert invariant(i <= len(vaddrs) and _return_value <= 1)
            assert variant(len(vaddrs) - i)
            if vaddrs[i] < end:
                return 0
            end = vaddrs[i] + memszs[i]
            i = i + 1
        return 1

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'])
    def entry_in_load(vaddrs: 'Array', memszs: 'Array',
                      entry: 'Nat') -> 'Nat':
        if len(memszs) < len(vaddrs):
            return 0
        i = 0
        while i < len(vaddrs):
            assert invariant(i <= len(vaddrs) and _return_value <= 1)
            assert variant(len(vaddrs) - i)
            if vaddrs[i] <= entry:
                if entry < vaddrs[i] + memszs[i]:
                    return 1
            i = i + 1
        return 0

    # -- the decision --------------------------------------------------------
    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'])
    def accept_image(vaddrs: 'Array', memszs: 'Array', entry: 'Nat',
               cls: 'Nat') -> 'Nat':
        if reg_class_ok(cls) == 0:
            return 0
        if loads_ordered(vaddrs, memszs) == 0:
            return 0
        if entry_in_load(vaddrs, memszs, entry) == 0:
            return 0
        return 1

    for fn in (reg_class_ok, loads_ordered, entry_in_load, accept_image):
        model[fn.__name__] = fn

    # -- the loops: result <= 1, by the early-return recipe -------------------
    for fn, fall in ((loads_ordered, 1), (entry_in_load, 0)):
        proc = fn.lean_procedure
        pf = H.early_return_bound(env, proc, 1, over='vaddrs', fallthrough=fall)
        L.define(env, fn.__name__ + '_bounded', proc.obligation, pf)
        facts[fn.__name__ + '_bounded'] = proc.obligation

    # -- theorems ------------------------------------------------------------
    # `f(...) == 1  ->  cls <= 3`, written as a Bool the kernel can compute
    # once each guard is decided:  orb (notb (eqb f 1)) (leb cls 3).
    def implies(f_term, cls):
        return app('orb',
                   app('notb', app('eqb', f_term, L.numeral(1))),
                   app('leb', cls, L.numeral(3)))

    cls = Var('cls')
    sized = Pi('cls', NAT, app('Holds',
               implies(app('reg_class_ok', cls), cls)))
    sized_pf = H.by_every_bool(env, sized, unfolding={'reg_class_ok'})
    L.define(env, 'reg_class_sized', sized, sized_pf)
    facts['reg_class_sized'] = sized

    v, m, e = Var('vaddrs'), Var('memszs'), Var('entry')
    through = Pi('vaddrs', BYTES, Pi('memszs', BYTES, Pi('entry', NAT,
              Pi('cls', NAT, app('Holds',
                 implies(app('accept_image', v, m, e, cls), cls))))))
    through_pf = H.by_every_bool(env, through,
                                 unfolding={'accept_image', 'reg_class_ok'})
    L.define(env, 'accept_sized', through, through_pf)
    facts['accept_sized'] = through

    return env, facts, model


def lean_source(env):
    """The theorems as Lean 4, for a second kernel to check."""
    import leanexport as X
    slow = H.prelude(fast=False)
    values = {n: L.value_of(slow, n) for n in H.ACCELERATED}
    names = ['loads_ordered_bounded', 'entry_in_load_bounded',
             'reg_class_sized', 'accept_sized']
    src, _ = X.export(env, names, values, ['#print axioms ' + n for n in names])
    return src


if __name__ == '__main__':
    import sys
    import threading

    def main():
        sys.setrecursionlimit(300000)
        env, facts, model = build(verbose=True)
        for name in facts:
            print('proved', name, ':', L.readable(facts[name]))
        src = lean_source(env)
        with open('ElfCheck.lean', 'w') as fh:
            fh.write(src)
        print('wrote ElfCheck.lean (%d lines)' % src.count('\n'))

    threading.stack_size(512 * 1024 * 1024)
    t = threading.Thread(target=main)
    t.start()
    t.join()
