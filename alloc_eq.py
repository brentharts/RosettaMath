#!/usr/bin/env python3
r"""alloc_eq.py -- LeanOS's per-thread bump allocator, modelled and proved.

`leanos/alloc.py` moves a counter `used` up a region the thread owns, if the
request fits, and otherwise leaves it.  Three theorems, all Lean-accepted:

  bump_bounded     used <= size  ->  bump ... used n <= size.  The guard is
                   the invariant.
  bump_monotone    used <= bump ... used n.  Allocation never gives back.
  slot_in_bounds   used < size  ->  base <= base + used < base + size.
                   The slot handed out is inside the region: the two
                   guards `contains` tests, as arithmetic.

The third is stated as arithmetic rather than through `contains` because
`contains` also tests that `heap` is an index and that `sizes` is long
enough, and those are preconditions of the caller, not facts about the
allocator.  A caller with them in hand composes this with `contains`'s
guards directly.
"""
import inspect
import textwrap

import lean4 as L
import hoare as H
import memmap_eq
from lean4 import Var, Lambda, Pi, App
from hoare import app, procedure, define, arrow, NAT, BOOL, BYTES

SOURCES = {}


def remember(func):
    SOURCES[func.__name__] = textwrap.dedent(inspect.getsource(func))
    return func


def build(verbose=False):
    env, facts, model = memmap_eq.build(verbose=verbose)
    sigs = {'contains': ([BYTES, BYTES, NAT, NAT], NAT)}

    @remember
    @procedure(env=env, verbose=verbose, ensures=['used <= result'])
    def bump(bases: 'Array', sizes: 'Array', owners: 'Array',
             tid: 'Nat', heap: 'Nat', used: 'Nat', n: 'Nat') -> 'Nat':
        if heap < len(bases):
            if owners[heap] == tid + 1:
                if used + n <= sizes[heap]:
                    return used + n
        return used

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result == bases[heap] + used'])
    def slot_addr(bases: 'Array', heap: 'Nat', used: 'Nat') -> 'Nat':
        return bases[heap] + used

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'],
               signatures=sigs)
    def slot_ok(bases: 'Array', sizes: 'Array', heap: 'Nat',
                used: 'Nat') -> 'Nat':
        if contains(bases, sizes, heap, bases[heap] + used) == 1:
            return 1
        return 0

    for fn in (bump, slot_addr, slot_ok):
        model[fn.__name__] = fn

    b, s, o = Var('bases'), Var('sizes'), Var('owners')
    tid, heap, used, n = Var('tid'), Var('heap'), Var('used'), Var('n')
    nth = lambda xs, i: app('nth', NAT, L.numeral(0), xs, i)
    size = nth(s, heap)
    base = nth(b, heap)
    bumped = app('bump', b, s, o, tid, heap, used, n)
    opened = H.unfold(bumped, env, {'bump'})
    params = [('bases', BYTES), ('sizes', BYTES), ('owners', BYTES),
              ('tid', NAT), ('heap', NAT), ('used', NAT), ('n', NAT)]

    def close(stmt, term, hyps=()):
        for name, ty in reversed(hyps):
            stmt = arrow(ty, stmt)
            term = Lambda(name, ty, term)
        for name, ty in reversed(params):
            stmt = Pi(name, ty, stmt)
            term = Lambda(name, ty, term)
        return stmt, term

    # -- bump_bounded: the guard is the invariant -----------------------------
    hyp = app('Holds', app('leb', used, size))
    goal = app('Holds', app('leb', opened, size))
    pf = H.bound_by_ites_or_guards(env, goal, Var('h'), hyp)
    stmt, term = close(app('Holds', app('leb', bumped, size)), pf, [('h', hyp)])
    define(env, 'bump_bounded', stmt, H.prove(stmt, term, env, verbose=False))
    facts['bump_bounded'] = stmt

    # -- bump_monotone: used <= used + n, or used <= used --------------------
    goal = app('Holds', app('leb', used, opened))
    pf = H.bound_by_ites_or_guards(
        env, goal, None, app('Holds', Var('false')),
        others=[(app('Holds', app('leb', used, app('add', used, n))),
                 app('le_add_right', used, n))])
    stmt, term = close(app('Holds', app('leb', used, bumped)), pf)
    define(env, 'bump_monotone', stmt, H.prove(stmt, term, env, verbose=False))
    facts['bump_monotone'] = stmt

    # -- slot_in_bounds: base <= base + used < base + size -------------------
    addr = app('add', base, used)
    hyp = app('Holds', app('ltb', used, size))
    lower = app('le_add_right', base, used)
    # ltb used size is leb (succ used) size; add b (succ used) is succ (add b used)
    upper = app('add_le_add_left', base, App(Var('succ'), used), size, Var('h'))
    both = app('andb_both', app('leb', base, addr), app('ltb', addr, app('add', base, size)),
               lower, upper)
    stmt, term = close(app('Holds', app('andb', app('leb', base, addr),
                                        app('ltb', addr, app('add', base, size)))),
                       both, [('h', hyp)])
    define(env, 'slot_in_bounds', stmt, H.prove(stmt, term, env, verbose=False))
    facts['slot_in_bounds'] = stmt
    return env, facts, model


THEOREMS = ['bump_bounded', 'bump_monotone', 'slot_in_bounds']


def lean_source(env):
    import leanexport as X
    slow = H.prelude(fast=False)
    values = {n: L.value_of(slow, n) for n in H.ACCELERATED}
    src, _ = X.export(env, THEOREMS, values,
                      ['#print axioms ' + t for t in THEOREMS])
    return src


if __name__ == '__main__':
    import sys
    import threading

    def main():
        sys.setrecursionlimit(300000)
        env, facts, _ = build()
        for name in THEOREMS:
            print('proved', name, ':', L.readable(facts[name])[:160])
        src = lean_source(env)
        with open('Alloc.lean', 'w') as fh:
            fh.write(src)
        print('wrote Alloc.lean (%d lines)' % src.count('\n'))

    threading.stack_size(512 * 1024 * 1024)
    t = threading.Thread(target=main)
    t.start()
    t.join()
