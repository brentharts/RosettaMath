#!/usr/bin/env python3
r"""threads_eq.py -- LeanOS threads, modelled and proved.

`leanos/threads.py` is a thread as a record over the region list: an owner
and a stack pointer, with `sp_ok` the access rule applied to the stack and
`sp_after_push` a guarded update.  The theorems are corollaries of
`region_of_unique`, which is the point of the design:

  push_keeps_sp_ok   if a thread's stack pointer is in its region, it still
                     is after `sp_after_push`, however large `n` is.  The
                     guard is the invariant, so preservation is the guard.
  sp_no_cross        if two threads' stack pointers coincide and each is in
                     its own region, they are the same thread.  A thread
                     cannot point into another's stack.  This is
                     `region_of_unique` through `sp_ok`, plus that `succ`
                     is injective.

`all_sps_ok` is modelled and evaluated; its loop theorem is the
`early_return_bound` shape and is left for when a caller needs it.

Paraphrases as in `memmap_eq.py`: `'Array'` for both list types, and
`assert invariant`/`variant` in the loop.  `sp_ok` and `sp_after_push` call
`region_of` and `sp_ok`, which the model reaches by signature.
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


def invariant(*_):
    return True


def variant(*_):
    return True


def build(verbose=False):
    env, facts, model = memmap_eq.build(verbose=verbose)
    sigs = {'region_of': ([BYTES, BYTES, BYTES, NAT, NAT], NAT),
            'sp_ok': ([BYTES, BYTES, BYTES, NAT, NAT], NAT)}

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result == tid + 1'])
    def thread_owner(tid: 'Nat') -> 'Nat':
        return tid + 1

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'],
               signatures=sigs)
    def sp_ok(bases: 'Array', sizes: 'Array', owners: 'Array',
              tid: 'Nat', sp: 'Nat') -> 'Nat':
        if region_of(bases, sizes, owners, tid + 1, sp) == 1:
            return 1
        return 0

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'],
               signatures=sigs)
    def all_sps_ok(bases: 'Array', sizes: 'Array', owners: 'Array',
                   sps: 'Array') -> 'Nat':
        i = 0
        while i < len(sps):
            assert invariant(i <= len(sps) and _return_value <= 1)
            assert variant(len(sps) - i)
            if sp_ok(bases, sizes, owners, i, sps[i]) == 0:
                return 0
            i = i + 1
        return 1

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= sp'],
               signatures=sigs)
    def sp_after_push(bases: 'Array', sizes: 'Array', owners: 'Array',
                      tid: 'Nat', sp: 'Nat', n: 'Nat') -> 'Nat':
        if n <= sp:
            if sp_ok(bases, sizes, owners, tid, sp - n) == 1:
                return sp - n
        return sp

    for fn in (thread_owner, sp_ok, all_sps_ok, sp_after_push):
        model[fn.__name__] = fn

    _prove_push(env, facts)
    _prove_no_cross(env, facts)
    return env, facts, model


def _guard_from_one(env, one_claim, guard, opened, hyp):
    """From `Holds (eqb BODY 1)` where BODY is `ite guard 1 0` up to the
    lowering's first-wins shape, to `Holds guard`.  Split the guard with
    evidence: true is the evidence itself, false makes BODY compute to 0."""
    one = L.numeral(1)
    at = lambda x: app('Holds', app('eqb', H.replace_subterm(opened, guard, x), one))
    motive = Lambda('_x', BOOL, arrow(app('Eq', BOOL, guard, Var('_x')),
                                      arrow(at(Var('_x')), app('Holds', guard))))
    when_true = Lambda('_e', app('Eq', BOOL, guard, Var('true')),
                       Lambda('_h', at(Var('true')), Var('_e')))
    when_false = Lambda('_e', app('Eq', BOOL, guard, Var('false')),
                        Lambda('_h', at(Var('false')),
                               app('absurd', app('Holds', guard), Var('_h'))))
    return app(app('Bool.ind', motive, when_true, when_false, guard),
               app('refl', BOOL, guard), hyp)


def _prove_push(env, facts):
    """sp_ok tid sp == 1  ->  sp_ok tid (sp_after_push ... sp n) == 1."""
    b, s, o = Var('bases'), Var('sizes'), Var('owners')
    tid, sp, n = Var('tid'), Var('sp'), Var('n')
    one = L.numeral(1)
    ok = lambda p: app('eqb', app('sp_ok', b, s, o, tid, p), one)
    pushed = app('sp_after_push', b, s, o, tid, sp, n)
    body = H.unfold(pushed, env, {'sp_after_push'})
    goal = app('Holds', ok(body))
    hyp_claim = app('Holds', ok(sp))
    pf = H.bound_by_ites_or_guards(env, goal, Var('h'), hyp_claim)
    stmt = Pi('bases', BYTES, Pi('sizes', BYTES, Pi('owners', BYTES, Pi(
        'tid', NAT, Pi('sp', NAT, Pi('n', NAT, arrow(
            hyp_claim, app('Holds', ok(pushed)))))))))
    term = Lambda('h', hyp_claim, pf)
    for name, ty in reversed([('bases', BYTES), ('sizes', BYTES),
                              ('owners', BYTES), ('tid', NAT), ('sp', NAT),
                              ('n', NAT)]):
        term = Lambda(name, ty, term)
    define(env, 'push_keeps_sp_ok', stmt, H.prove(stmt, term, env, verbose=False))
    facts['push_keeps_sp_ok'] = stmt


def _prove_no_cross(env, facts):
    """regions_disjoint == 1 -> sp_ok a sp == 1 -> sp_ok b sp == 1 -> a = b."""
    b_, s, o = Var('bases'), Var('sizes'), Var('owners')
    sp, ta, tb = Var('sp'), Var('a'), Var('b')
    one = L.numeral(1)
    succ = lambda t: App(Var('succ'), t)
    eqn = lambda x, y: app('Eq', NAT, x, y)
    ok = lambda t: app('eqb', app('sp_ok', b_, s, o, t, sp), one)
    of = lambda t: app('eqb', app('region_of', b_, s, o, app('add', t, one), sp),
                       one)

    def region_from_sp(t, h):
        opened = H.unfold(app('sp_ok', b_, s, o, t, sp), env, {'sp_ok'})
        return _guard_from_one(env, ok(t), of(t), opened, h)

    # succ is injective: transport `pred` along the equation
    def succ_inj(x, y, e):
        return app('Eq.ind', NAT, succ(x),
                   Lambda('c', NAT, Lambda('_t', eqn(succ(x), Var('c')),
                                            eqn(x, app('pred', Var('c'))))),
                   app('refl', NAT, x), succ(y), e)

    h_rd, ha, hb = Var('h_rd'), Var('ha'), Var('hb')
    same_owner = app('region_of_unique', b_, s, o, sp, app('add', ta, one),
                     app('add', tb, one), h_rd, region_from_sp(ta, ha),
                     region_from_sp(tb, hb))          # Eq (a+1) (b+1)
    body = succ_inj(ta, tb, same_owner)
    hyps = [('h_rd', app('Holds', app('eqb', app('regions_disjoint', b_, s), one))),
            ('ha', app('Holds', ok(ta))), ('hb', app('Holds', ok(tb)))]
    params = [('bases', BYTES), ('sizes', BYTES), ('owners', BYTES),
              ('sp', NAT), ('a', NAT), ('b', NAT)]
    stmt = eqn(ta, tb)
    for _, ty in reversed(hyps):
        stmt = arrow(ty, stmt)
    for name, ty in reversed(params):
        stmt = Pi(name, ty, stmt)
    term = body
    for name, ty in reversed(hyps):
        term = Lambda(name, ty, term)
    for name, ty in reversed(params):
        term = Lambda(name, ty, term)
    define(env, 'sp_no_cross', stmt, H.prove(stmt, term, env, verbose=False))
    facts['sp_no_cross'] = stmt


THEOREMS = ['push_keeps_sp_ok', 'sp_no_cross']


def lean_source(env):
    import leanexport as X
    slow = H.prelude(fast=False)
    values = {n: L.value_of(slow, n) for n in H.ACCELERATED}
    src, _ = X.export(env, THEOREMS + memmap_eq.THEOREMS, values,
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
        with open('Threads.lean', 'w') as fh:
            fh.write(src)
        print('wrote Threads.lean (%d lines)' % src.count('\n'))

    threading.stack_size(512 * 1024 * 1024)
    t = threading.Thread(target=main)
    t.start()
    t.join()
