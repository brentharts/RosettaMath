#!/usr/bin/env python3
r"""loader_eq.py -- LeanOS's loader, modelled and proved.

`leanos/loader.py` admits an ELF by two checks in order: `accept_image` on
its headers, and `regions_disjoint` on the region list with the loads
appended.  Both guards are written `== 1`, so each guard is the theorem
about it, and `by_every_bool` settles both:

  admit_accepts    admit == 1  ->  accept_image v m e cls == 1
  admit_disjoint   admit == 1  ->  regions_disjoint (extended b v) (extended s m) == 1

and the composition that is the point of the milestone,

  admit_ordered    admit == 1  ->  ordered_prefix (extended b v) (extended s m) (len ...)

which is `regions_disjoint_ordered` on the grown list: every theorem about
the region list -- pairwise disjointness, `contains_unique`,
`region_of_unique` -- now holds of the list with the guest in it.  The ELF
theorem and the memory theorem are one because `admit` made them one check.

`extended` and `claimed` are modelled and evaluated; their length theorems
are the `owned_by` shape and are left for a caller that needs them.
"""
import inspect
import textwrap

import lean4 as L
import hoare as H
import memmap_eq
import elfcheck_eq
from lean4 import Var, Lambda, Pi
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
    elfcheck_eq.build(verbose=verbose, env=env, facts=facts, model=model)
    sigs = {'accept_image': ([BYTES, BYTES, NAT, NAT], NAT),
            'regions_disjoint': ([BYTES, BYTES], NAT),
            'extended': ([BYTES, BYTES], BYTES)}

    @remember
    @procedure(env=env, verbose=verbose, ensures=['len(result) <= len(xs) + len(ys)'])
    def extended(xs: 'Array', ys: 'Array') -> 'Array':
        out: 'Array' = []
        i = 0
        while i < len(xs):
            assert invariant(i <= len(xs) and len(out) <= i)
            assert variant(len(xs) - i)
            out.append(xs[i])
            i = i + 1
        j = 0
        while j < len(ys):
            assert invariant(j <= len(ys) and len(out) <= len(xs) + j)
            assert variant(len(ys) - j)
            out.append(ys[j])
            j = j + 1
        return out

    @remember
    @procedure(env=env, verbose=verbose, ensures=['len(result) <= len(owners) + count'])
    def claimed(owners: 'Array', guest: 'Nat', count: 'Nat') -> 'Array':
        out: 'Array' = []
        i = 0
        while i < len(owners):
            assert invariant(i <= len(owners) and len(out) <= i)
            assert variant(len(owners) - i)
            out.append(owners[i])
            i = i + 1
        j = 0
        while j < count:
            assert invariant(j <= count and len(out) <= len(owners) + j)
            assert variant(count - j)
            out.append(guest)
            j = j + 1
        return out

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'], signatures=sigs)
    def admit(bases: 'Array', sizes: 'Array', vaddrs: 'Array', memszs: 'Array',
              entry: 'Nat', cls: 'Nat') -> 'Nat':
        if accept_image(vaddrs, memszs, entry, cls) == 1:
            if regions_disjoint(extended(bases, vaddrs), extended(sizes, memszs)) == 1:
                return 1
        return 0

    for fn in (extended, claimed, admit):
        model[fn.__name__] = fn

    b, s, v, m = Var('bases'), Var('sizes'), Var('vaddrs'), Var('memszs')
    e, cls = Var('entry'), Var('cls')
    one = L.numeral(1)
    params = [('bases', BYTES), ('sizes', BYTES), ('vaddrs', BYTES),
              ('memszs', BYTES), ('entry', NAT), ('cls', NAT)]
    adm = app('admit', b, s, v, m, e, cls)
    grown_b, grown_s = app('extended', b, v), app('extended', s, m)
    implies = lambda concl: app('orb', app('notb', app('eqb', adm, one)), concl)

    def closed(body):
        for name, ty in reversed(params):
            body = Pi(name, ty, body)
        return body

    accepts = closed(app('Holds', implies(app('eqb', app('accept_image', v, m, e, cls), one))))
    define(env, 'admit_accepts', accepts,
           H.by_every_bool(env, accepts, unfolding={'admit'}))
    facts['admit_accepts'] = accepts

    disjoint = closed(app('Holds', implies(app('eqb', app('regions_disjoint', grown_b, grown_s), one))))
    define(env, 'admit_disjoint', disjoint,
           H.by_every_bool(env, disjoint, unfolding={'admit'}))
    facts['admit_disjoint'] = disjoint

    # the composition: admit == 1 -> ordered_prefix on the grown list
    ordered = closed(arrow(app('Holds', app('eqb', adm, one)),
                     app('Holds', app('ordered_prefix', grown_b, grown_s,
                                      app('len', NAT, grown_b)))))
    rd = app('regions_disjoint', grown_b, grown_s)
    body = app('orb_false_left', app('notb', app('eqb', rd, one)),
               app('ordered_prefix', grown_b, grown_s, app('len', NAT, grown_b)),
               app('regions_disjoint_ordered', grown_b, grown_s),
               app('holds_notb_false', app('eqb', rd, one),
                   app('orb_false_left', app('notb', app('eqb', adm, one)),
                       app('eqb', rd, one),
                       app('admit_disjoint', b, s, v, m, e, cls),
                       app('holds_notb_false', app('eqb', adm, one), Var('h')))))
    term = Lambda('h', app('Holds', app('eqb', adm, one)), body)
    for name, ty in reversed(params):
        term = Lambda(name, ty, term)
    define(env, 'admit_ordered', ordered, H.prove(ordered, term, env, verbose=False))
    facts['admit_ordered'] = ordered
    return env, facts, model


THEOREMS = ['admit_accepts', 'admit_disjoint', 'admit_ordered']


def lean_source(env):
    import leanexport as X
    slow = H.prelude(fast=False)
    values = {n: L.value_of(slow, n) for n in H.ACCELERATED}
    src, _ = X.export(env, THEOREMS, values, ['#print axioms ' + t for t in THEOREMS])
    return src


if __name__ == '__main__':
    import sys
    import threading

    def main():
        sys.setrecursionlimit(300000)
        env, facts, _ = build()
        for name in THEOREMS:
            print('proved', name, ':', L.readable(facts[name])[:150])
        src = lean_source(env)
        with open('Loader.lean', 'w') as fh:
            fh.write(src)
        print('wrote Loader.lean (%d lines)' % src.count('\n'))

    threading.stack_size(512 * 1024 * 1024)
    t = threading.Thread(target=main)
    t.start()
    t.join()
