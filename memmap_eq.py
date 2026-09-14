#!/usr/bin/env python3
r"""memmap_eq.py -- LeanOS's region list, modelled and proved.

`leanos/memmap.py` in the crust tree is the founding data structure of
LeanOS: every region the kernel will touch, as a list of (base, size, owner)
laid out at build time.  `regions_disjoint` is the checker the rest of the
kernel rests on, and `region_of` is the access rule -- a thread may touch an
address only if this says 1 for it.

This file is those four functions again, statement for statement, in the
dialect `read_procedure` compiles, with what is proved about them today:

  region_index_found         result == len(bases), or owners[result] == who
                             and bases[result] <= addr < bases[result] +
                             sizes[result]: the witness is one it vouches
                             for, which is what lets a proof use it.
  regions_disjoint_bounded   result <= 1
  region_of_bounded          result <= 1
  contains_bounded           result <= 1
  owned_by_bounded           result <= len(owners)

All four are loop theorems, and the first three are through loops that
`return` early -- the shape no theorem in this tree went through before
`early_return_bound`.  What they say is that each function is a decision:
nothing about *which* decision.  The theorem LeanOS is founded on,

  regions_disjoint == 1  ->  no two regions overlap

is quantified over pairs of positions, and the fragment's invariants are
Bools over the carried state.  It waits on one primitive -- `allb`, a
Bool-valued "for every element" over a list, with the lemma that ties it to
`nth` -- and is stated in the docstring rather than the environment until
that primitive exists.  Nothing here pretends otherwise.

The paraphrases between this and the rpython, each forced by the encoding:
`'Array'` for `list[i64]` and `list[int]` alike; `assert invariant(...)` and
`assert variant(...)` in each loop; a read past the end is 0 here and an
IndexError there, and the length checks keep either from happening.
"""
import inspect
import textwrap

import lean4 as L
import hoare as H
from lean4 import Var
from lean4 import App, Lambda, Pi
from hoare import app, procedure, define, rec, arrow, NAT, BOOL, BYTES

SOURCES = {}


def remember(func):
    SOURCES[func.__name__] = textwrap.dedent(inspect.getsource(func))
    return func


def invariant(*_):
    return True


def variant(*_):
    return True


def in_order_at(b, s, k):
    """The loop's guard at position k, negated, and vacuous at k == 0.

    Written with the same `ltb`, `nth`, `add` and `sub k 1` the lowering
    emits for `bases[i] < bases[i - 1] + sizes[i - 1]`, so that after the
    guard is split the specification computes rather than needing a lemma.
    """
    nth = lambda xs, j: app('nth', NAT, L.numeral(0), xs, j)
    km1 = app('sub', k, L.numeral(1))
    prev_end = app('add', nth(b, km1), nth(s, km1))
    return app('ite', BOOL, app('ltb', L.numeral(0), k),
               app('notb', app('ltb', nth(b, k), prev_end)), L.Var('true'))


def build(verbose=False):
    env = H.prelude()
    facts = {}
    model = {}
    b, s = L.Var('bases'), L.Var('sizes')

    # -- the specification: every position below i passed the guard ---------
    define(env, 'ordered_prefix', arrow(BYTES, arrow(BYTES, arrow(NAT, BOOL))),
           Lambda('bases', BYTES, Lambda('sizes', BYTES, Lambda('i', NAT,
               rec(NAT, BOOL, L.Var('true'),
                   Lambda('k', NAT, Lambda('ih', BOOL,
                          app('andb', in_order_at(b, s, L.Var('k')), L.Var('ih')))),
                   L.Var('i'))))))

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'],
               signatures={'ordered_prefix': ([BYTES, BYTES, NAT], BOOL)})
    def regions_disjoint(bases: 'Array', sizes: 'Array') -> 'Nat':
        if len(sizes) < len(bases):
            return 0
        i = 0
        while i < len(bases):
            assert invariant(i <= len(bases)
                             and _return_value <= 1
                             and (not (_return_value == 1))
                             and (_returned or ordered_prefix(bases, sizes, i)))
            assert variant(len(bases) - i)
            if i > 0:
                if bases[i] < bases[i - 1] + sizes[i - 1]:
                    return 0
            i = i + 1
        return 1

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'])
    def contains(bases: 'Array', sizes: 'Array', i: 'Nat',
                 addr: 'Nat') -> 'Nat':
        if i >= len(bases):
            return 0
        if len(sizes) < len(bases):
            return 0
        if bases[i] <= addr:
            if addr < bases[i] + sizes[i]:
                return 1
        return 0

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= len(owners)'])
    def owned_by(owners: 'Array', who: 'Nat') -> 'Nat':
        n = 0
        i = 0
        while i < len(owners):
            assert invariant(i <= len(owners) and n <= i)
            assert variant(len(owners) - i)
            if owners[i] == who:
                n = n + 1
            i = i + 1
        return n

    FOUND = ('result == len(bases) or (owners[result] == who and '
             'bases[result] <= addr and addr < bases[result] + sizes[result])')

    @remember
    @procedure(env=env, verbose=verbose, ensures=[FOUND])
    def region_index(bases: 'Array', sizes: 'Array', owners: 'Array',
                     who: 'Nat', addr: 'Nat') -> 'Nat':
        if len(sizes) < len(bases):
            return len(bases)
        if len(owners) < len(bases):
            return len(bases)
        i = 0
        while i < len(bases):
            assert invariant((not _returned)
                             or _return_value == len(bases)
                             or (owners[_return_value] == who
                                 and bases[_return_value] <= addr
                                 and addr < bases[_return_value]
                                 + sizes[_return_value]))
            assert variant(len(bases) - i)
            if owners[i] == who:
                if bases[i] <= addr:
                    if addr < bases[i] + sizes[i]:
                        return i
            i = i + 1
        return len(bases)

    @remember
    @procedure(env=env, verbose=verbose, ensures=['result <= 1'],
               signatures={'region_index':
                           ([BYTES, BYTES, BYTES, NAT, NAT], NAT)})
    def region_of(bases: 'Array', sizes: 'Array', owners: 'Array',
                  who: 'Nat', addr: 'Nat') -> 'Nat':
        if region_index(bases, sizes, owners, who, addr) < len(bases):
            return 1
        return 0

    for fn in (regions_disjoint, contains, owned_by, region_index,
               region_of):
        model[fn.__name__] = fn

    # -- the early-return loops, by the one recipe ---------------------------
    _prove_found(env, region_index.lean_procedure, facts)

    # -- the founding theorem: what regions_disjoint decides -----------------
    _prove_ordered(env, regions_disjoint.lean_procedure, facts)

    # -- from the decision to what it decides -------------------------------
    _prove_pairwise(env, facts)

    # region_of is a guard chain over region_index
    proc = region_of.lean_procedure
    L.define(env, 'region_of_bounded', proc.obligation,
             H.by_every_bool(env, proc.obligation, unfolding={'region_of'}))
    facts['region_of_bounded'] = proc.obligation

    _prove_unique(env, facts)
    _prove_owner_unique(env, facts)

    # -- the guard chain -----------------------------------------------------
    proc = contains.lean_procedure
    pf = H.by_every_bool(env, proc.obligation, unfolding={'contains'})
    L.define(env, 'contains_bounded', proc.obligation, pf)
    facts['contains_bounded'] = proc.obligation

    # -- the counting loop: the `accepted` shape, n <= i <= len --------------
    proc = owned_by.lean_procedure
    goals = dict(proc.loop_obligations)
    carried = proc.shapes[0]['carried']
    n_len = app('len', H.NAT, Var('owners'))
    entry = H.discharge(goals['invariant holds on entry'], env, verbose=False)

    def keeps_it(f, h, claim):
        conj = H.reduce_projections(H.unfold(
            L.spine(claim)[1][-1], env, {'owned_by.inv1', 'owned_by.pass1'}))
        after_A, after_B = L.spine(conj)[1]
        A = app('leb', f['i'], n_len)
        B = app('leb', f['n'], f['i'])
        so_far = app('andb_right', A, B, h[0])
        # after_B is  leb (ite (owners[i] == who) (n + 1) n) (i + 1):
        # either succ n <= succ i, which is B by definition of leb, or
        # n <= succ i, which is B and leb_succ through leb_trans.
        keep_B = H.by_bool(env, app('Holds', after_B), None, so_far,
                           app('leb_trans', f['n'], f['i'],
                               app(Var('succ'), f['i']), so_far,
                               app('leb_succ', f['i'])))
        return app('andb_both', after_A, after_B, h[1], keep_B)

    kept = H.by_cases(env, None, goals['invariant is preserved'],
                      what='preservation', names=carried, using=keeps_it)
    down = H.by_cases(env, None, goals['variant decreases'],
                      what='the variant', names=carried,
                      using=lambda f, h, g: app('sub_lt', n_len, f['i'], h[1]))
    H.progress_by_loop(env, proc, entry, kept, down, verbose=False)
    at_exit = H.invariant_at_exit(env, proc, entry, kept)
    final, state = proc.shapes[0]['result'], proc.shapes[0]['state']
    n_f = H._project(final, state, carried.index('n'))
    i_f = H._project(final, state, carried.index('i'))
    held = app(at_exit, Var('owners'), Var('who'))
    A_f, B_f = app('leb', i_f, n_len), app('leb', n_f, i_f)
    post = L.Lambda('owners', H.BYTES, L.Lambda('who', H.NAT, app(
        'leb_trans', n_f, i_f, n_len, app('andb_right', A_f, B_f, held),
        app('andb_left', A_f, B_f, held))))
    pf = H.prove(proc.obligation, post, env, verbose=False)
    L.define(env, 'owned_by_bounded', proc.obligation, pf)
    facts['owned_by_bounded'] = proc.obligation

    return env, facts, model


def _prove_ordered(env, p, facts):
    """regions_disjoint == 1  ->  ordered_prefix bases sizes (regions_checked bases sizes).

    Stated over `len bases`: the loop's final counter is `<=` it by the
    invariant and `>=` it by the exit condition through `ltb_false_leb`,
    and `leb_antisymm` makes them equal; `regions_checked_is_len` records
    the equation.  The proof carries four things through the loop: the
    counter's bound, that the accumulator is `<= 1` and never 1, and that
    either the loop has returned or every pair so far was in order.
    """
    b, s = L.Var('bases'), L.Var('sizes')
    n = app('len', NAT, b)
    Var = L.Var
    goals = dict(p.loop_obligations)
    entry = H.by_every_bool(env, goals['invariant holds on entry'], unfolding={'regions_disjoint.inv1'})
    def keeps_it(f, h, claim):
        raw = H.unfold(L.spine(claim)[1][-1], env, {'regions_disjoint.inv1','regions_disjoint.pass1'})
        conj = H.reduce_projections(raw)
        after_ADC, after_B = L.spine(conj)[1]        # ((A and D) and C) and B, as Python parses it
        after_AD, after_C = L.spine(after_ADC)[1]
        after_A, after_D = L.spine(after_AD)[1]
        A = app('leb', f['i'], n)
        D = app('leb', Var('_return_value'), L.numeral(1))
        C = app('notb', app('eqb', Var('_return_value'), L.numeral(1)))
        B = app('orb', Var('_returned'), app('ordered_prefix', b, s, f['i']))
        AD = app('andb', A, D)
        ADC = app('andb', AD, C)
        have_ADC = app('andb_left', ADC, B, h[0])
        have_B = app('andb_right', ADC, B, h[0])
        have_AD = app('andb_left', AD, C, have_ADC)
        have_C = app('andb_right', AD, C, have_ADC)
        have_D = app('andb_right', A, D, have_AD)
        keep_D = H.bound_by_ites(env, app('Holds', after_D), have_D, app('Holds', D))
        keep_C = H.bound_by_ites(env, app('Holds', after_C), have_C, app('Holds', C))
        folded = app('ordered_prefix', b, s, app('add', f['i'], L.numeral(1)))
        opened = app('andb', in_order_at(b, s, f['i']), app('ordered_prefix', b, s, f['i']))
        goal = H.replace_subterm(app('Holds', after_B), folded, opened)
        keep_B = H.bound_by_ites(env, goal, have_B, app('Holds', B))
        return app('andb_both', after_ADC, after_B,
                   app('andb_both', after_AD, after_C,
                       app('andb_both', after_A, after_D, h[1], keep_D), keep_C),
                   keep_B)
    kept = H.by_cases(env, None, goals['invariant is preserved'], what='preservation', names=p.shapes[0]['carried'], using=keeps_it)
    carried = p.shapes[0]['carried']
    down = H.by_cases(env, None, goals['variant decreases'], what='the variant', names=carried,
                      using=lambda f, h, g: app('sub_lt', n, f['i'], h[1]))
    done = H.progress_by_loop(env, p, entry, kept, down, verbose=False)
    at_exit = H.invariant_at_exit(env, p, entry, kept)
    final, state = p.shapes[0]['result'], p.shapes[0]['state']
    rv_f = H._project(final, state, carried.index('_return_value'))
    rt_f = H._project(final, state, carried.index('_returned'))
    i_f  = H._project(final, state, carried.index('i'))
    # name the final counter, so the theorem reads
    define(env, 'regions_checked', arrow(BYTES, arrow(BYTES, NAT)),
           Lambda('bases', BYTES, Lambda('sizes', BYTES, i_f)))
    checked = app('regions_checked', b, s)
    held = app(at_exit, b, s)
    x = app('ordered_prefix', b, s, i_f)
    A_f = app('leb', i_f, n)
    D_f = app('leb', rv_f, L.numeral(1))
    C_f = app('notb', app('eqb', rv_f, L.numeral(1)))
    B_f = app('orb', rt_f, x)
    AD_f = app('andb', A_f, D_f)
    ADC_f = app('andb', AD_f, C_f)
    have_ADC = app('andb_left', ADC_f, B_f, held)
    have_B = app('andb_right', ADC_f, B_f, held)
    have_AD = app('andb_left', AD_f, C_f, have_ADC)
    have_C = app('andb_right', AD_f, C_f, have_ADC)
    have_A = app('andb_left', A_f, D_f, have_AD)
    have_D = app('andb_right', A_f, D_f, have_AD)
    # result <= 1, from D at exit
    motive_d = Lambda('_x', BOOL, app('Holds', app('leb', app('ite', NAT, Var('_x'), rv_f, L.numeral(1)), L.numeral(1))))
    one_le_one = H.discharge(app('Holds', app('leb', L.numeral(1), L.numeral(1))), env, verbose=False)
    pfd = H.prove(p.obligation, Lambda('bases', BYTES, Lambda('sizes', BYTES,
                  app('Bool.ind', motive_d, have_D, one_le_one, rt_f))), env, verbose=False)
    define(env, 'regions_disjoint_bounded', p.obligation, pfd)
    facts['regions_disjoint_bounded'] = p.obligation
    # split rt_f on an implication, so the false branch may use have_B at rt_f = false
    goal_at = lambda t: app('Holds', app('orb', app('notb', app('eqb', app('ite', NAT, t, rv_f, L.numeral(1)), L.numeral(1))), x))
    motive = Lambda('_x', BOOL, arrow(app('Holds', app('orb', Var('_x'), x)), goal_at(Var('_x'))))
    when_true = Lambda('_h', app('Holds', app('orb', Var('true'), x)),
                       app('holds_orb_left', C_f, x, have_C))
    when_false = Lambda('_h', app('Holds', app('orb', Var('false'), x)), Var('_h'))
    body = app(app('Bool.ind', motive, when_true, when_false, rt_f), have_B)

    # the counter at exit is the length: <= from the invariant, >= from the
    # exit condition through totality, and antisymmetry makes them equal
    not_lt = app(done, b, s)                                 # Holds (notb (ltb i_f n))
    eq_len = app('leb_antisymm', i_f, n, have_A,
                 app('ltb_false_leb', i_f, n, not_lt))      # Eq i_f n
    stmt = Pi('bases', BYTES, Pi('sizes', BYTES, app('Holds', app('orb',
              app('notb', app('eqb', app('regions_disjoint', b, s), L.numeral(1))),
              app('ordered_prefix', b, s, n)))))
    result = app('ite', NAT, rt_f, rv_f, L.numeral(1))
    at_c = Lambda('c', NAT, Lambda('_t', app('Eq', NAT, i_f, Var('c')),
                  app('Holds', app('orb', app('notb', app('eqb', result, L.numeral(1))),
                                   app('ordered_prefix', b, s, Var('c'))))))
    body_len = app('Eq.ind', NAT, i_f, at_c, body, n, eq_len)
    post = Lambda('bases', BYTES, Lambda('sizes', BYTES, body_len))
    pf = H.prove(stmt, post, env, verbose=False)
    define(env, 'regions_disjoint_ordered', stmt, pf)
    facts['regions_disjoint_ordered'] = stmt
    is_len = Pi('bases', BYTES, Pi('sizes', BYTES, app('Eq', NAT, checked, n)))
    pfl = H.prove(is_len, Lambda('bases', BYTES, Lambda('sizes', BYTES, eq_len)), env, verbose=False)
    define(env, 'regions_checked_is_len', is_len, pfl)
    facts['regions_checked_is_len'] = is_len


def _prove_pairwise(env, facts):
    """From "the checker said 1" to "consecutive regions do not overlap".

    `regions_disjoint_ordered` gives `ordered_prefix` at `len bases`, which
    is a conjunction of guards.  These take it apart: `ordered_guard_at`
    recovers the guard at any position below the bound, by induction on the
    bound with `eqb_eq` transporting the top case; `ordered_step` turns one
    guard into `end(j) <= base(j+1)`, with `sub_zero` rewriting the `i - 1`
    the lowering emits.  Together they are the founding sentence of LeanOS
    for adjacent regions.
    """
    b, s = L.Var('bases'), L.Var('sizes')
    Var, holds = L.Var, lambda t: app('Holds', t)
    succ = lambda t: L.App(Var('succ'), t)
    Lambda, Pi, App = L.Lambda, L.Pi, L.App
    nth = lambda xs, i: app('nth', NAT, L.numeral(0), xs, i)
    end_at = lambda i: app('add', nth(b, i), nth(s, i))
    leb = lambda x, y: app('leb', x, y)
    ltb = lambda x, y: app('ltb', x, y)
    guard = lambda i: in_order_at(b, s, i)
    prefix = lambda t: app('ordered_prefix', b, s, t)
    wrap = lambda t: Lambda('bases', BYTES, Lambda('sizes', BYTES, t))
    j, k, m, n = Var('j'), Var('k'), Var('m'), Var('n')
    # 1. the guard at succ j says the previous region ends at or before this
    #    one begins.  `sub (succ j) 1` is `sub j 0`, so sub_zero rewrites it.
    mot = Lambda('c', NAT, Lambda(
        '_t', app('Eq', NAT, app('sub', j, L.numeral(0)), Var('c')),
        arrow(holds(guard(succ(j))),
              holds(app('notb', app('ltb', nth(b, succ(j)),
                                    app('add', nth(b, Var('c')),
                                        nth(s, Var('c')))))))))
    peel = app('Eq.ind', NAT, app('sub', j, L.numeral(0)), mot,
               Lambda('h', holds(guard(succ(j))), Var('h')),
               j, app('sub_zero', j))
    step_goal = Pi('bases', BYTES, Pi('sizes', BYTES, Pi('j', NAT, arrow(
        holds(guard(succ(j))), holds(app('leb', end_at(j), nth(b, succ(j))))))))
    step_pf = wrap(Lambda('j', NAT, Lambda('h', holds(guard(succ(j))),
                   app('ltb_false_leb', nth(b, succ(j)), end_at(j),
                       app(peel, Var('h'))))))
    define(env, 'ordered_step', step_goal,
           H.prove(step_goal, step_pf, env, verbose=False))

    # 2. a prefix at n gives the guard at every position below n.  Induction
    #    on n; at succ m, either k is m (transport the guard back along the
    #    equation) or k is below m (the inductive hypothesis).
    Mg = Lambda('n', NAT, Pi('k', NAT, arrow(
        holds(prefix(n)), arrow(holds(app('ltb', k, n)), holds(guard(k))))))
    base = Lambda('k', NAT, Lambda('hp', holds(prefix(L.numeral(0))), Lambda(
        'hk', holds(app('ltb', k, L.numeral(0))),
        app('absurd', holds(guard(k)), Var('hk')))))

    def step_body(hp, hk, ih):
        motive = Lambda('_x', BOOL, arrow(
            app('Eq', BOOL, app('eqb', k, m), Var('_x')), holds(guard(k))))
        when_eq = Lambda('he', app('Eq', BOOL, app('eqb', k, m), Var('true')),
                         app('Eq.ind', NAT, k,
                             Lambda('c', NAT, Lambda(
                                 '_t', app('Eq', NAT, k, Var('c')),
                                 arrow(holds(guard(Var('c'))), holds(guard(k))))),
                             Lambda('g', holds(guard(k)), Var('g')),
                             m, app('eqb_eq', k, m, Var('he')),
                             app('andb_left', guard(m), prefix(m), hp)))
        when_ne = Lambda('he', app('Eq', BOOL, app('eqb', k, m), Var('false')),
                         app(ih, k, app('andb_right', guard(m), prefix(m), hp),
                             app('lt_succ_ne', k, m, hk, Var('he'))))
        return app(app('Bool.ind', motive, when_eq, when_ne,
                       app('eqb', k, m)),
                   app('refl', BOOL, app('eqb', k, m)))

    step = Lambda('m', NAT, Lambda('ih', App(Mg, m), Lambda('k', NAT, Lambda(
        'hp', holds(prefix(succ(m))), Lambda(
            'hk', holds(app('ltb', k, succ(m))),
            step_body(Var('hp'), Var('hk'), Var('ih')))))))
    at_goal = Pi('bases', BYTES, Pi('sizes', BYTES, Pi('n', NAT, App(Mg, n))))
    at_pf = wrap(Lambda('n', NAT, app('Nat.ind', Mg, base, step, n)))
    define(env, 'ordered_guard_at', at_goal,
           H.prove(at_goal, at_pf, env, verbose=False))

    # 3. the two together: a prefix at n means consecutive regions in it do
    #    not overlap.  This is the sentence LEANOS.md is founded on, for
    #    adjacent pairs; the general pair follows by transitivity of leb.
    adj_goal = Pi('bases', BYTES, Pi('sizes', BYTES, Pi('n', NAT, Pi('j', NAT,
        arrow(holds(prefix(n)), arrow(holds(app('ltb', succ(j), n)),
              holds(app('leb', end_at(j), nth(b, succ(j))))))))))
    adj_pf = wrap(Lambda('n', NAT, Lambda('j', NAT, Lambda(
        'hp', holds(prefix(n)), Lambda(
            'hk', holds(app('ltb', succ(j), n)),
            app('ordered_step', b, s, j,
                app('ordered_guard_at', b, s, n, succ(j), Var('hp'),
                    Var('hk'))))))))
    define(env, 'regions_adjacent_disjoint', adj_goal,
           H.prove(adj_goal, adj_pf, env, verbose=False))

    # -- and the general pair, by induction on the upper index --------------
    # For every j < k < n, region j ends at or before region k begins.
    # Induction on k.  At succ m, either j is m -- adjacent, which is
    # `regions_adjacent_disjoint` -- or j < m, and then
    #   end j <= base m          the inductive hypothesis
    #   base m <= end m          le_add_right
    #   end m <= base (succ m)   adjacent again
    # chained twice by leb_trans.  The prefix hypothesis is carried down
    # unchanged: it is at n throughout, not peeled.
    Mp = Lambda('k', NAT, Pi('j', NAT, arrow(
        holds(prefix(n)), arrow(holds(ltb(j, k)), arrow(
            holds(ltb(k, n)), holds(leb(end_at(j), nth(b, k))))))))

    base_case = Lambda('j', NAT, Lambda('hp', holds(prefix(n)), Lambda(
        'hj', holds(ltb(j, L.numeral(0))), Lambda(
            'hk', holds(ltb(L.numeral(0), n)),
            app('absurd', holds(leb(end_at(j), nth(b, L.numeral(0)))),
                Var('hj'))))))

    def step_body(hp, hj, hk, ih):
        adjacent = lambda i, less: app('regions_adjacent_disjoint', b, s, n, i,
                                       hp, less)
        # j == m: one adjacent step, transported along the equation
        # j == m: the adjacent fact at m, with m rewritten to j.  The
        # motive fixes the right-hand side and varies only the left, so
        # transport is from `end m` to `end j` along the symmetric equation.
        when_eq = Lambda('he', app('Eq', BOOL, app('eqb', j, m), Var('true')),
                         app('Eq.ind', NAT, m,
                             Lambda('c', NAT, Lambda(
                                 '_t', app('Eq', NAT, m, Var('c')),
                                 holds(leb(end_at(Var('c')), nth(b, succ(m)))))),
                             adjacent(m, hk), j,
                             app('eq_symm', NAT, j, m,
                                 app('eqb_eq', j, m, Var('he')))))
        # j < m: chain the hypothesis through region m
        below = app('lt_succ_ne', j, m, hj, Var('he'))
        m_lt_n = app('leb_trans', succ(m), succ(succ(m)), n,
                     app('leb_succ', succ(m)), hk)
        to_m = app(ih, j, hp, below, m_lt_n)
        when_ne = Lambda('he', app('Eq', BOOL, app('eqb', j, m), Var('false')),
                         app('leb_trans', end_at(j), nth(b, m), nth(b, succ(m)),
                             to_m,
                             app('leb_trans', nth(b, m), end_at(m),
                                 nth(b, succ(m)),
                                 app('le_add_right', nth(b, m), nth(s, m)),
                                 adjacent(m, hk))))
        motive = Lambda('_x', BOOL, arrow(
            app('Eq', BOOL, app('eqb', j, m), Var('_x')),
            holds(leb(end_at(j), nth(b, succ(m))))))
        return app(app('Bool.ind', motive, when_eq, when_ne,
                       app('eqb', j, m)),
                   app('refl', BOOL, app('eqb', j, m)))

    step = Lambda('m', NAT, Lambda('ih', App(Mp, m), Lambda('j', NAT, Lambda(
        'hp', holds(prefix(n)), Lambda(
            'hj', holds(ltb(j, succ(m))), Lambda(
                'hk', holds(ltb(succ(m), n)),
                step_body(Var('hp'), Var('hj'), Var('hk'), Var('ih'))))))))

    goal = Pi('bases', BYTES, Pi('sizes', BYTES, Pi('n', NAT, Pi('k', NAT,
             App(Mp, k)))))
    pf = wrap(Lambda('n', NAT, Lambda('k', NAT,
              app('Nat.ind', Mp, base_case, step, k))))
    define(env, 'regions_pairwise_disjoint', goal,
           H.prove(goal, pf, env, verbose=False))
    facts['regions_pairwise_disjoint'] = H.type_check(
        env, Var('regions_pairwise_disjoint'))

    for name in ('ordered_step', 'ordered_guard_at',
                 'regions_adjacent_disjoint'):
        facts[name] = H.type_check(env, Var(name))



def _prove_unique(env, facts):
    """At most one region contains an address.

    The witness `region_index` returns makes this usable: with the regions
    proved pairwise disjoint, two positions that both hold `addr` would put
    `addr` strictly below its own value.  Stated over the guards `contains`
    tests rather than over its verdict, because those are what a caller has
    in hand once `region_index` has returned an index.
    """
    b, s = L.Var('bases'), L.Var('sizes')
    Var, Lambda, Pi, App = L.Var, L.Lambda, L.Pi, L.App
    holds = lambda t: app('Holds', t)
    succ = lambda t: App(Var('succ'), t)
    n, addr, j, k = Var('n'), Var('addr'), Var('j'), Var('k')
    nth = lambda xs, i: app('nth', NAT, L.numeral(0), xs, i)
    end_at = lambda i: app('add', nth(b, i), nth(s, i))
    leb = lambda x, y: app('leb', x, y)
    ltb = lambda x, y: app('ltb', x, y)
    eqb = lambda x, y: app('eqb', x, y)
    eqn = lambda x, y: app('Eq', NAT, x, y)
    prefix = app('ordered_prefix', b, s, n)
    inside = lambda i: app('andb', leb(nth(b, i), addr), ltb(addr, end_at(i)))
    # From two positions that both hold addr, and the lower one's region
    # ending at or before the higher one's begins, comes addr < addr.
    def clash(lo, hi, h_lo, h_hi, hp, h_lt, h_hi_n):
        lt_end = app('andb_right', leb(nth(b, lo), addr), ltb(addr, end_at(lo)),
                     h_lo)
        ge_base = app('andb_left', leb(nth(b, hi), addr), ltb(addr, end_at(hi)),
                      h_hi)
        no_overlap = app('regions_pairwise_disjoint', b, s, n, hi, lo,
                         hp, h_lt, h_hi_n)
        return app('ltb_irrefl', addr,
                   app('leb_trans', succ(addr), end_at(lo), addr, lt_end,
                       app('leb_trans', end_at(lo), nth(b, hi), addr,
                           no_overlap, ge_base)))

    def body(hp, hj, hk, ij, ik):
        # j == k: the equation is the goal
        when_eq = Lambda('he', app('Eq', BOOL, eqb(j, k), Var('true')),
                         app('eqb_eq', j, k, Var('he')))
        # j != k: ordered one way or the other, and either way a clash
        def when_ne_body(he):
            ordered = app('ne_ordered', j, k, he)
            motive = Lambda('_y', BOOL, arrow(
                app('Eq', BOOL, ltb(j, k), Var('_y')), eqn(j, k)))
            lower_j = Lambda('hl', app('Eq', BOOL, ltb(j, k), Var('true')),
                             app('absurd', eqn(j, k),
                                 clash(j, k, ij, ik, hp, Var('hl'), hk)))
            # ltb j k is false, and j != k, so ltb k j: read it off `ordered`
            other = Lambda('hl', app('Eq', BOOL, ltb(j, k), Var('false')),
                           app('absurd', eqn(j, k),
                               clash(k, j, ik, ij, hp,
                                     app('orb_false_left', ltb(j, k),
                                         ltb(k, j), ordered, Var('hl')),
                                     hj)))
            return app(app('Bool.ind', motive, lower_j, other, ltb(j, k)),
                       app('refl', BOOL, ltb(j, k)))
        when_ne = Lambda('he', app('Eq', BOOL, eqb(j, k), Var('false')),
                         when_ne_body(Var('he')))
        motive = Lambda('_x', BOOL, arrow(
            app('Eq', BOOL, eqb(j, k), Var('_x')), eqn(j, k)))
        return app(app('Bool.ind', motive, when_eq, when_ne, eqb(j, k)),
                   app('refl', BOOL, eqb(j, k)))

    def chain(*parts):
        out = parts[-1]
        for x in reversed(parts[:-1]):
            out = arrow(x, out)
        return out

    inner = chain(holds(prefix), holds(ltb(j, n)), holds(ltb(k, n)),
                  holds(inside(j)), holds(inside(k)), eqn(j, k))
    goal = inner
    for name, ty in reversed([('bases', BYTES), ('sizes', BYTES), ('n', NAT),
                              ('addr', NAT), ('j', NAT), ('k', NAT)]):
        goal = Pi(name, ty, goal)

    pf = body(Var('hp'), Var('hj'), Var('hk'), Var('ij'), Var('ik'))
    for name, ty in reversed([('hp', holds(prefix)),
                              ('hj', holds(ltb(j, n))),
                              ('hk', holds(ltb(k, n))),
                              ('ij', holds(inside(j))),
                              ('ik', holds(inside(k)))]):
        pf = Lambda(name, ty, pf)
    for name, ty in reversed([('bases', BYTES), ('sizes', BYTES), ('n', NAT),
                              ('addr', NAT), ('j', NAT), ('k', NAT)]):
        pf = Lambda(name, ty, pf)

    define(env, 'contains_unique', goal,
           H.prove(goal, pf, env, verbose=False))
    facts['contains_unique'] = goal



def _prove_found(env, p, facts):
    """`region_index` returns `len(bases)`, or an index it can vouch for.

    The postcondition is carried as the invariant, with the case that the
    loop has not returned yet in front: `(not _returned) or _return_value ==
    len(bases) or found(_return_value)`.  The pre-loop returns give the
    second disjunct and the loop's own return the third.  The leaf that
    returns `i` is the one that needs the guards themselves -- `found(i)`
    mentions them at an occurrence that only exists once the `ite` has
    reduced -- and `bound_by_ites_or_guards` supplies them; the other leaves
    reuse the hypothesis, transported along the same equations.
    """
    Var, Lambda = L.Var, L.Lambda
    goals = dict(p.loop_obligations)
    n = app('len', NAT, Var('bases'))
    carried = p.shapes[0]['carried']
    nth = lambda xs, v: app('nth', NAT, L.numeral(0), Var(xs), v)
    found = lambda v: app('andb', app('andb',
                          app('eqb', nth('owners', v), Var('who')),
                          app('leb', nth('bases', v), Var('addr'))),
                          app('ltb', Var('addr'),
                              app('add', nth('bases', v), nth('sizes', v))))
    rv, rt = Var('_return_value'), Var('_returned')
    inv_claim = app('orb', app('orb', app('notb', rt), app('eqb', rv, n)),
                    found(rv))

    entry = H.by_every_bool(env, goals['invariant holds on entry'],
                            unfolding={'region_index.inv1'})

    def keeps(f, h, claim):
        conj = H.reduce_projections(H.unfold(
            L.spine(claim)[1][-1], env,
            {'region_index.inv1', 'region_index.pass1'}))
        return H.bound_by_ites_or_guards(env, app('Holds', conj), h[0],
                                         app('Holds', inv_claim))

    kept = H.by_cases(env, None, goals['invariant is preserved'],
                      what='preservation', names=carried, using=keeps)
    down = H.by_cases(env, None, goals['variant decreases'],
                      what='the variant', names=carried,
                      using=lambda f, h, g: app('sub_lt', n, f['i'], h[1]))
    H.progress_by_loop(env, p, entry, kept, down, verbose=False)
    at_exit = H.invariant_at_exit(env, p, entry, kept)

    final, state = p.shapes[0]['result'], p.shapes[0]['state']
    rv_f = H._project(final, state, carried.index('_return_value'))
    rt_f = H._project(final, state, carried.index('_returned'))
    held = app(at_exit, *[Var(x) for x, _ in p.params])
    result = app('ite', NAT, rt_f, rv_f, n)
    post_of = lambda r: app('orb', app('eqb', r, n), found(r))
    inv_f = app('orb', app('orb', app('notb', rt_f), app('eqb', rv_f, n)),
                 found(rv_f))

    def when_true(ev):
        # returned: result is rv_f, and the invariant at exit, with rt_f
        # rewritten to true, computes to the postcondition at rv_f
        motive = Lambda('_c', BOOL, Lambda(
            '_t', app('Eq', BOOL, rt_f, Var('_c')),
            app('Holds', H.replace_subterm(inv_f, rt_f, Var('_c')))))
        return app('Eq.ind', BOOL, rt_f, motive, held, Var('true'), ev)

    def when_false(_ev):
        # ran off the end: result is len(bases), and eqb n n holds
        return app('holds_orb_left', app('eqb', n, n), found(n),
                   app('eqb_refl', n))

    body = H.by_bool_with_evidence(env, app('Holds', post_of(result)), rt_f,
                                   when_true, when_false, label='_exit')
    post = body
    for name, ty in reversed(p.params):
        post = Lambda(name, ty, post)
    pf = H.prove(p.obligation, post, env, verbose=False)
    L.define(env, 'region_index_found', p.obligation, pf)
    facts['region_index_found'] = p.obligation


def _prove_owner_unique(env, facts):
    """`region_of` says 1 for at most one owner: the founding rule, verbatim.

    Composes everything above.  `region_of w == 1` opens to its guard, so
    the index is below `len` (split with evidence; the other branch is
    `region_of == 0` against the hypothesis).  `lt_ne` then discards the
    first disjunct of `region_index_found`, leaving that the index is owned
    by `w` and holds `addr`.  Two such indices are the same by
    `contains_unique`, with the prefix supplied by `regions_disjoint_ordered`
    once `holds_notb_false` opens its antecedent.  Equal indices with equal
    owners are equal owners, by transport.
    """
    Var, Lambda, Pi = L.Var, L.Lambda, L.Pi
    holds = lambda t: app('Holds', t)
    b, s, o = Var('bases'), Var('sizes'), Var('owners')
    addr, w1, w2 = Var('addr'), Var('w1'), Var('w2')
    n = app('len', NAT, b)
    nth = lambda xs, v: app('nth', NAT, L.numeral(0), xs, v)
    eqn = lambda x, y: app('Eq', NAT, x, y)
    one = L.numeral(1)
    index = lambda w: app('region_index', b, s, o, w, addr)
    of = lambda w: app('region_of', b, s, o, w, addr)
    found = lambda w: app('andb', app('andb',
                          app('eqb', nth(o, index(w)), w),
                          app('leb', nth(b, index(w)), addr)),
                          app('ltb', addr, app('add', nth(b, index(w)),
                                               nth(s, index(w)))))
    # From `region_of w == 1`, the index is below len: region_of is
    # `ite (ltb r n) 1 0`, so split on that guard with evidence.  If the
    # guard is false, region_of is 0 and `eqb 0 1` is false against the
    # hypothesis; if true, the evidence is what we wanted.
    def below(w, h_of):
        r = index(w)
        guard = app('ltb', r, n)
        goal = holds(guard)
        # the actual body of region_of at these arguments, guard abstracted
        body_of = H.unfold(of(w), env, {'region_of'})
        at = lambda x: holds(app('eqb', H.replace_subterm(body_of, guard, x), one))
        motive = Lambda('_x', BOOL, arrow(
            app('Eq', BOOL, guard, Var('_x')), arrow(at(Var('_x')), goal)))
        when_true = Lambda('_e', app('Eq', BOOL, guard, Var('true')), Lambda(
            '_h', at(Var('true')), Var('_e')))
        when_false = Lambda('_e', app('Eq', BOOL, guard, Var('false')), Lambda(
            '_h', at(Var('false')), app('absurd', goal, Var('_h'))))
        return app(app('Bool.ind', motive, when_true, when_false, guard),
                   app('refl', BOOL, guard), h_of)

    # From below, the `found` disjunct of region_index_found.
    def found_of(w, h_of):
        r = index(w)
        disj = app('region_index_found', b, s, o, w, addr)   # orb (eqb r n) (found)
        return app('orb_false_left', app('eqb', r, n), found(w), disj,
                   app('lt_ne', r, n, below(w, h_of)))

    # From regions_disjoint == 1, the prefix at len.
    def prefix_of(h_rd):
        rd = app('regions_disjoint', b, s)
        disj = app('regions_disjoint_ordered', b, s)   # orb (notb (eqb rd 1)) (prefix n)
        return app('orb_false_left', app('notb', app('eqb', rd, one)),
                   app('ordered_prefix', b, s, n), disj,
                   app('holds_notb_false', app('eqb', rd, one), h_rd))

    def body(h_rd, h1, h2):
        f1, f2 = found_of(w1, h1), found_of(w2, h2)
        own1 = app('andb_left', app('eqb', nth(o, index(w1)), w1),
                   app('leb', nth(b, index(w1)), addr),
                   app('andb_left', app('andb', app('eqb', nth(o, index(w1)), w1),
                                        app('leb', nth(b, index(w1)), addr)),
                       app('ltb', addr, app('add', nth(b, index(w1)), nth(s, index(w1)))),
                       f1))
        own2 = app('andb_left', app('eqb', nth(o, index(w2)), w2),
                   app('leb', nth(b, index(w2)), addr),
                   app('andb_left', app('andb', app('eqb', nth(o, index(w2)), w2),
                                        app('leb', nth(b, index(w2)), addr)),
                       app('ltb', addr, app('add', nth(b, index(w2)), nth(s, index(w2)))),
                       f2))
        # inside(w) from found(w): re-associate
        def inside_of(w, f):
            ab = app('andb', app('eqb', nth(o, index(w)), w),
                     app('leb', nth(b, index(w)), addr))
            c = app('ltb', addr, app('add', nth(b, index(w)), nth(s, index(w))))
            return app('andb_both', app('leb', nth(b, index(w)), addr), c,
                       app('andb_right', app('eqb', nth(o, index(w)), w),
                           app('leb', nth(b, index(w)), addr),
                           app('andb_left', ab, c, f)),
                       app('andb_right', ab, c, f))
        same = app('contains_unique', b, s, n, addr, index(w1), index(w2),
                   prefix_of(h_rd), below(w1, h1), below(w2, h2),
                   inside_of(w1, f1), inside_of(w2, f2))       # Eq r1 r2
        # owners[r1] = w1 and owners[r2] = w2 with r1 = r2 gives w1 = w2
        e1 = app('eqb_eq', nth(o, index(w1)), w1, own1)       # Eq o[r1] w1
        e2 = app('eqb_eq', nth(o, index(w2)), w2, own2)       # Eq o[r2] w2
        # transport e2 to r1 along same^-1 : Eq o[r1] w2
        e2_at_r1 = app('Eq.ind', NAT, index(w2),
                       Lambda('c', NAT, Lambda('_t', eqn(index(w2), Var('c')),
                                                eqn(nth(o, Var('c')), w2))),
                       e2, index(w1),
                       app('eq_symm', NAT, index(w1), index(w2), same))
        # Eq w1 o[r1] then Eq o[r1] w2 : w1 = w2 by transport
        return app('Eq.ind', NAT, nth(o, index(w1)),
                   Lambda('c', NAT, Lambda('_t', eqn(nth(o, index(w1)), Var('c')),
                                            eqn(Var('c'), w2))),
                   e2_at_r1, w1, e1)

    hyps = [('h_rd', holds(app('eqb', app('regions_disjoint', b, s), one))),
            ('h1', holds(app('eqb', of(w1), one))),
            ('h2', holds(app('eqb', of(w2), one)))]
    params = [('bases', BYTES), ('sizes', BYTES), ('owners', BYTES),
              ('addr', NAT), ('w1', NAT), ('w2', NAT)]
    goal = eqn(w1, w2)
    for _, ty in reversed(hyps):
        goal = arrow(ty, goal)
    for name, ty in reversed(params):
        goal = Pi(name, ty, goal)
    pf = body(Var('h_rd'), Var('h1'), Var('h2'))
    for name, ty in reversed(hyps):
        pf = Lambda(name, ty, pf)
    for name, ty in reversed(params):
        pf = Lambda(name, ty, pf)
    define(env, 'region_of_unique', goal,
           H.prove(goal, pf, env, verbose=False))
    facts['region_of_unique'] = goal



THEOREMS = ['region_of_unique',
            'regions_disjoint_ordered', 'regions_pairwise_disjoint',
            'regions_adjacent_disjoint',
            'regions_checked_is_len', 'ordered_guard_at', 'ordered_step',
            'regions_disjoint_bounded', 'contains_bounded',
            'owned_by_bounded', 'region_of_bounded',
            'region_index_found', 'contains_unique']


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
        env, facts, _ = build(verbose=False)
        for name in THEOREMS:
            print('proved', name, ':', L.readable(facts[name]))
        src = lean_source(env)
        with open('MemMap.lean', 'w') as fh:
            fh.write(src)
        print('wrote MemMap.lean (%d lines)' % src.count('\n'))

    threading.stack_size(512 * 1024 * 1024)
    t = threading.Thread(target=main)
    t.start()
    t.join()
