#!/usr/bin/env python3
r"""hoare.py -- an imperative fragment for the lean4.py micro-kernel.

`PythonToLean` accepts a single `return`: enough for a proof term, and not
enough for a program.  Contracts of the kind `extensions.py` already lifts out
of C source

    int calc_sum(int *ptr, unsigned int len)
    assert len(ptr) >= 64
    assert not len(ptr) % 4
    { ... }

are statements about a *body* -- assignments, branches, loops -- so checking
one in the kernel needs a way to read that body as a term.

The approach here is a Hoare triple {P} c {Q} discharged by **symbolic
execution**: the body is not given a semantics as an object in the kernel
(no state type, no Var, no big-step relation), it is *evaluated* into a pure
kernel term.  An assignment is a substitution, a branch is `ite`, and a
bounded loop is `Nat.rec`.  What comes out is an ordinary term of the calculus
of constructions, so everything downstream -- the elaborator, `type_check`,
`@theorem` -- is unchanged.

    {P} c {Q}    becomes    forall params, Holds P -> Holds Q[result := [[c]]]

which is a Pi type, and proving it is proving the contract.

Decidability, and why that is the right call here
-------------------------------------------------
A contract is a `Bool`-valued expression and the proposition is that it
computes to `true`:

    Holds b := Eq Bool b true

The tempting alternative, `le` as an inductive family, is refused by
`inductive()` -- a recursive argument in an indexed family would need the
induction hypothesis to name that occurrence's indices -- and the restriction
is deliberate, so it is not one to route around.

Encoding the other way costs nothing that matters and buys something real.
Every contract `extensions.py` parses (`len>=`, `len<=`, `div-by`) is already
decidable, because a contract that could not be *checked* would be no use to a
compiler.  So the proposition is about the same expression the runtime check
would evaluate, and the proof is what licenses deleting that check.  Closed
instances then need no proof at all: they compute, and `refl` is the proof.

The loop rule, and the one honest refusal
-----------------------------------------
`for i in range(n)` is a fold, and folds are what `Nat.rec` is:

    for i in range(n):        Nat.rec (lam _. T)
        v = v + f(i)   ==>            v0
                              (lam i ih. add ih (f i))
                              n

Several loop-carried variables are packed into a `Prod` and projected back out
on the way in, so the accumulator stays one term.

`while` is **refused**, with the reason in the diagnostic.  A while loop
terminates only for a reason the programmer knows and the text does not state,
so lowering one means either inventing a variant or assuming a fuel bound --
guessing, in a place where a guess is an unproved theorem.  `for` over a range
carries its own bound, which is why it is the fragment that is supported.
"""

import ast
import inspect
import sys
import textwrap
import lean4 as L
from lean4 import (App, Binder, Bound, Expr, KernelError, Lambda, Pi, REC,
                   TheoremError, Universe, Var, arrow, define, inductive,
                   numeral, normalize, readable, type_check)


class ContractError(KernelError):
    """A body, or a contract on one, that this fragment cannot read."""


# --------------------------------------------------------------- shorthands

NAT = Var('Nat')
BOOL = Var('Bool')
TYPE0 = Universe(1)
PROP = Universe(0)


def app(head, *args):
    """head a1 .. an, curried.  A string head means a global name."""
    out = Var(head) if isinstance(head, str) else head
    for a in args:
        out = App(out, a)
    return out


def rec(motive_type_, motive_body, *rest):
    """Nat.rec with the motive written as a body over one bound name."""
    return app('Nat.rec', Lambda('_', motive_type_, motive_body), *rest)



# ------------------------------------------------------------------ records

RECORDS = {}          # record name -> [(field name, field type)]
SINGLE_CTOR = {}      # inductive name -> its one constructor


def fields_of(env, type_term):
    r"""The constructor of a one-constructor type, and its field types here.

    Works through parameters, so `Prod Nat (List Nat)` reports fields `Nat`
    and `List Nat`.  That matters because a loop carrying two variables is
    carrying a `Prod`, and a `Prod` is as much a one-constructor type as a
    record is -- the case split that unsticks a record's projections unsticks
    `fst` and `snd` for exactly the same reason.
    """
    head, params = L.spine(normalize(type_term, env))
    if not isinstance(head, Var) or head.name not in SINGLE_CTOR:
        return None
    constructor = SINGLE_CTOR[head.name]
    signature = L.type_of(env, constructor)
    for value in params:
        signature = L.instantiate(signature.body, value)
    fields = []
    while isinstance(signature, Pi):
        fields.append(signature.var_type)
        signature = L.instantiate(signature.body, Var('_field'))
    return head.name, constructor, params, fields


def record(env, name, fields):
    r"""Declare a record: one constructor, named projections, named updaters.

    `inductive()` already builds everything a record needs -- a family with a
    single constructor is a product, and its recursor is the eliminator that
    takes the fields apart.  What it does not give is names, and a kernel
    context has ten of them.  Threading `Prod`s through a syscall means
    reading `fst (snd (snd (snd c)))` and counting, which is not a thing
    anyone should have to check by eye.

    For each field this generates

        Name.field       : Name -> FieldType
        Name.with_field  : Name -> FieldType -> Name

    both by iota on the one constructor, so both compute.  A functional
    update is what makes state threadable: a syscall takes a context and
    returns one, and nothing is mutated anywhere.
    """
    constructor = f'{name}.mk'
    inductive(env, name, [(constructor, [ty for _, ty in fields])])
    count = len(fields)
    slots = [f'f{i}' for i in range(count)]

    for i, (field, ftype) in enumerate(fields):
        case = Var(slots[i])
        for j in reversed(range(count)):
            case = Lambda(slots[j], fields[j][1], case)
        define(env, f'{name}.{field}', arrow(Var(name), ftype),
               Lambda('r', Var(name),
                      app(f'{name}.rec', Lambda('_', Var(name), ftype),
                          case, Var('r'))))

        rebuilt = Var(constructor)
        for j in range(count):
            rebuilt = App(rebuilt,
                          Var('v') if j == i else Var(slots[j]))
        for j in reversed(range(count)):
            rebuilt = Lambda(slots[j], fields[j][1], rebuilt)
        define(env, f'{name}.with_{field}',
               arrow(Var(name), arrow(ftype, Var(name))),
               Lambda('r', Var(name), Lambda('v', ftype,
                      app(f'{name}.rec', Lambda('_', Var(name), Var(name)),
                          rebuilt, Var('r')))))

    RECORDS[name] = list(fields)
    SINGLE_CTOR[name] = constructor
    TYPE_NAMES[name] = Var(name)
    SIGNATURES[constructor] = ([ty for _, ty in fields], Var(name))
    SIGNATURES[name] = ([ty for _, ty in fields], Var(name))
    return Var(name)


# ----------------------------------------------------------------- prelude

def replace_subterm(expr, target, replacement):
    r"""Every occurrence of `target` in `expr`, replaced.

    Used to recover the part of a body that runs *after* a loop, as a function
    of the loop's result: the body already has the loop's term substituted
    into it, and this takes it back out.  Safe here because the target is
    always an applied loop name -- a term with no bound variables of its own --
    so an occurrence under a binder is the same term as one outside it and
    needs no renumbering.
    """
    if expr.key() == target.key():
        return replacement
    if isinstance(expr, App):
        return App(replace_subterm(expr.func, target, replacement),
                   replace_subterm(expr.arg, target, replacement))
    if isinstance(expr, Binder):
        return expr.rebuild(
            replace_subterm(expr.var_type, target, replacement),
            replace_subterm(expr.body, target, replacement))
    return expr


def _abstract_over(term, bindings):
    for name, ty in bindings:
        term = Lambda(name, ty, term)
    return term


def prelude(env=None):
    r"""Everything the imperative fragment needs, defined rather than assumed.

    Nothing here is an axiom.  `Bool` and `Nat` come from the kernel's own
    environment; the operations are built from their recursors, so each one
    computes, and a closed contract is settled by `normalize` alone.
    """
    env = dict(L.GLOBAL_ENV) if env is None else env

    # -- the conditional: Bool.rec at a motive that ignores its argument ----
    define(env, 'ite',
           Pi('A', TYPE0,
              arrow(BOOL, arrow(Var('A'), arrow(Var('A'), Var('A')))),
              implicit=True),
           Lambda('A', TYPE0, Lambda('b', BOOL,
                  Lambda('t', Var('A'), Lambda('e', Var('A'),
                         app('Bool.rec', Lambda('_', BOOL, Var('A')),
                             Var('t'), Var('e'), Var('b')))))))

    # -- Bool algebra -------------------------------------------------------
    define(env, 'notb', arrow(BOOL, BOOL),
           Lambda('b', BOOL, app('Bool.rec', Lambda('_', BOOL, BOOL),
                                 Var('false'), Var('true'), Var('b'))))
    define(env, 'andb', arrow(BOOL, arrow(BOOL, BOOL)),
           Lambda('a', BOOL, Lambda('b', BOOL,
                  app('Bool.rec', Lambda('_', BOOL, BOOL),
                      Var('b'), Var('false'), Var('a')))))
    define(env, 'orb', arrow(BOOL, arrow(BOOL, BOOL)),
           Lambda('a', BOOL, Lambda('b', BOOL,
                  app('Bool.rec', Lambda('_', BOOL, BOOL),
                      Var('true'), Var('b'), Var('a')))))

    # -- arithmetic ---------------------------------------------------------
    define(env, 'pred', arrow(NAT, NAT),
           rec(NAT, NAT, numeral(0),
               Lambda('k', NAT, Lambda('ih', NAT, Var('k')))))
    # sub recurses on the *first* argument, so that `sub (m+1) (n+1)` is
    # `sub m n` by definition.  Iterating `pred` on the second argument
    # computes the same numbers and gives no such equation, which leaves any
    # proof about a `n - i` variant with nothing to induct on.
    define(env, 'sub', arrow(NAT, arrow(NAT, NAT)),
           rec(NAT, arrow(NAT, NAT),
               Lambda('n', NAT, numeral(0)),
               Lambda('m2', NAT, Lambda('ih', arrow(NAT, NAT),
                      Lambda('n', NAT,
                             rec(NAT, NAT, App(Var('succ'), Var('m2')),
                                 Lambda('n2', NAT, Lambda('_', NAT,
                                        App(Var('ih'), Var('n2')))),
                                 Var('n')))))))
    define(env, 'mul', arrow(NAT, arrow(NAT, NAT)),
           Lambda('m', NAT, Lambda('n', NAT,
                  rec(NAT, NAT, numeral(0),
                      Lambda('k', NAT, Lambda('ih', NAT,
                             app('add', Var('ih'), Var('m')))),
                      Var('n')))))

    # -- comparison: recursion on the left, then on the right ---------------
    define(env, 'leb', arrow(NAT, arrow(NAT, BOOL)),
           rec(NAT, arrow(NAT, BOOL),
               Lambda('n', NAT, Var('true')),
               Lambda('m2', NAT, Lambda('ihm', arrow(NAT, BOOL),
                      Lambda('n', NAT,
                             rec(NAT, BOOL, Var('false'),
                                 Lambda('n2', NAT, Lambda('_', BOOL,
                                        App(Var('ihm'), Var('n2')))),
                                 Var('n')))))))
    define(env, 'ltb', arrow(NAT, arrow(NAT, BOOL)),
           Lambda('m', NAT, Lambda('n', NAT,
                  app('leb', App(Var('succ'), Var('m')), Var('n')))))
    define(env, 'eqb', arrow(NAT, arrow(NAT, BOOL)),
           Lambda('m', NAT, Lambda('n', NAT,
                  app('andb', app('leb', Var('m'), Var('n')),
                      app('leb', Var('n'), Var('m'))))))

    # -- modulus, without division ------------------------------------------
    # mod 0 k = 0;  mod (n+1) k = if mod n k + 1 = k then 0 else mod n k + 1.
    # A counter that resets on reaching k, so no well-founded recursion is
    # needed -- which matters, because the kernel has none to offer.
    define(env, 'modb', arrow(NAT, arrow(NAT, NAT)),
           Lambda('n', NAT, Lambda('k', NAT,
                  rec(NAT, NAT, numeral(0),
                      Lambda('_p', NAT, Lambda('ih', NAT,
                             app('ite', NAT,
                                 app('eqb', App(Var('succ'), Var('ih')),
                                     Var('k')),
                                 numeral(0),
                                 App(Var('succ'), Var('ih'))))),
                      Var('n')))))
    define(env, 'dvdb', arrow(NAT, arrow(NAT, BOOL)),
           Lambda('k', NAT, Lambda('n', NAT,
                  app('eqb', app('modb', Var('n'), Var('k')), numeral(0)))))

    # -- pairs, for a loop that carries more than one variable --------------
    inductive(env, 'Prod', [('mk', [Var('A'), Var('B')])],
              params=[('A', TYPE0), ('B', TYPE0)])
    SINGLE_CTOR['Prod'] = 'mk'
    define(env, 'fst',
           Pi('A', TYPE0, Pi('B', TYPE0,
              arrow(app('Prod', Var('A'), Var('B')), Var('A')),
              implicit=True), implicit=True),
           Lambda('A', TYPE0, Lambda('B', TYPE0,
                  Lambda('p', app('Prod', Var('A'), Var('B')),
                         app('Prod.rec', Var('A'), Var('B'),
                             Lambda('_', app('Prod', Var('A'), Var('B')),
                                    Var('A')),
                             Lambda('a', Var('A'), Lambda('b', Var('B'),
                                    Var('a'))),
                             Var('p'))))))
    define(env, 'snd',
           Pi('A', TYPE0, Pi('B', TYPE0,
              arrow(app('Prod', Var('A'), Var('B')), Var('B')),
              implicit=True), implicit=True),
           Lambda('A', TYPE0, Lambda('B', TYPE0,
                  Lambda('p', app('Prod', Var('A'), Var('B')),
                         app('Prod.rec', Var('A'), Var('B'),
                             Lambda('_', app('Prod', Var('A'), Var('B')),
                                    Var('B')),
                             Lambda('a', Var('A'), Lambda('b', Var('B'),
                                    Var('b'))),
                             Var('p'))))))

    # -- lists, polymorphic in the element type -----------------------------
    # It was `List Nat` and nothing else, which is fine until a string turns
    # up.  A byte string is a list of Nat, and splitting one on a separator is
    # a list of those -- `List (List Nat)` -- so the element type has to be a
    # parameter.  `inductive()` already took params; the prelude just never
    # asked for one.
    inductive(env, 'List', [('nil', []), ('cons', [Var('A'), REC])],
              params=[('A', TYPE0)])
    listof = lambda ty: app('List', ty)

    define(env, 'len', Pi('A', TYPE0, arrow(listof(Var('A')), NAT),
                          implicit=True),
           Lambda('A', TYPE0,
                  app('List.rec', Var('A'),
                      Lambda('_', listof(Var('A')), NAT), numeral(0),
                      Lambda('h', Var('A'), Lambda('t', listof(Var('A')),
                             Lambda('ih', NAT, App(Var('succ'), Var('ih'))))))))

    # out of range reads the default, so `nth` is total -- the bound is what
    # the contract is *for*, not something the definition may assume.
    A = Var('A')
    deep = rec(NAT, A, Var('h'),
               Lambda('i2', NAT, Lambda('_', A, App(Var('ih'), Var('i2')))),
               Var('i'))
    step = Lambda('h', A, Lambda('t', listof(A),
                  Lambda('ih', arrow(NAT, A), Lambda('i', NAT, deep))))
    define(env, 'nth',
           Pi('A', TYPE0,
              arrow(A, arrow(listof(A), arrow(NAT, A))), implicit=True),
           Lambda('A', TYPE0, Lambda('d', A,
                  app('List.rec', A,
                      Lambda('_', listof(A), arrow(NAT, A)),
                      Lambda('i', NAT, Var('d')), step))))

    define(env, 'head',
           Pi('A', TYPE0, arrow(Var('A'), arrow(listof(Var('A')), Var('A'))),
              implicit=True),
           Lambda('A', TYPE0, Lambda('d', Var('A'),
                  app('List.rec', Var('A'),
                      Lambda('_', listof(Var('A')), Var('A')), Var('d'),
                      Lambda('h', Var('A'), Lambda('t', listof(Var('A')),
                             Lambda('_', Var('A'), Var('h'))))))))
    define(env, 'tail',
           Pi('A', TYPE0, arrow(listof(Var('A')), listof(Var('A'))),
              implicit=True),
           Lambda('A', TYPE0,
                  app('List.rec', Var('A'),
                      Lambda('_', listof(Var('A')), listof(Var('A'))),
                      app('nil', Var('A')),
                      Lambda('h', Var('A'), Lambda('t', listof(Var('A')),
                             Lambda('_', listof(Var('A')), Var('t')))))))

    define(env, 'append',
           Pi('A', TYPE0,
              arrow(listof(A), arrow(listof(A), listof(A))), implicit=True),
           Lambda('A', TYPE0,
                  app('List.rec', A,
                      Lambda('_', listof(A), arrow(listof(A), listof(A))),
                      Lambda('ys', listof(A), Var('ys')),
                      Lambda('h', A, Lambda('t', listof(A),
                             Lambda('ih', arrow(listof(A), listof(A)),
                                    Lambda('ys', listof(A),
                                           app('cons', A, Var('h'),
                                               App(Var('ih'), Var('ys')))))))))) 
    # snoc: the one a loop that builds a list in order actually needs.  A fold
    # over range(n) naturally produces its result backwards, and a reversed
    # answer is a wrong answer, not a presentational detail.
    define(env, 'snoc',
           Pi('A', TYPE0, arrow(listof(A), arrow(A, listof(A))),
              implicit=True),
           Lambda('A', TYPE0, Lambda('xs', listof(A), Lambda('x', A,
                  app('append', A, Var('xs'),
                      app('cons', A, Var('x'), app('nil', A)))))))
    define(env, 'rev', Pi('A', TYPE0, arrow(listof(A), listof(A)),
                          implicit=True),
           Lambda('A', TYPE0,
                  app('List.rec', A, Lambda('_', listof(A), listof(A)),
                      app('nil', A),
                      Lambda('h', A, Lambda('t', listof(A),
                             Lambda('ih', listof(A),
                                    app('snoc', A, Var('ih'), Var('h'))))))))

    # -- byte strings: List Nat, which is what a string is ------------------
    bytes_ = listof(NAT)
    strs = listof(bytes_)

    # find: the index of the first occurrence, or the length if there is none
    # -- which is exactly what `str.find` returning -1 means, without needing
    # a negative number Nat does not have.
    define(env, 'find', arrow(bytes_, arrow(NAT, NAT)),
           Lambda('xs', bytes_, Lambda('sep', NAT,
                  app('List.rec', NAT, Lambda('_', bytes_, NAT), numeral(0),
                      Lambda('h', NAT, Lambda('t', bytes_, Lambda('ih', NAT,
                             app('ite', NAT, app('eqb', Var('h'), Var('sep')),
                                 numeral(0), App(Var('succ'), Var('ih')))))),
                      Var('xs')))))
    define(env, 'take', arrow(bytes_, arrow(NAT, bytes_)),
           app('List.rec', NAT, Lambda('_', bytes_, arrow(NAT, bytes_)),
               Lambda('n', NAT, app('nil', NAT)),
               Lambda('h', NAT, Lambda('t', bytes_,
                      Lambda('ih', arrow(NAT, bytes_), Lambda('n', NAT,
                             rec(NAT, bytes_, app('nil', NAT),
                                 Lambda('n2', NAT, Lambda('_', bytes_,
                                        app('cons', NAT, Var('h'),
                                            App(Var('ih'), Var('n2'))))),
                                 Var('n'))))))))
    define(env, 'drop', arrow(bytes_, arrow(NAT, bytes_)),
           app('List.rec', NAT, Lambda('_', bytes_, arrow(NAT, bytes_)),
               Lambda('n', NAT, app('nil', NAT)),
               Lambda('h', NAT, Lambda('t', bytes_,
                      Lambda('ih', arrow(NAT, bytes_), Lambda('n', NAT,
                             rec(NAT, bytes_,
                                 app('cons', NAT, Var('h'), Var('t')),
                                 Lambda('n2', NAT, Lambda('_', bytes_,
                                        App(Var('ih'), Var('n2')))),
                                 Var('n'))))))))
    define(env, 'eqs', arrow(bytes_, arrow(bytes_, BOOL)),
           app('List.rec', NAT, Lambda('_', bytes_, arrow(bytes_, BOOL)),
               Lambda('ys', bytes_,
                      app('List.rec', NAT, Lambda('_', bytes_, BOOL),
                          Var('true'),
                          Lambda('h2', NAT, Lambda('t2', bytes_,
                                 Lambda('_', BOOL, Var('false')))),
                          Var('ys'))),
               Lambda('h', NAT, Lambda('t', bytes_,
                      Lambda('ih', arrow(bytes_, BOOL), Lambda('ys', bytes_,
                             app('List.rec', NAT, Lambda('_', bytes_, BOOL),
                                 Var('false'),
                                 Lambda('h2', NAT, Lambda('t2', bytes_,
                                        Lambda('_', BOOL,
                                               app('andb',
                                                   app('eqb', Var('h'),
                                                       Var('h2')),
                                                   App(Var('ih'),
                                                       Var('t2')))))),
                                 Var('ys'))))))))
    # split: a right fold that starts with one empty segment and either opens
    # a new one at a separator or pushes onto the one already open.
    define(env, 'split', arrow(bytes_, arrow(NAT, strs)),
           Lambda('xs', bytes_, Lambda('sep', NAT,
                  app('List.rec', NAT, Lambda('_', bytes_, strs),
                      app('cons', bytes_, app('nil', NAT), app('nil', bytes_)),
                      Lambda('h', NAT, Lambda('t', bytes_,
                             Lambda('ih', strs,
                                    app('ite', strs,
                                        app('eqb', Var('h'), Var('sep')),
                                        app('cons', bytes_, app('nil', NAT),
                                            Var('ih')),
                                        app('cons', bytes_,
                                            app('cons', NAT, Var('h'),
                                                app('head', bytes_,
                                                    app('nil', NAT),
                                                    Var('ih'))),
                                            app('tail', bytes_,
                                                Var('ih'))))))),
                      Var('xs')))))

    # -- records ------------------------------------------------------------
    # A single-constructor inductive is a record; what it lacks is names.  The
    # projections and updaters below are generated from the field list, so a
    # ten-field kernel context reads as `c.frames` rather than as a spine of
    # fst and snd through nine nested Prods.
    record(env, 'Context', [
        ('frames', app('List', NAT)),   # the frame table
        ('queue', app('List', NAT)),    # runnable thread ids, in order
        ('schemes', app('List', NAT)),  # scheme table: crustos/schemes.py
        ('current', NAT),             # index of the running thread
        ('nthreads', NAT),
        ('ticks', NAT),
    ])

    # -- the proposition a contract makes -----------------------------------
    define(env, 'Holds', arrow(BOOL, PROP),
           Lambda('b', BOOL, app('Eq', BOOL, Var('b'), Var('true'))))

    # -- what a while loop needs, proved once -------------------------------
    # A `while` lowers to iterating a guarded step.  Three things are needed
    # of it and all three are theorems here, not assumptions: that one guarded
    # pass keeps the invariant, that iterating something which keeps it keeps
    # it, and that the variant bounds how many passes there can be.
    inductive(env, 'TrueP', [('trivial', [])], level=0)
    holds = lambda x: App(Var('Holds'), x)
    yes = app('refl', BOOL, Var('true'))
    succ_ = lambda a: App(Var('succ'), a)
    leb_ = lambda a, b: app('leb', a, b)

    # From a false premise, anything: `Holds false` is `Eq Bool false true`,
    # so Eq.ind transports along it into a motive that reads `true` as the
    # goal and `false` as something already proved.
    define(env, 'absurd', Pi('C', PROP, arrow(holds(Var('false')), Var('C'))),
           Lambda('C', PROP, Lambda('h', holds(Var('false')), app(
               'Eq.ind', BOOL, Var('false'),
               Lambda('b', BOOL, Lambda(
                   '_t', app('Eq', BOOL, Var('false'), Var('b')),
                   app('Bool.rec', Lambda('_', BOOL, PROP), Var('C'),
                       Var('TrueP'), Var('b')))),
               Var('trivial'), Var('true'), Var('h')))))

    refl_motive = Lambda('x', NAT, holds(leb_(Var('x'), Var('x'))))
    define(env, 'leb_refl', Pi('x', NAT, holds(leb_(Var('x'), Var('x')))),
           Lambda('x', NAT, app('Nat.ind', refl_motive, yes,
                                Lambda('k', NAT, Lambda(
                                    'ih', App(refl_motive, Var('k')),
                                    Var('ih'))), Var('x'))))

    # transitivity: induction on the first, then a case split on the other two
    x_, y_, z_ = Var('x'), Var('y'), Var('z')
    x2, y2, z2 = Var('x2'), Var('y2'), Var('z2')
    chain = lambda a, b, c: arrow(holds(leb_(a, b)),
                                  arrow(holds(leb_(b, c)), holds(leb_(a, c))))
    Mx = Lambda('x', NAT, Pi('y', NAT, Pi('z', NAT, chain(x_, y_, z_))))
    base_x = Lambda('y', NAT, Lambda('z', NAT, Lambda(
        'h1', holds(leb_(numeral(0), y_)),
        Lambda('h2', holds(leb_(y_, z_)), yes))))
    Mz = Lambda('z', NAT, chain(succ_(x2), succ_(y2), z_))
    base_z = Lambda('h1', holds(leb_(succ_(x2), succ_(y2))), Lambda(
        'h2', holds(leb_(succ_(y2), numeral(0))),
        app('absurd', holds(leb_(succ_(x2), numeral(0))), Var('h2'))))
    step_z = Lambda('z2', NAT, Lambda('ihz', App(Mz, z2), Lambda(
        'h1', holds(leb_(succ_(x2), succ_(y2))), Lambda(
            'h2', holds(leb_(succ_(y2), succ_(z2))),
            app(Var('ih'), y2, z2, Var('h1'), Var('h2'))))))
    My = Lambda('y', NAT, Pi('z', NAT, chain(succ_(x2), y_, z_)))
    base_y = Lambda('z', NAT, Lambda(
        'h1', holds(leb_(succ_(x2), numeral(0))), Lambda(
            'h2', holds(leb_(numeral(0), z_)),
            app('absurd', holds(leb_(succ_(x2), z_)), Var('h1')))))
    step_y = Lambda('y2', NAT, Lambda('ihy', App(My, y2), Lambda(
        'z', NAT, app('Nat.ind', Mz, base_z, step_z, z_))))
    step_x = Lambda('x2', NAT, Lambda('ih', App(Mx, x2), Lambda(
        'y', NAT, app('Nat.ind', My, base_y, step_y, y_))))
    define(env, 'leb_trans',
           Pi('x', NAT, Pi('y', NAT, Pi('z', NAT, chain(x_, y_, z_)))),
           Lambda('x', NAT, app('Nat.ind', Mx, base_x, step_x, x_)))

    # leb_succ and sub_le: subtracting never grows a number, and `sub m 0`
    # is only `m` up to an induction, since the recursion is on the first
    # argument.  Both are needed before a variant can be reasoned about.
    succ_motive = Lambda('x', NAT, holds(leb_(Var('x'), succ_(Var('x')))))
    define(env, 'leb_succ', Pi('x', NAT, holds(leb_(Var('x'), succ_(Var('x'))))),
           Lambda('x', NAT, app('Nat.ind', succ_motive, yes,
                                Lambda('k', NAT, Lambda(
                                    'ih', App(succ_motive, Var('k')),
                                    Var('ih'))), Var('x'))))

    sub_ = lambda a, b: app('sub', a, b)
    Msub = Lambda('m', NAT, Pi('n', NAT, holds(leb_(sub_(Var('m'), Var('n')),
                                                    Var('m')))))
    Minner = Lambda('n', NAT, holds(leb_(sub_(succ_(Var('m2')), Var('n')),
                                         succ_(Var('m2')))))
    sub_le_step = Lambda('m2', NAT, Lambda('ih', App(Msub, Var('m2')), Lambda(
        'n', NAT, app('Nat.ind', Minner,
                      app('leb_refl', Var('m2')),
                      Lambda('n2', NAT, Lambda('_i', App(Minner, Var('n2')),
                             app('leb_trans', sub_(Var('m2'), Var('n2')),
                                 Var('m2'), succ_(Var('m2')),
                                 App(Var('ih'), Var('n2')),
                                 app('leb_succ', Var('m2'))))),
                      Var('n')))))
    define(env, 'sub_le',
           Pi('m', NAT, Pi('n', NAT, holds(leb_(sub_(Var('m'), Var('n')),
                                                Var('m'))))),
           Lambda('m', NAT, app('Nat.ind', Msub,
                                Lambda('n', NAT, yes), sub_le_step, Var('m'))))

    # n - (c+1) < n - c, whenever c < n: what a `n - i` variant needs
    c_, n_ = Var('c'), Var('n')
    ltb_ = lambda a, b: app('ltb', a, b)
    Mn = Lambda('n', NAT, Pi('c', NAT, arrow(
        holds(ltb_(c_, n_)),
        holds(ltb_(sub_(n_, succ_(c_)), sub_(n_, c_))))))
    Mc = Lambda('c', NAT, arrow(
        holds(ltb_(c_, succ_(Var('n2')))),
        holds(ltb_(sub_(succ_(Var('n2')), succ_(c_)),
                   sub_(succ_(Var('n2')), c_)))))
    sub_base = Lambda('c', NAT, Lambda(
        'h', holds(ltb_(c_, numeral(0))),
        app('absurd', holds(ltb_(sub_(numeral(0), succ_(c_)),
                                 sub_(numeral(0), c_))), Var('h'))))
    sub_zero = Lambda('h', holds(ltb_(numeral(0), succ_(Var('n2')))),
                      app('sub_le', Var('n2'), numeral(0)))
    sub_succ = Lambda('c2', NAT, Lambda('_ihc', App(Mc, Var('c2')), Lambda(
        'h', holds(ltb_(succ_(Var('c2')), succ_(Var('n2')))),
        app(Var('ihn'), Var('c2'), Var('h')))))
    sub_step = Lambda('n2', NAT, Lambda('ihn', App(Mn, Var('n2')), Lambda(
        'c', NAT, app('Nat.ind', Mc, sub_zero, sub_succ, c_))))
    define(env, 'sub_lt',
           Pi('n', NAT, Pi('c', NAT, arrow(
               holds(ltb_(c_, n_)),
               holds(ltb_(sub_(n_, succ_(c_)), sub_(n_, c_)))))),
           Lambda('n', NAT, app('Nat.ind', Mn, sub_base, sub_step, n_)))

    # -- the fold, as "iterate n times" -------------------------------------
    # Written so that one pass peels off the *front*: iter (n+1) s is
    # iter n (step s), not step (iter n s).  Both compute the same thing, but
    # the variant comes down on the first pass, so that is where an induction
    # on termination needs to be able to look.
    S, I_, f_, b_, V_ = Var('S'), Var('I'), Var('f'), Var('b'), Var('V')
    guarded_at = lambda t: app('ite', S, App(b_, t), App(f_, t), t)
    iterate = lambda n: app('Nat.rec', Lambda('_', NAT, arrow(S, S)),
                            Lambda('s', S, Var('s')),
                            Lambda('k', NAT, Lambda(
                                'ih', arrow(S, S), Lambda(
                                    's', S, App(Var('ih'),
                                                guarded_at(Var('s')))))), n)
    at_ = lambda n, t: App(iterate(n), t)
    two_step = Pi('s', S, arrow(holds(App(I_, Var('s'))),
                                arrow(holds(App(b_, Var('s'))),
                                      holds(App(I_, App(f_, Var('s')))))))
    one_step = Pi('s', S, arrow(holds(App(I_, Var('s'))),
                                holds(App(I_, guarded_at(Var('s'))))))
    quantify = lambda body: Pi('S', TYPE0, Pi('I', arrow(S, BOOL), Pi(
        'f', arrow(S, S), Pi('b', arrow(S, BOOL), body))))
    close_over = lambda t: _abstract_over(
        t, [('b', arrow(S, BOOL)), ('f', arrow(S, S)),
            ('I', arrow(S, BOOL)), ('S', TYPE0)])

    # guarded: a case split on the condition.  In the branch where it holds,
    # the hypothesis needed is `Holds true`, which refl proves -- which is why
    # the running condition is two separate hypotheses and not one `andb`.
    supposing = lambda t: arrow(holds(App(I_, Var('s'))),
                                arrow(holds(t),
                                      holds(App(I_, App(f_, Var('s'))))))
    branch = Lambda('x', BOOL, arrow(
        supposing(Var('x')),
        holds(App(I_, app('ite', S, Var('x'), App(f_, Var('s')), Var('s'))))))
    define(env, 'guarded', quantify(arrow(two_step, one_step)),
           close_over(Lambda('P', two_step, Lambda('s', S, Lambda(
               'h', holds(App(I_, Var('s'))),
               App(app('Bool.ind', branch,
                       Lambda('H', supposing(Var('true')),
                              app(Var('H'), Var('h'), yes)),
                       Lambda('H', supposing(Var('false')), Var('h')),
                       App(b_, Var('s'))),
                   App(Var('P'), Var('s'))))))))

    after_ = lambda n: Pi('s', S, arrow(holds(App(I_, Var('s'))),
                                        holds(App(I_, at_(n, Var('s'))))))
    keep_base = Lambda('s', S, Lambda('h', holds(App(I_, Var('s'))),
                                      Var('h')))
    keep_step = Lambda('k', NAT, Lambda('ih', after_(Var('k')), Lambda(
        's', S, Lambda('h', holds(App(I_, Var('s'))),
                       app(Var('ih'), guarded_at(Var('s')),
                           app(Var('H'), Var('s'), Var('h')))))))
    define(env, 'fold_preserves',
           quantify(arrow(one_step, Pi('n', NAT, after_(Var('n'))))),
           close_over(Lambda('H', one_step, Lambda('n', NAT, app(
               'Nat.ind', Lambda('n', NAT, after_(Var('n'))),
               keep_base, keep_step, Var('n'))))))
    define(env, 'loop_preserves',
           quantify(arrow(two_step, Pi('n', NAT, after_(Var('n'))))),
           close_over(Lambda('P', two_step,
                             app('fold_preserves', S, I_, f_, b_,
                                 app('guarded', S, I_, f_, b_, Var('P'))))))

    # -- termination --------------------------------------------------------
    over = lambda body: Pi('S', TYPE0, Pi('I', arrow(S, BOOL), Pi(
        'f', arrow(S, S), Pi('b', arrow(S, BOOL), Pi(
            'V', arrow(S, NAT), body)))))
    shut = lambda t: _abstract_over(
        t, [('V', arrow(S, NAT)), ('b', arrow(S, BOOL)), ('f', arrow(S, S)),
            ('I', arrow(S, BOOL)), ('S', TYPE0)])
    sv, kv = Var('s'), Var('k')
    notb_b = lambda t: holds(app('notb', App(b_, t)))

    # stuck: once the condition is false, iterating changes nothing
    Ms = Lambda('n', NAT, Pi('s', S, arrow(notb_b(Var('s')),
                                           notb_b(at_(Var('n'), Var('s'))))))
    Mb = Lambda('x', BOOL, arrow(
        holds(app('notb', Var('x'))),
        notb_b(at_(kv, app('ite', S, Var('x'), App(f_, sv), sv)))))
    define(env, 'stuck', over(Pi('n', NAT, App(Ms, Var('n')))),
           shut(Lambda('n', NAT, app(
               'Nat.ind', Ms,
               Lambda('s', S, Lambda('h', notb_b(Var('s')), Var('h'))),
               Lambda('k', NAT, Lambda('ih', App(Ms, kv), Lambda(
                   's', S, Lambda('h', notb_b(sv), app(
                       app('Bool.ind', Mb,
                           Lambda('hn', holds(app('notb', Var('true'))),
                                  app('absurd', notb_b(at_(kv, App(f_, sv))),
                                      Var('hn'))),
                           Lambda('hn', holds(app('notb', Var('false'))),
                                  app(Var('ih'), sv, Var('h'))),
                           App(b_, sv)),
                       Var('h')))))),
               Var('n')))))

    # fold_terminates: the variant is a bound on how many passes there can be
    hI = lambda t: holds(App(I_, t))
    rank = lambda t: App(V_, t)
    keeps = Pi('s', S, arrow(hI(Var('s')), arrow(holds(App(b_, Var('s'))),
                                                 hI(App(f_, Var('s'))))))
    drops = Pi('s', S, arrow(hI(Var('s')), arrow(holds(App(b_, Var('s'))),
        holds(app('ltb', rank(App(f_, Var('s'))), rank(Var('s')))))))
    Mt = Lambda('n', NAT, Pi('s', S, arrow(hI(Var('s')), arrow(
        holds(leb_(rank(Var('s')), Var('n'))),
        notb_b(at_(Var('n'), Var('s')))))))
    dropped = lambda nm: app(app(Var(nm), Var('hi')), yes)
    keep_at = lambda t: arrow(hI(sv), arrow(holds(t), hI(App(f_, sv))))
    drop_at = lambda t: arrow(hI(sv), arrow(holds(t), holds(
        leb_(succ_(rank(App(f_, sv))), rank(sv)))))
    Mb0 = Lambda('x', BOOL, arrow(drop_at(Var('x')),
                                  holds(app('notb', Var('x')))))
    base_t = Lambda('s', S, Lambda('hi', hI(sv), Lambda(
        'hz', holds(leb_(rank(sv), numeral(0))),
        App(app('Bool.ind', Mb0,
                Lambda('D1', drop_at(Var('true')),
                       app('leb_trans', succ_(rank(App(f_, sv))), rank(sv),
                           numeral(0), dropped('D1'), Var('hz'))),
                Lambda('D1', drop_at(Var('false')), yes), App(b_, sv)),
            App(Var('D'), sv)))))
    stuck_at = lambda t: arrow(holds(app('notb', t)), notb_b(at_(kv, sv)))
    Mb1 = Lambda('x', BOOL, arrow(keep_at(Var('x')), arrow(
        drop_at(Var('x')), arrow(stuck_at(Var('x')), notb_b(at_(
            kv, app('ite', S, Var('x'), App(f_, sv), sv)))))))
    step_t = Lambda('k', NAT, Lambda('ih', App(Mt, kv), Lambda(
        's', S, Lambda('hi', hI(sv), Lambda(
            'hn', holds(leb_(rank(sv), succ_(kv))), app(
                app('Bool.ind', Mb1,
                    Lambda('P1', keep_at(Var('true')), Lambda(
                        'D1', drop_at(Var('true')), Lambda(
                            '_st', stuck_at(Var('true')),
                            app(Var('ih'), App(f_, sv),
                                app(app(Var('P1'), Var('hi')), yes),
                                app('leb_trans', succ_(rank(App(f_, sv))),
                                    rank(sv), succ_(kv), dropped('D1'),
                                    Var('hn')))))),
                    Lambda('P1', keep_at(Var('false')), Lambda(
                        'D1', drop_at(Var('false')), Lambda(
                            'st', stuck_at(Var('false')),
                            App(Var('st'), yes)))),
                    App(b_, sv)),
                App(Var('P'), sv), App(Var('D'), sv),
                app('stuck', S, I_, f_, b_, V_, kv, sv)))))))
    define(env, 'fold_terminates',
           over(arrow(keeps, arrow(drops, Pi('n', NAT, App(Mt, Var('n')))))),
           shut(Lambda('P', keeps, Lambda('D', drops, Lambda(
               'n', NAT, app('Nat.ind', Mt, base_t, step_t, Var('n')))))))

    return env


# ------------------------------------------------- types of the fragment

BYTES = App(Var('List'), NAT)          # a string is a list of bytes
STRS = App(Var('List'), BYTES)

TYPE_NAMES = {'Nat': NAT, 'Bool': BOOL, 'int': NAT, 'bool': BOOL,
              'Array': BYTES, 'Bytes': BYTES, 'str': BYTES, 'Strs': STRS}

# name -> ([argument types], result type), for calls the fragment understands
SIGNATURES = {
    'add': ([NAT, NAT], NAT), 'mul': ([NAT, NAT], NAT),
    'sub': ([NAT, NAT], NAT), 'pred': ([NAT], NAT),
    'succ': ([NAT], NAT),
    'find': ([BYTES, NAT], NAT), 'take': ([BYTES, NAT], BYTES),
    'drop': ([BYTES, NAT], BYTES), 'eqs': ([BYTES, BYTES], BOOL),
    'split': ([BYTES, NAT], STRS),
    'leb': ([NAT, NAT], BOOL), 'ltb': ([NAT, NAT], BOOL),
    'eqb': ([NAT, NAT], BOOL), 'dvdb': ([NAT, NAT], BOOL),
    'modb': ([NAT, NAT], NAT),
    'notb': ([BOOL], BOOL), 'andb': ([BOOL, BOOL], BOOL),
    'orb': ([BOOL, BOOL], BOOL),
    'cons': ([NAT, BYTES], BYTES),
}

PRELUDE_ENV = None      # built below, once the tables above exist

BINOPS = {ast.Add: 'add', ast.Sub: 'sub', ast.Mult: 'mul', ast.Mod: 'modb'}
COMPARES = {ast.Lt: ('ltb', False), ast.Gt: ('ltb', True),
            ast.LtE: ('leb', False), ast.GtE: ('leb', True),
            ast.Eq: ('eqb', False)}


def element_type(list_type, node=None):
    """The A in `List A`, or None if this is not a list type."""
    head, args = L.spine(normalize(list_type, PRELUDE_ENV))
    if isinstance(head, Var) and head.name == 'List' and len(args) == 1:
        return args[0]
    return None


def default_for(ty):
    """A value of ty, for a read that the contract has not yet ruled out.

    Indexing is total here: out of range reads this rather than being
    undefined.  The bound is what a contract is *for*; making the definition
    assume it would be assuming the thing to be proved.
    """
    inner = element_type(ty)
    if inner is not None:
        return app('nil', inner)
    if normalize(ty, PRELUDE_ENV) == BOOL:
        return Var('false')
    return numeral(0)


def same_type(a, b):
    return normalize(a, PRELUDE_ENV) == normalize(b, PRELUDE_ENV)


PRELUDE_ENV = prelude()


# --------------------------------------------------- symbolic execution

class ImpToLean:
    r"""Evaluate an imperative body into a pure kernel term.

    The store is a Python dict from variable name to the term it currently
    holds, so an assignment is a substitution performed here rather than a
    `let` node the kernel would have to understand.  Nothing about this is
    trusted: whatever it produces is handed to `type_check`, which knows
    nothing of Python.
    """

    def __init__(self, where='<body>', signatures=None, env=None):
        self.where = where
        self.env = env
        self.store = {}          # name -> kernel term
        self.types = {}          # name -> kernel type
        self.signatures = dict(SIGNATURES)
        self.signatures.update(signatures or {})
        self.counter = 0
        self.obligations = []          # (label, goal) raised by while loops
        self.expected = None           # the type an annotation is asking for
        self.shapes = []               # the fold each while loop lowered to
        self.assumptions = []          # the procedure's preconditions

    def fail(self, node, message):
        line = getattr(node, 'lineno', '?')
        raise ContractError(f"{self.where}, line {line}: {message}")

    def fresh(self, hint):
        self.counter += 1
        return f"_{hint}{self.counter}"

    # -- types --------------------------------------------------------------

    def read_type(self, node, where):
        if isinstance(node, ast.Name) and node.id in TYPE_NAMES:
            return TYPE_NAMES[node.id]
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            if node.value in TYPE_NAMES:
                return TYPE_NAMES[node.value]
            return L.parse_type(node.value)
        self.fail(node, f"cannot read {where} as a type of this fragment "
                        f"(known: {', '.join(sorted(TYPE_NAMES))})")

    def type_of_expr(self, node):
        """The type of an expression, structurally.

        Deliberately not a call to `type_check`: at this point a parameter is
        still a free name, so there is nothing yet to check it against.  Any
        mistake made here shows up as a kernel error later, not as a theorem.
        """
        if isinstance(node, ast.Constant):
            if isinstance(node.value, bool):
                return BOOL
            if isinstance(node.value, int) and node.value >= 0:
                return NAT
            self.fail(node, f"{node.value!r} is not a value of this fragment")
        if isinstance(node, ast.List):
            if self.expected is not None:
                return self.expected
            if node.elts:
                return App(Var('List'), self.type_of_expr(node.elts[0]))
            self.fail(node, "an empty list literal needs an annotation")
        if isinstance(node, ast.Name):
            if node.id in self.types:
                return self.types[node.id]
            if node.id in ('True', 'False'):
                return BOOL
            self.fail(node, f"'{node.id}' is not bound here")
        if isinstance(node, ast.BinOp):
            return NAT
        if isinstance(node, (ast.Compare, ast.BoolOp)):
            return BOOL
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.Not):
            return BOOL     # of a Nat too: `not n` is `n = 0`
        if isinstance(node, ast.Subscript):
            inner = element_type(self.type_of_expr(node.value))
            if inner is None:
                self.fail(node, "this is not something that can be indexed")
            return inner
        if isinstance(node, ast.Attribute):
            return self.field_of(node)[1]
        if isinstance(node, ast.IfExp):
            return self.type_of_expr(node.body)
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name):
                if node.func.id in ('len', 'alen'):
                    return NAT
                if node.func.id == 'cons':
                    return self.type_of_expr(node.args[1])
                if node.func.id in ('snoc', 'append', 'rev'):
                    return self.type_of_expr(node.args[0])
                sig = self.signatures.get(node.func.id)
                if sig:
                    return sig[1]
            self.fail(node, "the result type of this call is not declared; "
                            "add it to SIGNATURES")
        self.fail(node, f"cannot give a type to {type(node).__name__}")

    def field_of(self, node):
        """The record a field access is reaching into, and the field's type."""
        owner = self.type_of_expr(node.value)
        name = owner.name if isinstance(owner, Var) else None
        if name not in RECORDS:
            self.fail(node, f"{readable(owner)} is not a record, so it has no "
                            f"field '{node.attr}'")
        for field, ftype in RECORDS[name]:
            if field == node.attr:
                return name, ftype
        self.fail(node, f"{name} has no field '{node.attr}' "
                        f"(it has {', '.join(f for f, _ in RECORDS[name])})")

    # -- expressions --------------------------------------------------------

    def expr(self, node):
        if isinstance(node, ast.Constant):
            if node.value is True:
                return Var('true')
            if node.value is False:
                return Var('false')
            if isinstance(node.value, int) and node.value >= 0:
                return numeral(node.value)
            self.fail(node, f"{node.value!r} is not a term the kernel knows")

        if isinstance(node, ast.Name):
            if node.id in self.store:
                return self.store[node.id]
            self.fail(node, f"'{node.id}' is read before it is bound")

        if isinstance(node, ast.List):
            # `out: 'Array' = []` is how schemes.py writes it, and an empty
            # literal has no type of its own -- the annotation supplies it.
            if self.expected is None:
                self.fail(node, "a list literal here has no type; write it as "
                                "`name: 'Array' = [...]` so there is one")
            inner = element_type(self.expected)
            if inner is None:
                self.fail(node, f"{readable(self.expected)} is not a list type")
            out = app('nil', inner)
            for item in reversed(node.elts):
                out = app('cons', inner, self.expr(item), out)
            return out

        if isinstance(node, ast.BinOp):
            op = BINOPS.get(type(node.op))
            if op is None:
                self.fail(node, f"{type(node.op).__name__} has no meaning in "
                                f"this fragment")
            return app(op, self.expr(node.left), self.expr(node.right))

        if isinstance(node, ast.UnaryOp):
            if isinstance(node.op, ast.Not):
                inner = self.expr(node.operand)
                if same_type(self.type_of_expr(node.operand), NAT):
                    # `assert not len(ptr) % 4` is C's spelling, and C's
                    # meaning: not(n) is n = 0.  Keeping the spelling matters,
                    # because this is the same text extensions.py already
                    # lifts out of a C function header.
                    return app('eqb', inner, numeral(0))
                return app('notb', inner)
            self.fail(node, f"{type(node.op).__name__} is not supported")

        if isinstance(node, ast.BoolOp):
            op = 'andb' if isinstance(node.op, ast.And) else 'orb'
            out = self.expr(node.values[0])
            for v in node.values[1:]:
                out = app(op, out, self.expr(v))
            return out

        if isinstance(node, ast.Compare):
            if len(node.ops) != 1:
                self.fail(node, "chained comparison: write it as `and`")
            entry = COMPARES.get(type(node.ops[0]))
            if entry is None:
                self.fail(node, f"{type(node.ops[0]).__name__} is not a "
                                f"decidable comparison here")
            name, flip = entry
            left, right = self.expr(node.left), self.expr(node.comparators[0])
            if flip:
                left, right = right, left
            return app(name, left, right)

        if isinstance(node, ast.IfExp):
            ty = self.type_of_expr(node.body)
            return app('ite', ty, self.expr(node.test),
                       self.expr(node.body), self.expr(node.orelse))

        if isinstance(node, ast.Subscript):
            container = self.type_of_expr(node.value)
            inner = element_type(container)
            if inner is None:
                self.fail(node, f"{readable(container)} cannot be indexed")
            return app('nth', inner, default_for(inner),
                       self.expr(node.value), self.expr(node.slice))

        if isinstance(node, ast.Attribute):
            record_name, _ = self.field_of(node)
            return app(f'{record_name}.{node.attr}', self.expr(node.value))

        if isinstance(node, ast.Call):
            if node.keywords:
                self.fail(node, "keyword arguments have no meaning here")
            if not isinstance(node.func, ast.Name):
                self.fail(node, "only a plain name may be called")
            name = node.func.id
            if name in ('len', 'alen'):
                if len(node.args) != 1:
                    self.fail(node, "len takes one argument")
                container = self.type_of_expr(node.args[0])
                inner = element_type(container)
                if inner is None:
                    self.fail(node, f"{readable(container)} has no length")
                return app('len', inner, self.expr(node.args[0]))
            if name in ('snoc', 'append', 'rev'):
                container = self.type_of_expr(node.args[0])
                inner = element_type(container)
                if inner is None:
                    self.fail(node, f"{name} needs a list, not "
                                    f"{readable(container)}")
                return app(name, inner,
                           *[self.expr(a) for a in node.args])
            if name == 'cons':
                if len(node.args) != 2:
                    self.fail(node, "cons takes an element and a list")
                container = self.type_of_expr(node.args[1])
                inner = element_type(container)
                if inner is None:
                    self.fail(node, f"cannot cons onto {readable(container)}")
                return app('cons', inner, self.expr(node.args[0]),
                           self.expr(node.args[1]))
            sig = self.signatures.get(name)
            if sig is None:
                self.fail(node, f"'{name}' is not a function this fragment "
                                f"knows; add a signature for it")
            args, _ = sig
            if len(node.args) != len(args):
                self.fail(node, f"'{name}' takes {len(args)} argument(s), "
                                f"given {len(node.args)}")
            target = 'alen' if name == 'len' else name
            return app(target, *[self.expr(a) for a in node.args])

        self.fail(node, f"{type(node).__name__} is not part of this fragment")

    # -- statements ---------------------------------------------------------

    def assigned(self, stmts, acc=None):
        """Every name a block writes to, in first-write order."""
        acc = [] if acc is None else acc
        for s in stmts:
            if isinstance(s, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
                targets = s.targets if isinstance(s, ast.Assign) else [s.target]
                for t in targets:
                    if isinstance(t, ast.Attribute) and isinstance(t.value,
                                                                   ast.Name):
                        t = t.value
                    if isinstance(t, ast.Name) and t.id not in acc:
                        acc.append(t.id)
            elif isinstance(s, ast.If):
                self.assigned(s.body, acc)
                self.assigned(s.orelse, acc)
            elif isinstance(s, (ast.For, ast.While)):
                self.assigned(s.body, acc)
        return acc

    def block(self, stmts):
        """Run a block.  Returns the returned term, or None if it falls off."""
        for stmt in stmts:
            out = self.statement(stmt)
            if out is not None:
                return out
        return None

    def statement(self, stmt):
        if isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant):
            return None                                   # a docstring

        if isinstance(stmt, ast.Pass):
            return None

        if isinstance(stmt, (ast.Assign, ast.AnnAssign)):
            if isinstance(stmt, ast.Assign):
                if len(stmt.targets) != 1:
                    self.fail(stmt, "one target per assignment, please")
                target = stmt.targets[0]
            else:
                target = stmt.target
            if stmt.value is None:
                self.fail(stmt, "a declaration without a value has no meaning")
            if isinstance(target, ast.Attribute):
                # c.field = v  is  c = Record.with_field c v.  Nothing is
                # mutated: the syscall gets a context and returns one.
                record_name, ftype = self.field_of(target)
                if not isinstance(target.value, ast.Name):
                    self.fail(stmt, "only a field of a plain variable may be "
                                    "assigned")
                base = target.value.id
                value = self.expr(stmt.value)
                if not same_type(self.type_of_expr(stmt.value), ftype):
                    self.fail(stmt, f"'{base}.{target.attr}' is "
                                    f"{readable(ftype)} and this assigns "
                                    f"{readable(self.type_of_expr(stmt.value))}")
                self.store[base] = app(f'{record_name}.with_{target.attr}',
                                       self.store[base], value)
                return None
            if not isinstance(target, ast.Name):
                self.fail(stmt, "only a plain variable or a record field may "
                                "be assigned; there is no mutable heap in "
                                "this fragment")
            annotated = (isinstance(stmt, ast.AnnAssign) and stmt.annotation)
            self.expected = (self.read_type(stmt.annotation, 'the annotation')
                             if annotated else None)
            ty = self.expected or self.type_of_expr(stmt.value)
            term = self.expr(stmt.value)
            self.expected = None
            if target.id in self.types and not same_type(self.types[target.id], ty):
                self.fail(stmt, f"'{target.id}' was "
                                f"{readable(self.types[target.id])} and this "
                                f"assigns it {readable(ty)}; a variable keeps "
                                f"one type, so the loop accumulator has one")
            self.store[target.id] = term
            self.types[target.id] = ty
            return None

        if isinstance(stmt, ast.AugAssign):
            op = BINOPS.get(type(stmt.op))
            if op is None:
                self.fail(stmt, f"{type(stmt.op).__name__}= is not supported")
            if not isinstance(stmt.target, ast.Name):
                self.fail(stmt, "only a plain variable may be updated")
            return self.statement(ast.copy_location(ast.Assign(
                targets=[stmt.target],
                value=ast.copy_location(ast.BinOp(
                    left=ast.copy_location(ast.Name(id=stmt.target.id,
                                                    ctx=ast.Load()), stmt),
                    op=stmt.op, right=stmt.value), stmt)), stmt))

        if isinstance(stmt, ast.Assert):
            return None            # a precondition; lifted before the body

        if isinstance(stmt, ast.If):
            return self.branch(stmt)

        if isinstance(stmt, ast.For):
            return self.loop(stmt)

        if isinstance(stmt, ast.While):
            return self.while_loop(stmt)

        if isinstance(stmt, ast.Return):
            if stmt.value is None:
                self.fail(stmt, "return needs a value")
            return self.expr(stmt.value)

        self.fail(stmt, f"{type(stmt).__name__} is not part of this fragment")

    def branch(self, stmt):
        """`if` joins the two stores with `ite`, one variable at a time."""
        if self.returns(stmt.body) or self.returns(stmt.orelse):
            self.fail(stmt, "a `return` inside `if` is not supported yet: "
                            "the join would have to know which branch ran. "
                            "Assign to a variable and return it at the end.")
        test = self.expr(stmt.test)
        if not same_type(self.type_of_expr(stmt.test), BOOL):
            self.fail(stmt, "the condition of an `if` must be decidable (Bool)")

        before_store, before_types = dict(self.store), dict(self.types)
        self.block(stmt.body)
        then_store, then_types = dict(self.store), dict(self.types)

        self.store, self.types = dict(before_store), dict(before_types)
        self.block(stmt.orelse)
        else_store, else_types = dict(self.store), dict(self.types)

        self.store, self.types = dict(before_store), dict(before_types)
        for name in self.assigned([stmt]):
            in_then = name in then_store
            in_else = name in else_store
            if not (in_then and in_else) and name not in before_store:
                self.fail(stmt, f"'{name}' is assigned in only one branch and "
                                f"has no value before the `if`, so it would be "
                                f"undefined on the other path")
            hi = then_store.get(name, before_store.get(name))
            lo = else_store.get(name, before_store.get(name))
            ty = then_types.get(name, else_types.get(name))
            other = else_types.get(name, ty)
            if not same_type(ty, other):
                self.fail(stmt, f"'{name}' is {readable(ty)} on one branch and "
                                f"{readable(other)} on the other")
            self.store[name] = app('ite', ty, test, hi, lo)
            self.types[name] = ty
        return None

    def returns(self, stmts):
        return any(isinstance(s, ast.Return) or
                   (isinstance(s, (ast.If, ast.For, ast.While)) and
                    (self.returns(s.body) or self.returns(getattr(s, 'orelse', []))))
                   for s in stmts)

    def loop(self, stmt):
        r"""`for i in range(n)` is `Nat.rec`: the fold it always was."""
        if stmt.orelse:
            self.fail(stmt, "`for ... else` has no meaning here")
        if self.returns(stmt.body):
            self.fail(stmt, "a `return` inside a loop is not supported: the "
                            "fold has no way to stop early")
        if not isinstance(stmt.target, ast.Name):
            self.fail(stmt, "the loop variable must be a plain name")
        call = stmt.iter
        if not (isinstance(call, ast.Call) and isinstance(call.func, ast.Name)
                and call.func.id == 'range' and len(call.args) == 1):
            self.fail(stmt, "only `for i in range(n)` is supported: the bound "
                            "is what makes the loop a fold")
        bound = self.expr(call.args[0])
        index = stmt.target.id

        carried = [n for n in self.assigned(stmt.body) if n != index]
        for name in carried:
            if name not in self.store:
                self.fail(stmt, f"'{name}' is assigned in the loop but has no "
                                f"value going in; a fold needs somewhere to "
                                f"start")
        if not carried:
            self.fail(stmt, "this loop assigns nothing that outlives it, so "
                            "it has no meaning as a fold")

        types = [self.types[n] for n in carried]
        acc_type = types[-1]
        for ty in reversed(types[:-1]):
            acc_type = app('Prod', ty, acc_type)

        init = self.pack([self.store[n] for n in carried], types)
        acc = self.fresh('acc')

        outer_store, outer_types = dict(self.store), dict(self.types)
        for pos, name in enumerate(carried):
            self.store[name] = self.project(Var(acc), types, pos)
        self.store[index] = Var(index)
        self.types[index] = NAT
        self.block(stmt.body)
        step_body = self.pack([self.store[n] for n in carried], types)
        self.store, self.types = outer_store, outer_types

        folded = self.name_loop(
            rec(NAT, acc_type, init,
                Lambda(index, NAT, Lambda(acc, acc_type, step_body)), bound),
            acc_type)

        self.bind(carried, types, acc_type, folded)
        return None

    def markers(self, stmt):
        """The `invariant` and `variant` annotations at the top of a body."""
        found, rest = {}, list(stmt.body)
        while rest and isinstance(rest[0], ast.Assert):
            test = rest[0].test
            if not (isinstance(test, ast.Call)
                    and isinstance(test.func, ast.Name)
                    and test.func.id in ('invariant', 'variant')):
                break
            if len(test.args) != 1:
                self.fail(test, f"{test.func.id}() takes one expression")
            found[test.func.id] = test.args[0]
            rest = rest[1:]
        return found, rest

    def while_loop(self, stmt):
        r"""`while` is admissible once the annotation supplies the bound.

        It was refused because a while loop terminates for a reason the text
        does not state.  An explicit variant states it: a Nat that strictly
        decreases on every pass.  The loop then lowers to the same fold a
        `for` does, with the variant's value on entry as the number of steps,
        and each step guarded so that once the condition is false the state
        stops changing:

            while b: c   ==>   Nat.rec (lam _. S) s0
                                       (lam _ s. ite (b s) (c s) s)
                                       (variant s0)

        That the fold is the loop is not assumed.  It is emitted as an
        obligation -- `progress`, that the condition really is false at the
        end -- so the claim is checked by the kernel rather than argued for
        in a comment.  The invariant and variant obligations are the tools
        for proving it; they are stated too, and none of them is trusted.
        """
        if stmt.orelse:
            self.fail(stmt, "`while ... else` has no meaning here")
        if self.returns(stmt.body):
            self.fail(stmt, "a `return` inside a loop is not supported: the "
                            "fold has no way to stop early")
        found, body = self.markers(stmt)
        if 'variant' not in found:
            self.fail(stmt, "a `while` loop needs a variant to be admissible: "
                            "write `assert variant(<Nat that decreases>)` as "
                            "its first statement. Without one the loop "
                            "terminates for a reason the text does not state, "
                            "and lowering it would mean guessing a bound.")
        if 'invariant' not in found:
            self.fail(stmt, "a `while` loop needs `assert invariant(<Bool>)`: "
                            "the variant proves it stops, the invariant is "
                            "what it is still true of when it does")
        inv_node, var_node = found['invariant'], found['variant']

        if not same_type(self.type_of_expr(stmt.test), BOOL):
            self.fail(stmt, "the condition of a `while` must be decidable")
        if not same_type(self.type_of_expr(var_node), NAT):
            self.fail(stmt, "a variant must be a Nat: it is a count of the "
                            "passes still to come")
        if not same_type(self.type_of_expr(inv_node), BOOL):
            self.fail(stmt, "an invariant must be decidable (Bool)")

        carried = self.assigned(body)
        for name in carried:
            if name not in self.store:
                self.fail(stmt, f"'{name}' is assigned in the loop but has no "
                                f"value going in")
        if not carried:
            self.fail(stmt, "this loop changes nothing, so it either does not "
                            "terminate or does not matter")

        types = [self.types[n] for n in carried]
        acc_type = types[-1]
        for ty in reversed(types[:-1]):
            acc_type = app('Prod', ty, acc_type)

        entry_store = dict(self.store)
        entry_types = dict(self.types)
        init = self.pack([self.store[n] for n in carried], types)

        # The condition, the invariant, the variant and one pass: each named
        # as a function of the state.  The fold is then built from those
        # names, which is what lets the general lemmas -- stated about
        # `ite (b s) (f s) s` -- apply to this particular loop.
        acc = self.fresh('acc')
        for pos, name in enumerate(carried):
            self.store[name] = self.project(Var(acc), types, pos)
        guard = self.expr(stmt.test)
        loop_inv = self.expr(inv_node)
        loop_rank = self.expr(var_node)
        self.block(body)
        advanced = self.pack([self.store[n] for n in carried], types)
        self.store, self.types = dict(entry_store), dict(entry_types)

        named = lambda term, ty, stem: self.name_loop(
            Lambda(acc, acc_type, term), arrow(acc_type, ty), stem=stem)
        cond_fn = named(guard, BOOL, 'cond')
        inv_fn = named(loop_inv, BOOL, 'inv')
        rank_fn = named(loop_rank, NAT, 'rank')
        pass_fn = named(advanced, acc_type, 'pass')

        # the variant at the starting state is the number of passes there can
        # be, which is the whole content of writing one down
        fuel = App(rank_fn, init)
        stepping = Lambda('s', acc_type, App(
            Var('_it'), app('ite', acc_type, App(cond_fn, Var('s')),
                            App(pass_fn, Var('s')), Var('s'))))
        iterate = app('Nat.rec', Lambda('_', NAT, arrow(acc_type, acc_type)),
                      Lambda('s', acc_type, Var('s')),
                      Lambda('_k', NAT, Lambda('_it', arrow(acc_type, acc_type),
                                               stepping)), fuel)
        folded = self.name_loop(App(iterate, init), acc_type)

        # the state the rest of the function sees
        self.bind(carried, types, acc_type, folded)
        exit_store, exit_types = dict(self.store), dict(self.types)

        holds = lambda t: App(Var('Holds'), t)
        sv = Var('s')
        # Two hypotheses rather than one `andb`.  They carry the same content,
        # but a case split on the condition has `Holds true` to hand in the
        # branch where it holds, and `refl` proves that; `Holds (andb I true)`
        # with a symbolic I has nothing to reduce, and the chain stops there.
        running = lambda goal: Pi('s', acc_type, arrow(
            holds(App(inv_fn, sv)), arrow(holds(App(cond_fn, sv)), goal)))
        raw = [
            ('progress', holds(app('notb', App(cond_fn, folded)))),
            ('invariant holds on entry', holds(App(inv_fn, init))),
            ('invariant is preserved',
             running(holds(App(inv_fn, App(pass_fn, sv))))),
            ('variant decreases',
             running(holds(app('ltb', App(rank_fn, App(pass_fn, sv)),
                               App(rank_fn, sv))))),
        ]
        closed, binders = self.close_all([g for _, g in raw], entry_types)
        for (label, _), goal in zip(raw, closed):
            self.obligations.append((label, goal))
        self.shapes.append({'cond': cond_fn, 'pass': pass_fn, 'inv': inv_fn,
                            'rank': rank_fn, 'state': acc_type,
                            'carried': list(carried), 'fuel': fuel,
                            'init': init, 'result': folded,
                            'binders': binders,
                            'assumptions': list(self.assumptions)})
        return None

    def name_loop(self, term, result_type, stem='loop'):
        r"""Give a loop's fold a name, and use the name from then on.

        A fold inlined into a goal is unreadable at any size worth checking:
        `schedule`'s postcondition printed as six hundred characters with the
        same `Nat.rec` in it twice, and a goal nobody can read is a goal
        nobody can tell is the wrong one.  The name is a definition, so it
        unfolds by delta whenever anything needs to compute -- this costs
        nothing but the reader's ability to see what was written.
        """
        if self.env is None:
            return term
        live = [n for n in self.types if n in L.free_names(term)]
        declared, value = result_type, term
        for name in reversed(live):
            declared = Pi(name, self.types[name], declared)
            value = Lambda(name, self.types[name], value)
        base, index = f'{self.where}.{stem}', 1
        while f'{base}{index}' in self.env:
            index += 1
        define(self.env, f'{base}{index}', declared, value)
        return app(f'{base}{index}', *[Var(n) for n in live])

    def close_all(self, goals, types):
        """Close a family of obligations over one shared list of binders.

        Each goal on its own would quantify only what it happens to mention,
        and then the four could not be applied to each other -- which is the
        whole point of stating them. The union, in declaration order, keeps
        them pluggable.
        """
        live = set()
        for goal in goals:
            live |= L.free_names(goal)
        for term in self.assumptions:
            live |= L.free_names(term)
        binders = [(n, types[n]) for n in types if n in live]
        out = []
        for goal in goals:
            for term in reversed(self.assumptions):
                goal = arrow(App(Var('Holds'), term), goal)
            for name, ty in reversed(binders):
                goal = Pi(name, ty, goal)
            out.append(goal)
        return out, binders

    def close(self, goal, types):
        """Quantify over every free name the obligation still mentions."""
        live = L.free_names(goal)
        for name in reversed([n for n in types if n in live]):
            goal = Pi(name, types[name], goal)
        return goal

    def bind(self, carried, types, acc_type, folded):
        """Read the loop-carried variables back out of the fold."""
        if len(carried) == 1:
            self.store[carried[0]] = folded
            return
        whole = self.fresh('loop')
        for pos, name in enumerate(carried):
            self.store[name] = App(
                Lambda(whole, acc_type, self.project(Var(whole), types, pos)),
                folded)

    def pack(self, terms, types):
        """v1, .., vk as a right-nested Prod."""
        out = terms[-1]
        acc_type = types[-1]
        for term, ty in zip(reversed(terms[:-1]), reversed(types[:-1])):
            out = app('mk', ty, acc_type, term, out)
            acc_type = app('Prod', ty, acc_type)
        return out

    def project(self, term, types, pos):
        """The pos'th component out of a right-nested Prod."""
        rest = types[-1]
        tails = [rest]
        for ty in reversed(types[1:-1]):
            rest = app('Prod', ty, rest)
            tails.append(rest)
        tails.reverse()                       # tails[i] = type of components i.. for i>=1
        out = term
        for i in range(pos):
            out = app('snd', types[i], tails[i], out)
        if pos < len(types) - 1:
            out = app('fst', types[pos], tails[pos], out)
        return out


# ------------------------------------------------------- the Hoare triple

class Procedure:
    """A body read as a term, with the contract stated about it."""

    def __init__(self, name, params, result_type, body, requires, ensures,
                 obligation, loop_obligations=()):
        self.name = name
        self.params = params                # [(name, type)]
        self.result_type = result_type
        self.body = body                    # the pure term the body computes
        self.requires = requires            # [Bool term]
        self.ensures = ensures              # [Bool term], `result` substituted
        self.obligation = obligation        # the Pi type to be proved
        self.loop_obligations = list(loop_obligations)   # from while loops

    def __repr__(self):
        return f"<procedure {self.name} : {readable(self.obligation)}>"


def read_procedure(func, env=None, signatures=None, ensures=(),
                   define_as=None, preserves=None):
    r"""Compile a Python function into a term, a contract, and an obligation.

    Leading `assert` statements are the precondition, in the spelling
    `extensions.py` already lifts out of C:

        def calc_sum(ptr: 'Array', n: 'Nat') -> 'Nat':
            assert len(ptr) >= 64
            assert not len(ptr) % 4
            ...
    """
    env = PRELUDE_ENV if env is None else env
    if isinstance(func, str):
        # source text, which is what a compiler pass has to hand rather than
        # a live function object
        source = textwrap.dedent(func)
    else:
        try:
            source = textwrap.dedent(inspect.getsource(func))
        except (OSError, TypeError) as exc:
            raise ContractError(
                f"cannot read the source of "
                f"{getattr(func, '__name__', func)}: a contract must live in "
                f"a file, not an interactive session ({exc})")
    tree = ast.parse(source).body[0]
    if not isinstance(tree, ast.FunctionDef):
        raise ContractError(f"{func.__name__} is not a function definition")

    reader = ImpToLean(where=tree.name, signatures=signatures, env=env)
    args = tree.args.posonlyargs + tree.args.args
    if tree.args.vararg or tree.args.kwarg or tree.args.kwonlyargs:
        raise ContractError(f"{tree.name}: *args and **kwargs have no meaning "
                            f"as a dependent function")
    params = []
    for arg in args:
        if arg.annotation is None:
            raise ContractError(f"{tree.name}: parameter '{arg.arg}' has no "
                                f"type annotation, so there is nothing to "
                                f"check")
        ty = reader.read_type(arg.annotation, f"the annotation on '{arg.arg}'")
        params.append((arg.arg, ty))
        reader.store[arg.arg] = Var(arg.arg)
        reader.types[arg.arg] = ty

    body = [s for s in tree.body
            if not (isinstance(s, ast.Expr) and isinstance(s.value, ast.Constant)
                    and isinstance(s.value.value, str))]
    pre = []
    while body and isinstance(body[0], ast.Assert):
        clause = body[0]
        if not same_type(reader.type_of_expr(clause.test), BOOL):
            reader.fail(clause, "a precondition must be a decidable (Bool) "
                                "expression")
        pre.append(reader.expr(clause.test))
        body = body[1:]
    if any(isinstance(s, ast.Assert) for s in body):
        raise ContractError(f"{tree.name}: a precondition belongs before the "
                            f"body; an assertion in the middle is a different "
                            f"thing and is not supported yet")

    # A procedure that preserves the state invariant may assume it going in,
    # and this has to be settled before the body is read: a loop obligation
    # may legitimately need what the procedure was promised, and `progress`
    # for a scheduler needs exactly that.
    if preserves:
        pre.insert(0, App(Var(f'{preserves}.invariant'), Var(params[0][0])))
    reader.assumptions = list(pre)
    term = reader.block(body)
    if term is None:
        raise ContractError(f"{tree.name}: the body falls off the end without "
                            f"returning")
    result_type = (reader.read_type(tree.returns, 'the return annotation')
                   if tree.returns is not None else NAT)

    # The function is declared before its contract is stated, so that the
    # postcondition can say `schedule(c)` rather than inlining the fold.  It
    # is a definition, so the two are the same term to the kernel and only
    # different to the reader.
    fn_type = result_type
    for name, ty in reversed(params):
        fn_type = Pi(name, ty, fn_type)
    fn_term = term
    for name, ty in reversed(params):
        fn_term = Lambda(name, ty, fn_term)
    actual = type_check(env, fn_term)
    if not L.definitionally_equal(fn_type, actual, env):
        raise ContractError(f"{tree.name}: the body has type "
                            f"{readable(actual)}, not the declared "
                            f"{readable(fn_type)}")
    declared_as, index = define_as or tree.name, 1
    while declared_as in env:
        index += 1
        declared_as = f"{define_as or tree.name}{index}"
    define(env, declared_as, fn_type, fn_term)
    applied = app(declared_as, *[Var(n) for n, _ in params])

    # the postcondition is read in a scope where `result` is that call
    post = []
    for clause in ensures:
        node = ast.parse(clause, mode='eval').body
        saved_store, saved_types = dict(reader.store), dict(reader.types)
        reader.store = {n: Var(n) for n, _ in params}
        reader.types = {n: t for n, t in params}
        reader.store['result'] = applied
        reader.types['result'] = result_type
        if not same_type(reader.type_of_expr(node), BOOL):
            raise ContractError(f"{tree.name}: the postcondition {clause!r} "
                                f"is not decidable (Bool)")
        post.append(reader.expr(node))
        reader.store, reader.types = saved_store, saved_types

    # {P} c {Q}  ==  forall params, Holds P -> ... -> Holds Q.
    # Several postconditions are one Bool joined by `andb`, not several Pis:
    # the conclusion of a triple is a single proposition.
    if not post:
        raise ContractError(f"{tree.name}: no postcondition to prove; pass "
                            f"ensures=[...] to state one")
    conj = post[0]
    for q in post[1:]:
        conj = app('andb', conj, q)
    goal = App(Var('Holds'), conj)
    for p in reversed(pre):
        goal = arrow(App(Var('Holds'), p), goal)
    for name, ty in reversed(params):
        goal = Pi(name, ty, goal)

    type_check(env, goal)

    for label, extra in reader.obligations:
        type_check(env, extra)
    preservation = subject = None
    pass_goals = []
    if preserves:
        if not same_type(result_type, Var(preserves)):
            raise ContractError(f"{tree.name} claims to preserve {preserves} "
                                f"but does not return one")
        preservation, subject = preservation_goal(env, preserves, declared_as,
                                                  params)
        type_check(env, preservation)
        # The loop's own invariant is not the state's.  A while loop inside a
        # syscall raises one more obligation: that a single guarded pass keeps
        # the *state* invariant, which is the hypothesis `loop_preserves`
        # wants and the only thing missing between the loop obligations
        # already stated and the syscall being composable.
        inv = Var(f'{preserves}.invariant')
        hold = lambda x: App(Var('Holds'), x)
        hands_on = lambda g: Pi('s', Var(preserves),
                                arrow(hold(App(inv, Var('s'))),
                                      hold(App(inv, g(Var('s'))))))
        for shape in reader.shapes:
            if not same_type(shape['state'], Var(preserves)):
                continue
            goal = Pi('s', Var(preserves),
                      arrow(hold(App(inv, Var('s'))),
                            arrow(hold(App(shape['cond'], Var('s'))),
                                  hold(App(inv,
                                           App(shape['pass'], Var('s')))))))
            type_check(env, goal)
            # The loop is rarely the whole body.  What runs before it and what
            # runs after are each a function of the state too, and each has to
            # hand the invariant on, or the chain has a hole in it exactly
            # where nobody is looking.  This is the sequence rule, inside one
            # procedure rather than across several.
            def named(body, stem):
                # a segment gets a name for the same reason the loop does:
                # inlined, these goals print as a lambda applied to a variable
                if L.free_names(body) - set(env):
                    return None
                base, index = f'{tree.name}.{stem}', 1
                while f'{base}{index}' in env:
                    index += 1
                define(env, f'{base}{index}',
                       arrow(Var(preserves), Var(preserves)), body)
                return Var(f'{base}{index}')

            identity = Lambda('s', Var(preserves), Var('s'))
            segments = []
            for stem, label, body in (
                    ('before', 'before the loop',
                     Lambda(subject, Var(preserves), shape['init'])),
                    ('after', 'after the loop',
                     Lambda('_s', Var(preserves),
                            replace_subterm(term, shape['result'],
                                            Var('_s'))))):
                if L.definitionally_equal(body, identity, env):
                    continue          # nothing runs there; nothing to prove
                fn = named(body, stem) or body
                goal2 = hands_on(lambda x, fn=fn: App(fn, x))
                type_check(env, goal2)
                segments.append((label, goal2, fn))
                shape[stem] = fn
            shape['segments'] = segments
            pass_goals.append(goal)
    proc = Procedure(tree.name, params, result_type, term, pre, post, goal,
                     reader.obligations)
    proc.fn_term, proc.fn_type = fn_term, fn_type
    SIGNATURES[declared_as] = ([ty for _, ty in params], result_type)
    proc.declared_as = declared_as
    proc.preserves = preserves
    proc.preservation = preservation
    proc.preservation_subject = subject
    proc.pass_goals = pass_goals
    proc.shapes = list(reader.shapes)
    return proc


def procedure(env=None, ensures=(), signatures=None, verbose=True,
              define_as=None, preserves=None):
    r"""Read a Python body as a term and state its contract as a proposition.

        @procedure(ensures=['result == add(n, n)'])
        def double(n: 'Nat') -> 'Nat':
            v = 0
            for i in range(2):
                v = v + n
            return v

    The decorated function keeps working as ordinary Python.  What it gains is
    `.lean_obligation`, the Pi type a proof must inhabit.
    """
    def decorator(func):
        scope = PRELUDE_ENV if env is None else env
        proc = read_procedure(func, scope, signatures, ensures, define_as,
                              preserves)
        func.lean_procedure = proc
        func.lean_term = proc.body
        func.lean_obligation = proc.obligation
        if verbose:
            print(f"read {proc.declared_as} : {readable(proc.fn_type)}")
            print(f"  obligation: {readable(proc.obligation)}")
            for label, extra in proc.loop_obligations:
                print(f"  loop obligation ({label}): {readable(extra)}")
            if proc.preservation is not None:
                print(f"  preserves: {readable(proc.preservation)}")
            for goal in proc.pass_goals:
                print(f"  one pass keeps it: {readable(goal)}")
            for shape in proc.shapes:
                for label, goal, _ in shape.get('segments', ()):
                    print(f"  {label}: {readable(goal)}")
        return func
    return decorator


def at(proc, *args):
    """The obligation with the parameters given actual values.

    `simd_contracts.py` proves a contract *at each call site*, because that is
    where the argument is known.  This is that, with a kernel proof at the end
    of it instead of a dataflow verdict.
    """
    goal = proc.obligation if isinstance(proc, Procedure) else proc
    for arg in args:
        if not isinstance(goal, Pi):
            raise ContractError("more arguments than the contract quantifies")
        goal = L.instantiate(goal.body, arg)
    return goal


def discharge(proc, env=None, verbose=True):
    r"""Prove an obligation that computes: `refl` is the whole proof.

    A binder is introduced rather than refused.  Some goals are quantified and
    still compute -- `Holds (leb 0 (len parts))` is true whatever `parts` is,
    because `leb 0 n` reduces without looking at `n` -- and refusing those
    would send perfectly settled obligations off for a proof by hand.  What is
    refused is a claim that does not reduce to `true` once the binders are in
    scope, which is the honest boundary: it may still be true, but not for a
    reason computation can see.
    """
    env = PRELUDE_ENV if env is None else env
    goal = proc.obligation if isinstance(proc, Procedure) else proc
    binders, claim = peel(goal)

    head, args = L.spine(claim)
    if not (isinstance(head, Var) and head.name == 'Holds' and args):
        raise ContractError(f"{readable(claim)} is not a Holds(...) claim")
    unknowns = [n for n, _, is_hyp in binders if not is_hyp]
    value = normalize(args[-1], env)
    if value != Var('true'):
        if not unknowns:
            raise TheoremError(f"the contract does not hold: it computes to "
                               f"{readable(value)}, not true")
        raise TheoremError(
            f"the contract is universally quantified over "
            f"{', '.join(unknowns)} and does not compute to true for an "
            f"arbitrary one. Give it a value with at(), or prove it.")

    proof = app('refl', BOOL, Var('true'))
    for name, ty, _ in reversed(binders):
        proof = Lambda(name, ty, proof)
    actual = type_check(env, proof)
    if not L.definitionally_equal(goal, actual, env):
        raise TheoremError(f"proved {readable(actual)}, not {readable(goal)}")
    if verbose:
        note = f" (for any {', '.join(unknowns)})" if unknowns else ""
        print(f"  proved by computation{note}")
    return proof


def prove(goal, term, env=None, verbose=True):
    """Discharge an obligation with a proof term, checked by the kernel."""
    env = PRELUDE_ENV if env is None else env
    if L.has_meta(term):
        checked, actual = L.elaborate(env, term, goal)
        type_check(env, checked)
    else:
        # a term whose implicit arguments are all written out has nothing for
        # the elaborator to solve, and handing it one anyway makes it try to
        # insert a hole where an argument already is
        checked = term
        actual = type_check(env, checked)
    if not L.definitionally_equal(goal, actual, env):
        raise TheoremError(f"proved {readable(actual)}, not {readable(goal)}")
    if verbose:
        print(f"  proved: {readable(goal)}")
    return checked


def loop_body(proc, env=None, which=1):
    """The term a named loop stands for, for when you do want to see it."""
    env = PRELUDE_ENV if env is None else env
    return L.value_of(env, f'{proc.name}.loop{which}')


def array(values, element=None):
    """A concrete list.  Ints become Nat; anything else is taken as a term."""
    element = NAT if element is None else element
    out = app('nil', element)
    for v in reversed(values):
        item = numeral(v) if isinstance(v, int) else v
        out = app('cons', element, item, out)
    return out


def text(value):
    """A byte string, from Python bytes or str."""
    raw = value.encode() if isinstance(value, str) else value
    return array(list(raw))


def texts(values):
    """A list of byte strings: the scheme table, for instance."""
    return array([text(v) for v in values], element=BYTES)


# ------------------------------------------------------- a global invariant

def state_invariant(env, record_name, source, param='c'):
    r"""State once what every syscall must keep true of the kernel context.

        state_invariant(env, 'Context',
                        'c.current <= c.nthreads and c.nthreads <= len(c.queue)')

    This is the seL4 shape: not a property of one operation but of the state,
    with each operation obliged to hand it on.  It is a definition rather than
    something the decorator remembers in Python, so the obligations below are
    about a term the kernel can unfold.
    """
    reader = ImpToLean(where=f'{record_name}.invariant', env=env)
    reader.store[param] = Var(param)
    reader.types[param] = Var(record_name)
    node = ast.parse(source, mode='eval').body
    if not same_type(reader.type_of_expr(node), BOOL):
        raise ContractError("a state invariant must be decidable (Bool)")
    term = reader.expr(node)
    name = f'{record_name}.invariant'
    define(env, name, arrow(Var(record_name), BOOL),
           Lambda(param, Var(record_name), term))
    return Var(name)


def preservation_goal(env, record_name, callee, params):
    """forall c, Holds (I c) -> Holds (I (callee c))."""
    inv = f'{record_name}.invariant'
    if len(params) != 1 or not same_type(params[0][1], Var(record_name)):
        raise ContractError(
            f"a procedure that preserves {record_name} takes exactly one "
            f"argument, the {record_name} it hands on")
    subject = params[0][0]
    goal = Pi(subject, Var(record_name),
              arrow(App(Var('Holds'), App(Var(inv), Var(subject))),
                    App(Var('Holds'),
                        App(Var(inv), App(Var(callee), Var(subject))))))
    return goal, subject


def peel(goal):
    """Split a goal into its binders, in order, saying which are hypotheses.

    A hypothesis is a binder whose type is a `Holds(...)`; anything else binds
    a value.  Keeping them in one ordered list rather than two buckets matters:
    a loop obligation inside a procedure that has a precondition reads
    `forall c, Holds (I c) -> forall s, Holds .. -> ..`, so the two kinds
    genuinely interleave.
    """
    binders, body = [], goal
    while isinstance(body, Pi):
        head, _ = L.spine(body.var_type)
        binders.append((body.var_name, body.var_type,
                        isinstance(head, Var) and head.name == 'Holds'))
        body = L.instantiate(body.body, Var(body.var_name))
    return binders, body


def by_cases(env, record_name, goal, verbose=False, what='this', using=None):
    r"""Prove a goal by splitting on the one constructor of its subject.

    A projection of an update is stuck on a variable -- `Context.current
    (Context.with_ticks c v)` cannot reduce, because until the value is known
    to be built by its constructor there is nothing for iota to fire on.  One
    case split unsticks every projection at once, and what is left is often
    one of the hypotheses already to hand: for a scheduler advancing
    `current`, the goal after a pass is `current + 1 <= nthreads`, and the
    condition going in was `current < nthreads`, which is the same
    proposition, since `ltb a b` is `leb (succ a) b` by definition.

    The subject need not be a record.  A loop carrying two variables carries
    a `Prod`, and that is a one-constructor type too; passing `None` for the
    name splits on whatever the goal quantifies over that can be split.

    `using` supplies a term to try first, for the cases where the goal follows
    from a lemma rather than from something already in scope -- a `n - i`
    variant comes down for an arithmetic reason, not a contextual one.
    """
    binders, _claim = peel(goal)
    subjects = []
    for i, (_, ty, is_hyp) in enumerate(binders):
        if is_hyp:
            continue
        if record_name is not None and not same_type(ty, Var(record_name)):
            continue
        if fields_of(env, ty) is not None:
            subjects.append(i)
    if not subjects:
        raise ContractError(f"{readable(goal)} does not quantify over "
                            f"anything with a single constructor to split on")
    where = subjects[-1]
    subject, subject_type = binders[where][0], binders[where][1]
    if any(not is_hyp for _, _, is_hyp in binders[where + 1:]):
        raise ContractError(f"{readable(goal)} binds a value after the thing "
                            f"it would split on")
    name, constructor, params, fields = fields_of(env, subject_type)
    field_vars = [Var(f'f{i}') for i in range(len(fields))]
    built = app(constructor, *params, *field_vars)

    rest = goal
    for _ in range(where):
        rest = L.instantiate(rest.body, Var(rest.var_name))
    motive = Lambda(subject, subject_type,
                    L.instantiate(rest.body, Var(subject)))
    concrete = L.instantiate(rest.body, built)

    hypotheses, walk = [], concrete
    while isinstance(walk, Pi):
        hypotheses.append(walk.var_type)
        walk = L.instantiate(walk.body, Var('_unused'))
    hyp_vars = [Var(f'_h{i}') for i in range(len(hypotheses))]
    attempts = ([('the lemma given', using(field_vars, hyp_vars))]
                if using else [])
    attempts += [(f'hypothesis {i + 1}', v) for i, v in enumerate(hyp_vars)]

    for how, chosen in attempts:
        case = chosen
        for i in reversed(range(len(hypotheses))):
            case = Lambda(f'_h{i}', hypotheses[i], case)
        for i in reversed(range(len(fields))):
            case = Lambda(f'f{i}', fields[i], case)
        term = Lambda(subject, subject_type,
                      app(f'{name}.ind', *params, motive, case, Var(subject)))
        for bname, ty, _ in reversed(binders[:where]):
            term = Lambda(bname, ty, term)
        try:
            proof = prove(goal, term, env, verbose=False)
            if verbose:
                print(f"  proved by cases on {name}, from {how}")
            return proof
        except KernelError:
            continue
    raise TheoremError(
        f"{what} does not follow from a case split: neither the lemma given "
        f"nor any of the {len(hypotheses)} hypotheses is the goal. Prove "
        f"{readable(goal)} directly and pass it in.")


def hands_on_by_cases(env, record_name, goal, verbose=False, what='this'):
    r"""Prove `forall s, Holds (I s) -> Holds (I (g s))` by one case split.

    A projection of an update is stuck on a variable -- `Context.current
    (Context.with_ticks c v)` cannot reduce, because until `c` is known to be
    built by the constructor there is nothing for iota to fire on.  So even a
    step that plainly leaves a field alone has nothing to compute with.
    `Record.ind` supplies the missing step: one constructor, so one case, and
    inside it every projection fires.  Where the invariant then reads
    identically on both sides, the proof of the case is the hypothesis.
    """
    fields = RECORDS[record_name]
    subject = goal.var_name
    motive = Lambda(subject, Var(record_name),
                    L.instantiate(goal.body, Var(subject)))
    built = app(f'{record_name}.mk',
                *[Var(f'f{i}') for i in range(len(fields))])
    case = Lambda('h', L.instantiate(goal.body, built).var_type, Var('h'))
    for i in reversed(range(len(fields))):
        case = Lambda(f'f{i}', fields[i][1], case)
    term = Lambda(subject, Var(record_name),
                  app(f'{record_name}.ind', motive, case, Var(subject)))
    try:
        return prove(goal, term, env, verbose=verbose)
    except KernelError:
        raise TheoremError(
            f"{what} changes what the {record_name} invariant reads, so the "
            f"hypothesis going in is not a proof of the conclusion coming "
            f"out. It needs a real argument: prove {readable(goal)} and pass "
            f"it in.")


def preserves_by_cases(env, record_name, proc, verbose=True):
    """Prove a syscall hands the invariant on, when it does not touch it."""
    return hands_on_by_cases(env, record_name, proc.preservation,
                             verbose=verbose, what=proc.declared_as)


def pass_by_cases(env, record_name, proc, which=0, verbose=True):
    r"""Prove that one guarded pass keeps the state invariant, by cases.

    Same reason as `preserves_by_cases`: a projection of an update is stuck
    until the record is known to be built by its constructor.  Inside the one
    case, the goal often turns out to be one of the two hypotheses already to
    hand -- for a scheduler advancing `current`, the goal after the pass is
    `current + 1 <= nthreads`, and the loop condition going in was
    `current < nthreads`, which is the same proposition since `ltb a b` is
    `leb (succ a) b` by definition.  Both hypotheses are tried; if neither
    fits, this refuses rather than guessing.
    """
    goal = proc.pass_goals[which]
    fields = RECORDS[record_name]
    inv = Var(f'{record_name}.invariant')
    shape = proc.shapes[which]
    hold = lambda x: App(Var('Holds'), x)
    built = app(f'{record_name}.mk',
                *[Var(f'f{i}') for i in range(len(fields))])
    motive = Lambda('s', Var(record_name),
                    arrow(hold(App(inv, Var('s'))),
                          arrow(hold(App(shape['cond'], Var('s'))),
                                hold(App(inv, App(shape['pass'],
                                                  Var('s')))))))
    problems = []
    for choice in ('the condition', 'the invariant'):
        case = Lambda('h2', hold(App(shape['cond'], built)),
                      Var('h2' if choice == 'the condition' else 'h1'))
        case = Lambda('h1', hold(App(inv, built)), case)
        for i in reversed(range(len(fields))):
            case = Lambda(f'f{i}', fields[i][1], case)
        term = Lambda('s', Var(record_name),
                      app(f'{record_name}.ind', motive, case, Var('s')))
        try:
            proof = prove(goal, term, env, verbose=False)
            if verbose:
                print(f"  one pass keeps the invariant, by {choice}")
            return proof
        except KernelError as exc:
            problems.append(choice)
    raise TheoremError(
        f"one pass of {proc.declared_as}'s loop does not obviously keep the "
        f"{record_name} invariant: neither hypothesis is the goal. Prove "
        f"{readable(goal)} directly and pass it to preserves_by_loop().")


def preserves_by_loop(env, record_name, proc, pass_proof, which=0,
                      before_proof=None, after_proof=None, verbose=True):
    r"""Turn the loop obligations into the syscall's preservation proof.

    `loop_preserves` does the general work -- one guarded pass keeps the
    invariant, so any number of them do.  What is left is the sequence: the
    statements before the loop and the statements after it are each a step of
    their own, and the proof is the three applied in turn, exactly as
    `compose` chains separate procedures.  Where a segment does not touch the
    invariant its proof is found by case split; where it does, pass one in.
    """
    shape = proc.shapes[which]
    subject = proc.preservation_subject
    record = Var(record_name)
    inv = Var(f'{record_name}.invariant')
    supplied = {'before the loop': before_proof, 'after the loop': after_proof}
    segment_proofs = {}
    for label, goal, _fn in shape.get('segments', ()):
        given = supplied.get(label)
        segment_proofs[label] = given if given is not None else (
            hands_on_by_cases(env, record_name, goal, verbose=False,
                              what=f"what runs {label} in "
                                   f"{proc.declared_as}"))

    entered = Var(subject)
    carried = Var('h')
    if 'before the loop' in segment_proofs:
        carried = app(segment_proofs['before the loop'], entered, carried)
        entered = App(shape['before'], entered)
    carried = App(app('loop_preserves', record, inv, shape['pass'],
                      shape['cond'], pass_proof, shape['fuel'], entered),
                  carried)
    entered = shape['result']
    if 'after the loop' in segment_proofs:
        carried = app(segment_proofs['after the loop'], entered, carried)

    term = Lambda(subject, record,
                  Lambda('h', App(Var('Holds'), App(inv, Var(subject))),
                         carried))
    try:
        return prove(proc.preservation, term, env, verbose=verbose)
    except KernelError as exc:
        raise TheoremError(
            f"{proc.declared_as}'s loop proof does not close the gap: {exc}")


def progress_by_loop(env, proc, entry, preserved, decreases, which=0,
                     verbose=True):
    r"""Prove the loop finishes, for every starting state, not just tested ones.

    `progress` says the condition is false once the fold is done, and until
    now it was only ever discharged at a concrete value -- which checks the
    examples and says nothing about the rest.  `fold_terminates` closes that:
    the variant is a bound on how many passes there can be, so running it that
    many times is enough.  What is left here is applying it at this loop's
    invariant, condition, pass and variant, with the three obligations that
    were already being stated as its hypotheses.
    """
    shape = proc.shapes[which]
    binders, assumptions = shape['binders'], shape['assumptions']
    args = [Var(n) for n, _ in binders]
    hypotheses = [f'_p{i}' for i in range(len(assumptions))]
    supply = lambda proof: app(proof, *args, *[Var(h) for h in hypotheses])

    term = app('fold_terminates', shape['state'], shape['inv'], shape['pass'],
               shape['cond'], shape['rank'], supply(preserved),
               supply(decreases), shape['fuel'], shape['init'],
               supply(entry), app('leb_refl', shape['fuel']))
    for name, clause in reversed(list(zip(hypotheses, assumptions))):
        term = Lambda(name, App(Var('Holds'), clause), term)
    for name, ty in reversed(binders):
        term = Lambda(name, ty, term)

    goal = dict(proc.loop_obligations)['progress']
    try:
        return prove(goal, term, env, verbose=verbose)
    except KernelError as exc:
        raise TheoremError(f"the loop is not shown to finish: {exc}")


def compose(env, name, steps, record_name='Context', param='c'):
    r"""Chain syscalls, and chain their preservation proofs with them.

        compose(env, 'boot', [(tick, tick_proof), (note, note_proof)])

    The composite's proof is not a new argument.  If f hands the invariant on
    and g hands it on, then g after f hands it on, and the term that says so
    is just the two proofs applied in turn -- which is the point of stating
    the invariant about the state rather than about an operation.  The kernel
    checks the chain; nothing here is taken on trust.
    """
    inv = f'{record_name}.invariant'
    body = Var(param)
    for proc, _ in steps:
        if len(proc.params) != 1:
            raise ContractError(f"{proc.declared_as} takes more than the "
                                f"context, so it cannot be chained")
        body = App(Var(proc.declared_as), body)
    define(env, name, arrow(Var(record_name), Var(record_name)),
           Lambda(param, Var(record_name), body))

    goal = Pi(param, Var(record_name),
              arrow(App(Var('Holds'), App(Var(inv), Var(param))),
                    App(Var('Holds'),
                        App(Var(inv), App(Var(name), Var(param))))))

    state, carried = Var(param), Var('h')
    for proc, proof in steps:
        carried = App(App(proof, state), carried)
        state = App(Var(proc.declared_as), state)
    term = Lambda(param, Var(record_name),
                  Lambda('h', App(Var('Holds'), App(Var(inv), Var(param))),
                         carried))
    checked = prove(goal, term, env, verbose=False)
    return Var(name), goal, checked


# --------------------------------------------- the bridge to crust contracts

def from_crust(bounds, param='ptr'):
    r"""Turn `extensions.py`'s parsed bounds into one Bool term.

    `shivyc/extensions.py` already reduces

        assert len(ptr) >= 64
        assert not len(ptr) % 4

    to {'ptr': {'len>=': 64, 'div-by': 4}}, which four whole-program passes
    then consume.  The same dict reads as a proposition, which is what lets a
    pass that *omits* a check say what it proved to do so.
    """
    clauses = []
    length = app('len', NAT, Var(param))
    for key, value in sorted(bounds.items()):
        if key == 'len>=':
            clauses.append(app('leb', numeral(value), length))
        elif key == 'len<=':
            clauses.append(app('leb', length, numeral(value)))
        elif key == 'div-by':
            clauses.append(app('dvdb', numeral(value), length))
        else:
            raise ContractError(f"unknown contract bound {key!r}")
    if not clauses:
        raise ContractError("no bounds to translate")
    out = clauses[0]
    for c in clauses[1:]:
        out = app('andb', out, c)
    return out


# ------------------------------------------------------------------ self test

def selftest():
    """Every claim this module makes, checked."""
    checks = [0, 0]

    def ok(label, condition):
        checks[0] += 1
        if condition:
            checks[1] += 1
        else:
            print(f"  FAILED: {label}")

    def computes(label, term, expected):
        ok(label, normalize(term, PRELUDE_ENV) == expected)

    def refuses(label, thunk, fragment):
        checks[0] += 1
        try:
            thunk()
        except (ContractError, KernelError, TheoremError) as exc:
            if fragment in str(exc):
                checks[1] += 1
            else:
                print(f"  FAILED: {label}: refused, but for the wrong reason:"
                      f" {exc}")
            return
        print(f"  FAILED: {label}: accepted something it should refuse")

    T, F = Var('true'), Var('false')

    # -- the prelude computes ----------------------------------------------
    computes("ite true", app('ite', NAT, T, numeral(1), numeral(2)), numeral(1))
    computes("ite false", app('ite', NAT, F, numeral(1), numeral(2)), numeral(2))
    computes("notb", app('notb', T), F)
    computes("andb", app('andb', T, F), F)
    computes("orb", app('orb', F, T), T)
    computes("mul", app('mul', numeral(3), numeral(4)), numeral(12))
    computes("sub", app('sub', numeral(7), numeral(3)), numeral(4))
    computes("sub below zero", app('sub', numeral(3), numeral(7)), numeral(0))
    computes("pred", app('pred', numeral(5)), numeral(4))
    computes("leb yes", app('leb', numeral(3), numeral(3)), T)
    computes("leb no", app('leb', numeral(4), numeral(3)), F)
    computes("ltb", app('ltb', numeral(3), numeral(3)), F)
    computes("eqb yes", app('eqb', numeral(9), numeral(9)), T)
    computes("eqb no", app('eqb', numeral(9), numeral(8)), F)
    computes("modb", app('modb', numeral(14), numeral(4)), numeral(2))
    computes("modb exact", app('modb', numeral(16), numeral(4)), numeral(0))
    computes("dvdb yes", app('dvdb', numeral(4), numeral(64)), T)
    computes("dvdb no", app('dvdb', numeral(4), numeral(70)), F)
    computes("len", app('len', NAT, array([5, 6, 7])), numeral(3))
    computes("nth", app('nth', NAT, numeral(0), array([5, 6, 7]), numeral(1)),
             numeral(6))
    computes("nth past the end reads the default",
             app('nth', NAT, numeral(0), array([5, 6, 7]), numeral(9)),
             numeral(0))
    pair = app('mk', NAT, NAT, numeral(1), numeral(2))
    computes("fst", app('fst', NAT, NAT, pair), numeral(1))
    computes("snd", app('snd', NAT, NAT, pair), numeral(2))

    # the scale the SIMD contracts are actually written at
    computes("len >= 64", app('leb', numeral(64), numeral(64)), T)
    computes("len >= 64, violated", app('leb', numeral(64), numeral(63)), F)

    # -- the fragment lowers ------------------------------------------------
    env = prelude()

    @procedure(env=env, ensures=['result == add(n, n)'], verbose=False)
    def double(n: 'Nat') -> 'Nat':
        v = 0
        for i in range(2):
            v = v + n
        return v
    ok("a loop lowers to Nat.rec",
       'Nat.rec' in readable(loop_body(double.lean_procedure, env)))
    ok("and the body refers to it by name",
       'double.loop1' in readable(double.lean_procedure.body))
    ok("double 5 = 10",
       normalize(App(double.lean_procedure.fn_term, numeral(5)), env)
       == numeral(10))

    @procedure(env=env, ensures=['result == 7'], verbose=False)
    def branchy(a: 'Nat') -> 'Nat':
        if a < 3:
            r = 7
        else:
            r = 7
        return r
    ok("a branch lowers to ite", 'ite' in readable(branchy.lean_procedure.body))
    ok("branchy 1 = 7",
       normalize(App(branchy.lean_procedure.fn_term, numeral(1)), env)
       == numeral(7))
    ok("branchy 9 = 7",
       normalize(App(branchy.lean_procedure.fn_term, numeral(9)), env)
       == numeral(7))

    @procedure(env=env, ensures=['result == 10'], verbose=False)
    def two_carried() -> 'Nat':
        s = 0
        c = 0
        for i in range(5):
            s = s + i
            c = c + 1
        return s
    ok("two loop-carried variables use a Prod",
       'mk' in readable(loop_body(two_carried.lean_procedure, env)))
    ok("0+1+2+3+4 = 10", discharge(two_carried.lean_procedure, env,
                                   verbose=False) is not None)

    @procedure(env=env, ensures=['result == 6'], verbose=False)
    def augmented(n: 'Nat') -> 'Nat':
        v = n
        v += 1
        v = v * 2
        return v
    ok("augmented assignment",
       normalize(App(augmented.lean_procedure.fn_term, numeral(2)), env)
       == numeral(6))

    # -- the contract, in crust's spelling ----------------------------------
    @procedure(env=env, ensures=['result == 128'], verbose=False)
    def calc_sum(ptr: 'Array') -> 'Nat':
        assert len(ptr) >= 64
        assert not len(ptr) % 4
        v = 0
        for i in range(len(ptr)):
            v = v + ptr[i]
        return v
    goal = calc_sum.lean_procedure.obligation
    ok("the obligation quantifies the parameter", isinstance(goal, Pi))
    ok("both preconditions are in it",
       readable(goal).count('Holds') == 3)
    ok("proven at a 64-element call site",
       discharge(at(calc_sum.lean_procedure, array([2] * 64)), env,
                 verbose=False) is not None)
    refuses("refused at a 70-element call site",
            lambda: discharge(at(calc_sum.lean_procedure, array([2] * 70)),
                              env, verbose=False),
            "does not hold")

    # -- a contract that needs induction ------------------------------------
    @procedure(env=env, ensures=['result == n'], verbose=False)
    def count(n: 'Nat') -> 'Nat':
        v = 0
        for i in range(n):
            v = v + 1
        return v
    refuses("a quantified obligation does not compute",
            lambda: discharge(count.lean_procedure, env, verbose=False),
            "universally quantified")
    motive = Lambda('n', NAT, App(Var('Holds'),
                                  app('eqb', app('count', Var('n')), Var('n'))))
    proof = Lambda('n', NAT, app(
        'Nat.ind', motive, app('refl', BOOL, Var('true')),
        Lambda('k', NAT, Lambda('ih', App(motive, Var('k')), Var('ih'))),
        Var('n')))
    ok("proved for every n by induction",
       prove(count.lean_procedure.obligation, proof, env, verbose=False)
       is not None)
    refuses("a wrong proof is rejected",
            lambda: prove(count.lean_procedure.obligation,
                          Lambda('n', NAT, Var('n')), env, verbose=False),
            "")

    # -- the refusals, which are the deliverable ----------------------------
    def read(src, **kw):
        return read_procedure(src, env, None,
                              kw.get('ensures', ['result == 0']),
                              preserves=kw.get('preserves'))

    refuses("return inside a loop is refused", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            v = 0
            for i in range(n):
                return i
            return v
        '''), "no way to stop early")
    refuses("return inside a branch is refused", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            if n < 2:
                return 1
            return 0
        '''), "which branch ran")
    refuses("an unbounded iterable is refused", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            v = 0
            for i in n:
                v = v + 1
            return v
        '''), "range(n)")
    refuses("an unannotated parameter is refused", lambda: read('''
        def f(n) -> 'Nat':
            return n
        '''), "no type annotation")
    refuses("a variable assigned in one branch only", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            if n < 2:
                r = 1
            return r
        '''), "only one branch")
    refuses("a variable changing type", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            v = 0
            v = n < 2
            return v
        '''), "keeps one type")
    refuses("reading an unbound variable", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            return q
        '''), "read before it is bound")
    refuses("a loop with nothing carried", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            for i in range(n):
                pass
            return 0
        '''), "no meaning as a fold")
    refuses("a body that never returns", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            v = 0
        '''), "falls off the end")
    refuses("an undeclared call", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            return mystery(n)
        '''), "not a function this fragment knows")
    refuses("division, which the prelude has no definition for", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            return n / 2
        '''), "no meaning in this fragment")
    refuses("a postcondition that is not decidable", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            return n
        ''', ensures=['n']), "not decidable")

    # -- records ------------------------------------------------------------
    ctx = app('Context.mk', array([9, 9]), array([0, 1]), array([3]),
              numeral(1), numeral(2), numeral(7))
    computes("a projection", app('Context.ticks', ctx), numeral(7))
    computes("another projection", app('Context.current', ctx), numeral(1))
    computes("a list-valued field",
             app('len', NAT, app('Context.schemes', ctx)), numeral(1))
    updated = app('Context.with_ticks', ctx, numeral(99))
    computes("an update takes", app('Context.ticks', updated), numeral(99))
    computes("an update leaves the other fields alone",
             app('Context.current', updated), numeral(1))
    computes("and the list fields too",
             app('len', NAT, app('Context.frames', updated)), numeral(2))

    @procedure(env=env, ensures=['result.ticks == add(c.ticks, 1)'],
               verbose=False)
    def tick(c: 'Context') -> 'Context':
        c.ticks = c.ticks + 1
        return c
    ok("a field assignment lowers to with_",
       'Context.with_ticks' in readable(tick.lean_procedure.body))
    ok("a syscall's contract holds at a context",
       discharge(at(tick.lean_procedure, ctx), env, verbose=False) is not None)

    refuses("a field that does not exist", lambda: read("""
        def f(c: 'Context') -> 'Nat':
            return c.nonesuch
        """), "has no field")
    refuses("a field of something that is not a record", lambda: read("""
        def f(n: 'Nat') -> 'Nat':
            return n.ticks
        """), "is not a record")
    refuses("a field assigned the wrong type", lambda: read("""
        def f(c: 'Context') -> 'Context':
            c.ticks = c.frames
            return c
        """, ensures=['result.ticks == 0']), "and this assigns")

    # -- while, now that a variant makes it admissible ----------------------
    @procedure(env=env, ensures=['result.current == result.nthreads'],
               verbose=False)
    def schedule(c: 'Context') -> 'Context':
        while c.current < c.nthreads:
            assert invariant(c.current <= c.nthreads)
            assert variant(c.nthreads - c.current)
            c.current = c.current + 1
            c.ticks = c.ticks + 1
        return c
    inner = readable(loop_body(schedule.lean_procedure, env))
    ok("a while loop lowers to a guarded fold",
       'ite' in inner and 'Nat.rec' in inner)
    ok("the obligation reads in terms of the call, not the fold",
       'Nat.rec' not in readable(schedule.lean_procedure.obligation))
    labels = [label for label, _ in schedule.lean_procedure.loop_obligations]
    ok("it raises all four obligations",
       labels == ['progress', 'invariant holds on entry',
                  'invariant is preserved', 'variant decreases'])
    start = app('Context.mk', array([9, 9, 9]), array([0, 1, 2]), array([]),
                numeral(0), numeral(3), numeral(0))
    ok("the postcondition holds at a context",
       discharge(at(schedule.lean_procedure, start), env, verbose=False)
       is not None)
    for label, goal in schedule.lean_procedure.loop_obligations:
        if label in ('progress', 'invariant holds on entry'):
            ok(f"while: {label} (at a context)",
               discharge(L.instantiate(goal.body, start), env, verbose=False)
               is not None)
        else:
            # now stated for every state, so a value proves nothing about it
            ok(f"while: {label} (for every state)",
               by_cases(env, 'Context', goal, what=label,
                        using=lambda f, h: app('sub_lt', f[4], f[3], h[1]))
               is not None)
    ok("the loop really ran",
       normalize(app('Context.ticks', L.instantiate(
           L.abstract(schedule.lean_procedure.body, 'c'), start)), env)
       == numeral(3))

    @procedure(env=env, ensures=['result.current == result.nthreads'],
               verbose=False)
    def stuck(c: 'Context') -> 'Context':
        while c.current < c.nthreads:
            assert invariant(c.current <= c.nthreads)
            assert variant(c.nthreads)
            c.ticks = c.ticks + 1
        return c
    raised = dict(stuck.lean_procedure.loop_obligations)
    refuses("a constant variant fails to decrease",
            lambda: by_cases(env, 'Context', raised['variant decreases'],
                             what='the variant'),
            "does not follow from a case split")
    refuses("and the loop is caught not finishing",
            lambda: discharge(L.instantiate(raised['progress'].body, start),
                              env, verbose=False),
            "does not hold")

    refuses("while without a variant is still refused", lambda: read("""
        def f(n: 'Nat') -> 'Nat':
            v = 0
            while v < n:
                v = v + 1
            return v
        """), "needs a variant to be admissible")
    refuses("while without an invariant is refused", lambda: read("""
        def f(n: 'Nat') -> 'Nat':
            v = 0
            while v < n:
                assert variant(n - v)
                v = v + 1
            return v
        """), "needs `assert invariant")
    refuses("a variant that is not a Nat", lambda: read("""
        def f(n: 'Nat') -> 'Nat':
            v = 0
            while v < n:
                assert invariant(v <= n)
                assert variant(v < n)
                v = v + 1
            return v
        """), "a variant must be a Nat")

    # -- byte strings -------------------------------------------------------
    url = text("file:/etc/passwd")
    computes("find a separator", app('find', url, numeral(58)), numeral(4))
    computes("find, when absent, gives the length",
             app('find', text("abc"), numeral(58)), numeral(3))
    computes("take", app('take', url, numeral(4)), text("file"))
    computes("drop", app('drop', url, numeral(5)), text("/etc/passwd"))
    computes("string equality", app('eqs', text("file"), text("file")), T)
    computes("string inequality", app('eqs', text("file"), text("pipe")), F)
    computes("and on a prefix, which is not equality",
             app('eqs', text("fil"), text("file")), F)
    parts = app('split', text("a,bb,ccc"), numeral(44))
    computes("split counts the segments",
             app('len', BYTES, parts), numeral(3))
    computes("split keeps the first",
             app('nth', BYTES, app('nil', NAT), parts, numeral(0)),
             text("a"))
    computes("split keeps the last",
             app('nth', BYTES, app('nil', NAT), parts, numeral(2)),
             text("ccc"))
    computes("splitting nothing still gives one segment",
             app('len', BYTES, app('split', text(""), numeral(44))),
             numeral(1))

    # -- building a list in order -------------------------------------------
    computes("append", app('append', NAT, array([1, 2]), array([3])),
             array([1, 2, 3]))
    computes("snoc puts it on the end",
             app('snoc', NAT, array([1, 2]), numeral(3)), array([1, 2, 3]))
    computes("rev", app('rev', NAT, array([1, 2, 3])), array([3, 2, 1]))

    @procedure(env=env, ensures=['len(result) == n'], verbose=False)
    def upto(n: 'Nat') -> 'Array':
        out: 'Array' = []
        for i in range(n):
            out = snoc(out, i)
        return out
    ok("a loop can build a list in order",
       normalize(App(upto.lean_procedure.fn_term, numeral(4)), env)
       == array([0, 1, 2, 3]))
    refuses("an empty literal with no annotation is refused", lambda: read("""
        def f(n: 'Nat') -> 'Nat':
            out = []
            return n
        """), "needs an annotation")

    # -- crustos/schemes.py, with its own routing ---------------------------
    names = texts(["sys", "memory", "file", "pipe", "irq", "debug", "gpu"])

    @procedure(env=env, ensures=['result <= len(names)'], verbose=False)
    def scheme_of(names: 'Strs', url: 'Bytes') -> 'Nat':
        idx = find(url, 58)                  # ord(':')
        head = take(url, idx)
        i = 0
        found = len(names)                   # stands in for SCHEME_NONE
        while i < len(names):
            assert invariant(i <= len(names))
            assert variant(len(names) - i)
            if eqs(names[i], head) and found == len(names):
                found = i
            i = i + 1
        return found

    @procedure(env=env, ensures=['len(result) <= len(url)'], verbose=False)
    def path_of(url: 'Bytes') -> 'Bytes':
        idx = find(url, 58)
        if idx < len(url):
            out = drop(url, idx + 1)
        else:
            out = url                        # no colon: the whole thing
        return out

    def routed(u):
        return normalize(app('scheme_of', names, text(u)), env)
    ok("sys: routes to 0", routed("sys:boot") == numeral(0))
    ok("file: routes to 2", routed("file:/etc/passwd") == numeral(2))
    ok("gpu: routes to 6", routed("gpu:0") == numeral(6))
    ok("an unregistered scheme gets the sentinel",
       routed("nope:/x") == numeral(7))
    ok("so does a url with no scheme at all",
       routed("/etc/passwd") == numeral(7))
    ok("a prefix of a scheme name does not route",
       routed("fil:/x") == numeral(7))
    ok("the index never leaves the scheme table",
       discharge(at(scheme_of.lean_procedure, names, text("nope:/x")), env,
                 verbose=False) is not None)
    ok("path_of strips the scheme",
       normalize(app('path_of', text("file:/etc/passwd")), env)
       == text("/etc/passwd"))
    ok("and keeps a url that has none",
       normalize(app('path_of', text("/etc/passwd")), env)
       == text("/etc/passwd"))
    ok("the path never grows",
       discharge(at(path_of.lean_procedure, text("file:/etc/passwd")), env,
                 verbose=False) is not None)

    # -- the other two public functions of schemes.py -----------------------
    @procedure(env=env, verbose=False,
               ensures=['len(result) == len(split(urls, 44))'])
    def route_all(names: 'Strs', urls: 'Bytes') -> 'Array':
        parts = split(urls, 44)              # ord(',')
        out: 'Array' = []
        for i in range(len(parts)):
            out = snoc(out, scheme_of(names, parts[i]))
        return out

    @procedure(env=env, verbose=False,
               ensures=['len(result) <= len(split(urls, 44))'])
    def accepted(names: 'Strs', urls: 'Bytes') -> 'Array':
        parts = split(urls, 44)
        out: 'Array' = []
        i = 0
        while i < len(parts):
            assert invariant(i <= len(parts))
            assert variant(len(parts) - i)
            if scheme_of(names, parts[i]) < len(names):
                out = snoc(out, i)
            i = i + 1
        return out

    batch = text("sys:boot,nope:/x,file:/etc/passwd,gpu:0")
    ok("route_all keeps the order",
       normalize(app('route_all', names, batch), env) == array([0, 7, 2, 6]))
    ok("one scheme id per url",
       discharge(at(route_all.lean_procedure, names, batch), env,
                 verbose=False) is not None)
    ok("accepted picks out the registered ones",
       normalize(app('accepted', names, batch), env) == array([0, 2, 3]))
    ok("and is never longer than the batch",
       discharge(at(accepted.lean_procedure, names, batch), env,
                 verbose=False) is not None)

    # -- accepted's loop carries a Prod, and that splits too ----------------
    ok("a two-variable loop carries a Prod",
       'Prod' in readable(accepted.lean_procedure.shapes[0]['state']))
    acc_goals = dict(accepted.lean_procedure.loop_obligations)
    acc_entry = discharge(acc_goals['invariant holds on entry'], env,
                          verbose=False)
    ok("the entry invariant computes, whatever the input",
       acc_entry is not None)
    acc_kept = by_cases(env, None, acc_goals['invariant is preserved'],
                        what='preservation')
    ok("one pass keeps it, by splitting on the Prod", acc_kept is not None)
    acc_down = by_cases(
        env, None, acc_goals['variant decreases'], what='the variant',
        using=lambda f, h: app('sub_lt',
                               app('len', BYTES,
                                   app('split', Var('urls'), numeral(44))),
                               f[1], h[1]))
    ok("and the variant comes down", acc_down is not None)
    ok("so accepted's loop finishes for every input, not just tested ones",
       progress_by_loop(env, accepted.lean_procedure, acc_entry, acc_kept,
                        acc_down, verbose=False) is not None)

    # -- one invariant, threaded through a sequence of syscalls -------------
    state_invariant(env, 'Context', 'c.current <= c.nthreads')

    @procedure(env=env, preserves='Context', verbose=False,
               ensures=['result.ticks == add(c.ticks, 1)'])
    def tick(c: 'Context') -> 'Context':
        c.ticks = c.ticks + 1
        return c

    @procedure(env=env, preserves='Context', verbose=False,
               ensures=['len(result.queue) == add(len(c.queue), 1)'])
    def enqueue(c: 'Context') -> 'Context':
        c.queue = cons(0, c.queue)
        return c

    ok("preservation is stated as an obligation",
       'Context.invariant' in readable(tick.lean_procedure.preservation))
    tick_proof = preserves_by_cases(env, 'Context', tick.lean_procedure,
                                    verbose=False)
    enqueue_proof = preserves_by_cases(env, 'Context',
                                       enqueue.lean_procedure, verbose=False)
    ok("tick hands the invariant on", tick_proof is not None)
    ok("so does enqueue", enqueue_proof is not None)
    _, chained, _ = compose(env, 'boot',
                            [(tick.lean_procedure, tick_proof),
                             (enqueue.lean_procedure, enqueue_proof),
                             (tick.lean_procedure, tick_proof)])
    ok("and the sequence does, by chaining their proofs",
       'boot' in readable(chained))
    started = app('Context.mk', array([9]), array([0]), array([]),
                  numeral(1), numeral(2), numeral(0))
    booted = normalize(App(Var('boot'), started), env)
    ok("the sequence actually ran",
       normalize(app('Context.ticks', booted), env) == numeral(2))
    ok("all of it",
       normalize(app('len', NAT, app('Context.queue', booted)), env)
       == numeral(2))

    @procedure(env=env, preserves='Context', verbose=False,
               ensures=['result.current == add(c.current, 1)'])
    def advance(c: 'Context') -> 'Context':
        c.current = c.current + 1            # can run past nthreads
        return c
    @procedure(env=env, preserves='Context', verbose=False,
               ensures=['result.current == result.nthreads'])
    def sched(c: 'Context') -> 'Context':
        while c.current < c.nthreads:
            assert invariant(c.current <= c.nthreads)
            assert variant(c.nthreads - c.current)
            c.current = c.current + 1
            c.ticks = c.ticks + 1
        return c
    ok("a while loop raises one more obligation when it preserves state",
       len(sched.lean_procedure.pass_goals) == 1)
    one_pass = pass_by_cases(env, 'Context', sched.lean_procedure,
                             verbose=False)
    ok("one guarded pass keeps the state invariant", one_pass is not None)
    sched_proof = preserves_by_loop(env, 'Context', sched.lean_procedure,
                                    one_pass, verbose=False)
    ok("and so the whole loop does, by loop_preserves",
       sched_proof is not None)
    _, with_loop, _ = compose(env, 'run',
                              [(tick.lean_procedure, tick_proof),
                               (sched.lean_procedure, sched_proof),
                               (tick.lean_procedure, tick_proof)])
    ok("a while-containing syscall composes with the rest",
       'run' in readable(with_loop))
    ran = normalize(App(Var('run'), started), env)
    ok("the scheduler ran to the end",
       normalize(app('Context.current', ran), env) == numeral(2))
    ok("and the ticks add up",
       normalize(app('Context.ticks', ran), env) == numeral(3))

    ok("a loop that is the whole body raises no segment obligations",
       sched.lean_procedure.shapes[0].get('segments') == [])

    # -- termination, for every starting state rather than tested ones ------
    goals = dict(sched.lean_procedure.loop_obligations)
    ok("progress is stated about the loop, not about a value",
       'sched.loop1' in readable(goals['progress']))
    entry_pf = by_cases(env, 'Context', goals['invariant holds on entry'],
                        what='entry')
    kept_pf = by_cases(env, 'Context', goals['invariant is preserved'],
                       what='preservation')
    down_pf = by_cases(env, 'Context', goals['variant decreases'],
                       what='the variant',
                       using=lambda f, h: app('sub_lt', f[4], f[3], h[1]))
    ok("the invariant holds going in", entry_pf is not None)
    ok("one pass keeps the loop invariant", kept_pf is not None)
    ok("the variant comes down, by sub_lt", down_pf is not None)
    ok("and so the loop finishes, for every context",
       progress_by_loop(env, sched.lean_procedure, entry_pf, kept_pf, down_pf,
                        verbose=False) is not None)

    # the arithmetic the variant proof rests on, checked on its own
    computes("sub still computes", app('sub', numeral(7), numeral(3)),
             numeral(4))
    computes("and saturates", app('sub', numeral(3), numeral(7)), numeral(0))
    ok("sub_le : subtracting never grows a number",
       type_check(env, app('sub_le', numeral(5), numeral(2))) is not None)
    ok("sub_lt : n - (c+1) < n - c when c < n",
       type_check(env, app('sub_lt', numeral(5), numeral(2),
                           app('refl', BOOL, Var('true')))) is not None)
    ok("absurd : anything follows from Holds false",
       'Holds(false)' in readable(L.type_of(env, 'absurd')))
    ok("leb_trans is available", L.type_of(env, 'leb_trans') is not None)

    # -- the sequence rule: statements on both sides of a loop --------------
    @procedure(env=env, preserves='Context', verbose=False,
               ensures=['result.current == result.nthreads'])
    def bootseq(c: 'Context') -> 'Context':
        c.ticks = c.ticks + 1                   # before
        while c.current < c.nthreads:
            assert invariant(c.current <= c.nthreads)
            assert variant(c.nthreads - c.current)
            c.current = c.current + 1
            c.ticks = c.ticks + 1
        c.queue = cons(0, c.queue)              # after
        c.ticks = c.ticks + 1
        return c
    labels = [lab for lab, _, _ in bootseq.lean_procedure.shapes[0]['segments']]
    ok("both segments are raised as obligations",
       labels == ['before the loop', 'after the loop'])
    ok("and they are named, not inlined",
       'bootseq.before1' in readable(
           bootseq.lean_procedure.shapes[0]['segments'][0][1]))
    seq_step = pass_by_cases(env, 'Context', bootseq.lean_procedure,
                             verbose=False)
    seq_proof = preserves_by_loop(env, 'Context', bootseq.lean_procedure,
                                  seq_step, verbose=False)
    ok("prefix, loop and suffix chain into one preservation proof",
       seq_proof is not None)
    # started is current=1 nthreads=2: one tick before, one pass, one after
    ok("the whole thing runs",
       normalize(app('Context.ticks',
                     App(Var('bootseq'), started)), env) == numeral(3))
    ok("and the loop reached the end",
       normalize(app('Context.current',
                     App(Var('bootseq'), started)), env) == numeral(2))
    ok("and the suffix ran",
       normalize(app('len', NAT, app('Context.queue',
                     App(Var('bootseq'), started))), env) == numeral(2))
    ok("and it composes with the rest",
       compose(env, 'session',
               [(tick.lean_procedure, tick_proof),
                (bootseq.lean_procedure, seq_proof)])[1] is not None)

    @procedure(env=env, preserves='Context', verbose=False,
               ensures=['result.nthreads == c.nthreads'])
    def bad_suffix(c: 'Context') -> 'Context':
        while c.current < c.nthreads:
            assert invariant(c.current <= c.nthreads)
            assert variant(c.nthreads - c.current)
            c.current = c.current + 1
        c.current = c.current + 1           # runs past nthreads, after it
        return c
    bad_step = pass_by_cases(env, 'Context', bad_suffix.lean_procedure,
                             verbose=False)
    refuses("a suffix that breaks the invariant is refused",
            lambda: preserves_by_loop(env, 'Context',
                                      bad_suffix.lean_procedure, bad_step,
                                      verbose=False),
            "what runs after the loop in bad_suffix")

    @procedure(env=env, preserves='Context', verbose=False,
               ensures=['result.ticks == result.ticks'])
    def runaway(c: 'Context') -> 'Context':
        while c.ticks < c.nthreads:
            assert invariant(c.ticks <= c.nthreads)
            assert variant(c.nthreads - c.ticks)
            c.current = c.current + 1        # breaks current <= nthreads
            c.ticks = c.ticks + 1
        return c
    refuses("a loop that breaks the state invariant is refused",
            lambda: pass_by_cases(env, 'Context', runaway.lean_procedure,
                                  verbose=False),
            "neither hypothesis is the goal")

    refuses("a syscall that can break the invariant is refused",
            lambda: preserves_by_cases(env, 'Context',
                                       advance.lean_procedure, verbose=False),
            "changes what the Context invariant reads")
    refuses("and one that does not return a context", lambda: read("""
        def f(c: 'Context') -> 'Nat':
            return c.ticks
        """, preserves='Context'), "does not return one")

    # -- the bridge to crust ------------------------------------------------
    prop = from_crust({'len>=': 64, 'div-by': 4}, 'ptr')
    closed = L.instantiate(L.abstract(prop, 'ptr'), array([2] * 64))
    ok("crust bounds hold at a 64-element buffer",
       normalize(closed, PRELUDE_ENV) == T)
    closed = L.instantiate(L.abstract(prop, 'ptr'), array([2] * 70))
    ok("crust bounds fail at a 70-element buffer",
       normalize(closed, PRELUDE_ENV) == F)
    refuses("an unknown bound is refused",
            lambda: from_crust({'align': 16}, 'ptr'), "unknown contract bound")

    print(f"{checks[0]} checks, "
          f"{'all passed' if checks[0] == checks[1] else f'{checks[0]-checks[1]} FAILED'}")
    return checks[0] == checks[1]


if __name__ == '__main__':
    import threading
    sys.setrecursionlimit(300000)
    threading.stack_size(512 * 1024 * 1024)
    result = []
    thread = threading.Thread(target=lambda: result.append(selftest()))
    thread.start()
    thread.join()
    sys.exit(0 if result and result[0] else 1)
