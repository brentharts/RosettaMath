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

import copy
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
INT = Var('Int')
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


# ---------------------------------------------- literals that compute fast

def read_numeral(term):
    """A term as a Python int, if it is a numeral in normal form."""
    if isinstance(term, L.NatLit):
        return term.value
    count = 0
    while isinstance(term, App):
        head = term.func
        if not (isinstance(head, Var) and head.name == 'succ'):
            return None
        count += 1
        term = term.arg
        if count > 1_000_000:
            return None
    return count if isinstance(term, Var) and term.name == 'zero' else None


def as_term(value):
    """A Python answer, back as a term: a literal, one node however large --
    so an accelerated `mul` does not hand back a result the size of its
    value."""
    if isinstance(value, bool):
        return Var('true') if value else Var('false')
    return L.numeral(value)


# A literal larger than this, beside a symbolic argument, leaves an
# accelerated definition folded (see `accelerate`).  The same budget as the
# compiler's CRUST_PROOF_MAX: below it, unfolding a numeral is merely slow.
UNFOLD_LITERAL_LIMIT = 1 << 16


def accelerate(env, name, arity, compute):
    r"""Let a definition on literals be settled by arithmetic, not by unfolding.

    `Nat` is unary, so `leb 64 n` walks n of them and rebuilds a term at every
    step: about a second at 64 and half a minute at 1024.  That is fine for a
    proof and useless to a compiler, which wants the same question answered at
    a buffer length.

    So the *definition* stays exactly as it was -- every proof by induction
    below still unfolds it and still works -- and a computation rule is
    attached that fires only when the arguments have already reduced to
    numerals.  Anything else falls through to ordinary delta, so a symbolic
    argument behaves as it always did.

    This is a real extension of the trusted base: `compute` is Python, and the
    kernel takes its word.  Lean does the same for `Nat` and for the same
    reason.  What keeps it honest is that the accelerated answer and the
    defined answer are checked against each other over a grid, in `selftest`
    below -- an accelerator that disagreed with its definition would make the
    kernel unsound, so it is not something to take on trust either.
    """
    decl = L.as_decl(name, env[name])
    value = decl.value

    # The declaration keeps its body but stops offering it as a `value`.
    # `normalize` unfolds a value the moment it meets the bare name, so a
    # definition that carries one never reaches `reduce_head` with its
    # arguments in hand and a computation rule on it can never fire.  Driving
    # delta from the rule instead means the whole application is seen at once,
    # which is the only place the arguments can be looked at.
    def rule(_env, args):
        if len(args) < arity:
            # Stuck on purpose.  Unfolding here would hand back a lambda, the
            # caller would beta-reduce it, and the full application -- the only
            # place the arguments are all visible -- would never be looked at.
            return None
        literals = [read_numeral(a) for a in args[:arity]]
        if all(x is not None for x in literals):
            out = as_term(compute(*literals))
        elif any(x is not None and x > UNFOLD_LITERAL_LIMIT
                 for x in literals):
            # `sub 18446744073709551615 used`: one side a literal, the other
            # symbolic, so there is nothing to compute -- and unfolding would
            # walk the literal down one `succ` at a time under the step
            # function, 2^64 of them, which is how `u64::MAX` in a guard
            # first met the kernel.  Left folded, the term is still itself:
            # two copies of it are equal, and a split on it is a split.
            # Reducing less can only refuse a true statement, never admit a
            # false one.
            return None
        else:
            out = value                 # not literals: unfold as usual
            for extra in args[:arity]:
                out = App(out, extra)
        for extra in args[arity:]:
            out = App(out, extra)
        return out

    env[name] = L.Decl(name, decl.type, value=None, rule=rule,
                       kind=decl.kind)


ACCELERATED = {
    'add': (2, lambda a, b: a + b),
    'mul': (2, lambda a, b: a * b),
    'sub': (2, lambda a, b: a - b if a > b else 0),
    'pred': (1, lambda a: a - 1 if a else 0),
    'leb': (2, lambda a, b: a <= b),
    'ltb': (2, lambda a, b: a < b),
    'eqb': (2, lambda a, b: a == b),
    # modb n 0 is n: the definition counts up and never reaches a zero
    # divisor to reset at, and an accelerator has to say the same thing
    'modb': (2, lambda a, b: a % b if b else a),
    # divb n 0 is 0: the counter never reaches a zero divisor to increment at
    'divb': (2, lambda a, b: a // b if b else 0),
    'dvdb': (2, lambda k, n: (n % k == 0) if k else n == 0),
}


def _abstract_over(term, bindings):
    for name, ty in bindings:
        term = Lambda(name, ty, term)
    return term


def prelude(env=None, fast=True):
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
    # -- division, as the counter modb already keeps ------------------------
    # div 0 k = 0;  div (p+1) k = if mod p k + 1 = k then div p k + 1 else
    # div p k.  The same structural recursion as modb, incrementing where
    # modb resets, so division needs no well-founded recursion either.
    # `div n 0` is 0, which is Lean's own convention for `Nat.div`.
    define(env, 'divb', arrow(NAT, arrow(NAT, NAT)),
           Lambda('n', NAT, Lambda('k', NAT,
                  rec(NAT, NAT, numeral(0),
                      Lambda('p', NAT, Lambda('ih', NAT,
                             app('ite', NAT,
                                 app('eqb',
                                     App(Var('succ'),
                                         app('modb', Var('p'), Var('k'))),
                                     Var('k')),
                                 App(Var('succ'), Var('ih')),
                                 Var('ih')))),
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

    if fast:
        for name, (arity, compute) in ACCELERATED.items():
            accelerate(env, name, arity, compute)

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

    # Symmetry, by transport along the equation into `Eq c a`.
    define(env, 'eq_symm',
           Pi('A', TYPE0, Pi('a', Var('A'), Pi('b', Var('A'),
              arrow(app('Eq', Var('A'), Var('a'), Var('b')),
                    app('Eq', Var('A'), Var('b'), Var('a')))))),
           Lambda('A', TYPE0, Lambda('a', Var('A'), Lambda('b', Var('A'),
               Lambda('h', app('Eq', Var('A'), Var('a'), Var('b')), app(
                   'Eq.ind', Var('A'), Var('a'),
                   Lambda('c', Var('A'), Lambda(
                       '_t', app('Eq', Var('A'), Var('a'), Var('c')),
                       app('Eq', Var('A'), Var('c'), Var('a')))),
                   app('refl', Var('A'), Var('a')), Var('b'), Var('h')))))))
    # `Holds a -> Holds (orb a b)`: rewrite `a` to `true` in the goal, where
    # `orb true b` computes.  The one place a loop proof needs an equation
    # rather than a case split: the hypothesis is about a variable and the
    # goal is about a term built from it.
    define(env, 'holds_orb_left',
           Pi('a', BOOL, Pi('b', BOOL, arrow(holds(Var('a')),
                                             holds(app('orb', Var('a'), Var('b')))))),
           Lambda('a', BOOL, Lambda('b', BOOL, Lambda('h', holds(Var('a')), app(
               'Eq.ind', BOOL, Var('true'),
               Lambda('c', BOOL, Lambda('_t', app('Eq', BOOL, Var('true'), Var('c')),
                                          holds(app('orb', Var('c'), Var('b'))))),
               yes, Var('a'),
               app('eq_symm', BOOL, Var('a'), Var('true'), Var('h')))))))

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

    # taking a conjunction apart and putting one together.  `Holds (andb x y)`
    # does not reduce on a symbolic x, so both directions need a case split.
    xb, yb = Var('x'), Var('y')
    both = lambda body: Pi('x', BOOL, Pi('y', BOOL, body))
    andb_ = lambda a, b: app('andb', a, b)
    eqb_ = lambda a, b: app('eqb', a, b)
    eqn = lambda a, b: app('Eq', NAT, a, b)
    a2, b2 = Var('a2'), Var('b2')

    # `Holds b -> Holds (orb a b)`: `orb a true` is true for either a, so
    # this is a case split on `a` rather than a rewrite.
    define(env, 'holds_orb_right',
           Pi('a', BOOL, Pi('b', BOOL, arrow(holds(Var('b')),
                                             holds(app('orb', Var('a'), Var('b')))))),
           Lambda('a', BOOL, Lambda('b', BOOL, Lambda(
               'h', holds(Var('b')),
               app('Eq.ind', BOOL, Var('true'),
                   Lambda('c', BOOL, Lambda('_t', app('Eq', BOOL, Var('true'), Var('c')),
                                             holds(app('orb', Var('a'), Var('c'))))),
                   app('Bool.ind', Lambda('_x', BOOL, holds(app('orb', Var('_x'), Var('true')))),
                       yes, yes, Var('a')),
                   Var('b'),
                   app('eq_symm', BOOL, Var('b'), Var('true'), Var('h')))))))

    # If `orb a b` holds and `a` is false, then `b` holds: rewrite `a` to
    # false, where `orb false b` computes to `b`.  The companion to
    # holds_orb_left, for reading the other side of a decided disjunction.
    define(env, 'orb_false_left',
           Pi('a', BOOL, Pi('b', BOOL, arrow(
              holds(app('orb', Var('a'), Var('b'))),
              arrow(app('Eq', BOOL, Var('a'), Var('false')),
                    holds(Var('b')))))),
           Lambda('a', BOOL, Lambda('b', BOOL, Lambda(
               'h', holds(app('orb', Var('a'), Var('b'))), Lambda(
               'e', app('Eq', BOOL, Var('a'), Var('false')),
               app('Eq.ind', BOOL, Var('a'),
                   Lambda('c', BOOL, Lambda(
                       '_t', app('Eq', BOOL, Var('a'), Var('c')),
                       arrow(holds(app('orb', Var('a'), Var('b'))),
                             holds(app('orb', Var('c'), Var('b')))))),
                   Lambda('g', holds(app('orb', Var('a'), Var('b'))), Var('g')),
                   Var('false'), Var('e'), Var('h')))))))

    Mer = Lambda('a', NAT, holds(eqb_(Var('a'), Var('a'))))
    define(env, 'eqb_refl', Pi('a', NAT, holds(eqb_(Var('a'), Var('a')))),
           Lambda('a', NAT, app('Nat.ind', Mer, yes,
                  Lambda('m', NAT, Lambda('ih', App(Mer, Var('m')), Var('ih'))),
                  Var('a'))))

    # Nothing is below itself: `ltb a a` is `leb (succ a) a`, and at
    # `succ a` that is the same term again, so the hypothesis serves.
    Mi = Lambda('a', NAT, arrow(holds(ltb_(Var('a'), Var('a'))),
                                holds(Var('false'))))
    define(env, 'ltb_irrefl',
           Pi('a', NAT, arrow(holds(ltb_(Var('a'), Var('a'))),
                              holds(Var('false')))),
           Lambda('a', NAT, app('Nat.ind', Mi,
                  Lambda('h', holds(ltb_(numeral(0), numeral(0))), Var('h')),
                  Lambda('m', NAT, Lambda('ih', App(Mi, Var('m')), Var('ih'))),
                  Var('a'))))

    # Two different numbers are ordered one way or the other.
    tri_ = lambda x, y: app('orb', ltb_(x, y), ltb_(y, x))
    Mtr = Lambda('j', NAT, Pi('k', NAT, arrow(
        app('Eq', BOOL, eqb_(Var('j'), Var('k')), Var('false')),
        holds(tri_(Var('j'), Var('k'))))))
    Mtr0 = Lambda('k', NAT, arrow(
        app('Eq', BOOL, eqb_(numeral(0), Var('k')), Var('false')),
        holds(tri_(numeral(0), Var('k')))))
    base_tr = Lambda('k', NAT, app('Nat.ind', Mtr0,
        Lambda('he', app('Eq', BOOL, eqb_(numeral(0), numeral(0)), Var('false')),
               app('absurd', holds(tri_(numeral(0), numeral(0))),
                   app('eq_symm', BOOL, Var('true'), Var('false'), Var('he')))),
        Lambda('k2', NAT, Lambda('_i', App(Mtr0, Var('k2')),
               Lambda('_e', app('Eq', BOOL, eqb_(numeral(0), succ_(Var('k2'))),
                                Var('false')), yes))),
        Var('k')))
    Mtrs = Lambda('k', NAT, arrow(
        app('Eq', BOOL, eqb_(succ_(Var('j2')), Var('k')), Var('false')),
        holds(tri_(succ_(Var('j2')), Var('k')))))
    step_tr = Lambda('j2', NAT, Lambda('ih', App(Mtr, Var('j2')), Lambda(
        'k', NAT, app('Nat.ind', Mtrs,
            Lambda('_e', app('Eq', BOOL, eqb_(succ_(Var('j2')), numeral(0)),
                             Var('false')), yes),
            Lambda('k2', NAT, Lambda('_i', App(Mtrs, Var('k2')), Lambda(
                'he', app('Eq', BOOL, eqb_(succ_(Var('j2')), succ_(Var('k2'))),
                          Var('false')),
                app(Var('ih'), Var('k2'), Var('he'))))),
            Var('k')))))
    define(env, 'ne_ordered',
           Pi('j', NAT, Pi('k', NAT, arrow(
              app('Eq', BOOL, eqb_(Var('j'), Var('k')), Var('false')),
              holds(tri_(Var('j'), Var('k')))))),
           Lambda('j', NAT, app('Nat.ind', Mtr, base_tr, step_tr, Var('j'))))

    notb_ = lambda a: app('notb', a)
    ltb_ = lambda a, b: app('ltb', a, b)

    # `a < b` gives `eqb a b = false`: induction on a with a split on b,
    # every case computation, the hypothesis, or absurd.
    Mln = Lambda('a', NAT, Pi('b', NAT, arrow(holds(ltb_(Var('a'), Var('b'))),
                  app('Eq', BOOL, eqb_(Var('a'), Var('b')), Var('false')))))
    Mln0 = Lambda('b', NAT, arrow(holds(ltb_(numeral(0), Var('b'))),
                  app('Eq', BOOL, eqb_(numeral(0), Var('b')), Var('false'))))
    base_ln = Lambda('b', NAT, app('Nat.ind', Mln0,
        Lambda('h', holds(ltb_(numeral(0), numeral(0))),
               app('absurd', app('Eq', BOOL, eqb_(numeral(0), numeral(0)),
                                 Var('false')), Var('h'))),
        Lambda('b2', NAT, Lambda('_i', App(Mln0, Var('b2')),
               Lambda('_h', holds(ltb_(numeral(0), succ_(Var('b2')))),
                      app('refl', BOOL, Var('false'))))),
        Var('b')))
    Mlns = Lambda('b', NAT, arrow(holds(ltb_(succ_(Var('a2')), Var('b'))),
                  app('Eq', BOOL, eqb_(succ_(Var('a2')), Var('b')), Var('false'))))
    step_ln = Lambda('a2', NAT, Lambda('ih', App(Mln, Var('a2')), Lambda(
        'b', NAT, app('Nat.ind', Mlns,
            Lambda('h', holds(ltb_(succ_(Var('a2')), numeral(0))),
                   app('absurd', app('Eq', BOOL, eqb_(succ_(Var('a2')), numeral(0)),
                                     Var('false')), Var('h'))),
            Lambda('b2', NAT, Lambda('_i', App(Mlns, Var('b2')), Lambda(
                'h', holds(ltb_(succ_(Var('a2')), succ_(Var('b2')))),
                app(Var('ih'), Var('b2'), Var('h'))))),
            Var('b')))))
    define(env, 'lt_ne',
           Pi('a', NAT, Pi('b', NAT, arrow(holds(ltb_(Var('a'), Var('b'))),
              app('Eq', BOOL, eqb_(Var('a'), Var('b')), Var('false'))))),
           Lambda('a', NAT, app('Nat.ind', Mln, base_ln, step_ln, Var('a'))))

    # `Holds a` gives `notb a = false`: rewrite a to true, where it computes.
    define(env, 'holds_notb_false',
           Pi('a', BOOL, arrow(holds(Var('a')),
                               app('Eq', BOOL, notb_(Var('a')), Var('false')))),
           Lambda('a', BOOL, Lambda('h', holds(Var('a')), app(
               'Eq.ind', BOOL, Var('true'),
               Lambda('c', BOOL, Lambda('_t', app('Eq', BOOL, Var('true'), Var('c')),
                                          app('Eq', BOOL, notb_(Var('c')), Var('false')))),
               app('refl', BOOL, Var('false')), Var('a'),
               app('eq_symm', BOOL, Var('a'), Var('true'), Var('h'))))))

    # `a <= a + b`.  `add` recurses on its second argument, so `add a 0` is
    # `a` by computation and `add a (succ b)` is `succ (add a b)`: the
    # induction is on `b`, and each step is leb_succ through leb_trans.
    j2 = Var('j2')
    Mla = Lambda('b', NAT, holds(leb_(Var('a'), app('add', Var('a'), Var('b')))))
    define(env, 'le_add_right',
           Pi('a', NAT, Pi('b', NAT,
              holds(leb_(Var('a'), app('add', Var('a'), Var('b')))))),
           Lambda('a', NAT, Lambda('b', NAT, app('Nat.ind', Mla,
                  app('leb_refl', Var('a')),
                  Lambda('k', NAT, Lambda('ih', App(Mla, Var('k')),
                         app('leb_trans', Var('a'),
                             app('add', Var('a'), Var('k')),
                             succ_(app('add', Var('a'), Var('k'))),
                             Var('ih'),
                             app('leb_succ', app('add', Var('a'), Var('k')))))),
                  Var('b')))))

    # `x <= y` gives `b + x <= b + y`.  `add` recurses on its second
    # argument, so the induction is on x with a split on y: x = 0 is
    # le_add_right; at succ both sides step by succ and leb steps with them.
    Mal = Lambda('x', NAT, Pi('y', NAT, arrow(holds(leb_(Var('x'), Var('y'))),
                  holds(leb_(app('add', Var('b'), Var('x')),
                             app('add', Var('b'), Var('y')))))))
    Mal0 = Lambda('y', NAT, arrow(holds(leb_(numeral(0), Var('y'))),
                  holds(leb_(app('add', Var('b'), numeral(0)),
                             app('add', Var('b'), Var('y'))))))
    base_al = Lambda('y', NAT, Lambda('_h', holds(leb_(numeral(0), Var('y'))),
                     app('le_add_right', Var('b'), Var('y'))))
    Mals = Lambda('y', NAT, arrow(holds(leb_(succ_(Var('x2')), Var('y'))),
                  holds(leb_(app('add', Var('b'), succ_(Var('x2'))),
                             app('add', Var('b'), Var('y'))))))
    step_al = Lambda('x2', NAT, Lambda('ih', App(Mal, Var('x2')), Lambda(
        'y', NAT, app('Nat.ind', Mals,
            Lambda('h', holds(leb_(succ_(Var('x2')), numeral(0))),
                   app('absurd', holds(leb_(app('add', Var('b'), succ_(Var('x2'))),
                                            app('add', Var('b'), numeral(0)))),
                       Var('h'))),
            Lambda('y2', NAT, Lambda('_i', App(Mals, Var('y2')), Lambda(
                'h', holds(leb_(succ_(Var('x2')), succ_(Var('y2')))),
                app(Var('ih'), Var('y2'), Var('h'))))),
            Var('y')))))
    define(env, 'add_le_add_left',
           Pi('b', NAT, Pi('x', NAT, Pi('y', NAT, arrow(
              holds(leb_(Var('x'), Var('y'))),
              holds(leb_(app('add', Var('b'), Var('x')),
                         app('add', Var('b'), Var('y')))))))),
           Lambda('b', NAT, Lambda('x', NAT,
                  app('Nat.ind', Mal, base_al, step_al, Var('x')))))

    # `eqb a b` as an equation: the bridge from a decided comparison to a
    # substitution.  Every proof that splits on `eqb` and then wants to use
    # the two sides interchangeably needs it, and it is an induction on both.
    Meb = Lambda('a', NAT, Pi('b', NAT, arrow(holds(eqb_(Var('a'), Var('b'))),
                                               eqn(Var('a'), Var('b')))))
    Meb0 = Lambda('b', NAT, arrow(holds(eqb_(numeral(0), Var('b'))),
                                  eqn(numeral(0), Var('b'))))
    base_eb = Lambda('b', NAT, app('Nat.ind', Meb0,
        Lambda('_h', holds(eqb_(numeral(0), numeral(0))), app('refl', NAT, numeral(0))),
        Lambda('b2', NAT, Lambda('_i', App(Meb0, Var('b2')), Lambda(
            'h', holds(eqb_(numeral(0), succ_(Var('b2')))),
            app('absurd', eqn(numeral(0), succ_(Var('b2'))), Var('h'))))),
        Var('b')))
    Mebs = Lambda('b', NAT, arrow(holds(eqb_(succ_(Var('a2')), Var('b'))),
                                  eqn(succ_(Var('a2')), Var('b'))))
    cong_s = lambda e: app('Eq.ind', NAT, Var('a2'),
                           Lambda('c', NAT, Lambda('_t', eqn(Var('a2'), Var('c')),
                                                    eqn(succ_(Var('a2')), succ_(Var('c'))))),
                           app('refl', NAT, succ_(Var('a2'))), Var('b2'), e)
    step_eb = Lambda('a2', NAT, Lambda('ih', App(Meb, Var('a2')), Lambda('b', NAT,
        app('Nat.ind', Mebs,
            Lambda('h', holds(eqb_(succ_(Var('a2')), numeral(0))),
                   app('absurd', eqn(succ_(Var('a2')), numeral(0)), Var('h'))),
            Lambda('b2', NAT, Lambda('_i', App(Mebs, Var('b2')), Lambda(
                'h', holds(eqb_(succ_(Var('a2')), succ_(Var('b2')))),
                cong_s(app(Var('ih'), Var('b2'), Var('h')))))),
            Var('b')))))
    define(env, 'eqb_eq',
           Pi('a', NAT, Pi('b', NAT, arrow(holds(eqb_(Var('a'), Var('b'))),
                                            eqn(Var('a'), Var('b'))))),
           Lambda('a', NAT, app('Nat.ind', Meb, base_eb, step_eb, Var('a'))))

    # `a < succ b` and `a != b` give `a < b`: `ltb a (succ b)` is
    # `leb a b`, and `leb` with `eqb` false is `ltb`.  Both halves are the
    # same induction, so they are one lemma.
    Mls = Lambda('a', NAT, Pi('b', NAT, arrow(holds(ltb_(Var('a'), succ_(Var('b')))),
                  arrow(app('Eq', BOOL, eqb_(Var('a'), Var('b')), Var('false')),
                        holds(ltb_(Var('a'), Var('b')))))))
    Mls0 = Lambda('b', NAT, arrow(holds(ltb_(numeral(0), succ_(Var('b')))),
                  arrow(app('Eq', BOOL, eqb_(numeral(0), Var('b')), Var('false')),
                        holds(ltb_(numeral(0), Var('b'))))))
    base_ls = Lambda('b', NAT, app('Nat.ind', Mls0,
        Lambda('_h', holds(ltb_(numeral(0), succ_(numeral(0)))),
               Lambda('he', app('Eq', BOOL, eqb_(numeral(0), numeral(0)), Var('false')),
                      app('absurd', holds(ltb_(numeral(0), numeral(0))),
                          app('eq_symm', BOOL, Var('true'), Var('false'),
                              Var('he'))))),
        Lambda('b2', NAT, Lambda('_i', App(Mls0, Var('b2')),
               Lambda('_h', holds(ltb_(numeral(0), succ_(succ_(Var('b2'))))),
                      Lambda('_e', app('Eq', BOOL, eqb_(numeral(0), succ_(Var('b2'))),
                                        Var('false')), yes)))),
        Var('b')))
    Mlss = Lambda('b', NAT, arrow(holds(ltb_(succ_(Var('a2')), succ_(Var('b')))),
                  arrow(app('Eq', BOOL, eqb_(succ_(Var('a2')), Var('b')), Var('false')),
                        holds(ltb_(succ_(Var('a2')), Var('b'))))))
    step_ls = Lambda('a2', NAT, Lambda('ih', App(Mls, Var('a2')), Lambda('b', NAT,
        app('Nat.ind', Mlss,
            Lambda('h', holds(ltb_(succ_(Var('a2')), succ_(numeral(0)))),
                   Lambda('_e', app('Eq', BOOL, eqb_(succ_(Var('a2')), numeral(0)),
                                     Var('false')),
                          app('absurd', holds(ltb_(succ_(Var('a2')), numeral(0))),
                              Var('h')))),
            Lambda('b2', NAT, Lambda('_i', App(Mlss, Var('b2')), Lambda(
                'h', holds(ltb_(succ_(Var('a2')), succ_(succ_(Var('b2'))))),
                Lambda('e', app('Eq', BOOL, eqb_(succ_(Var('a2')), succ_(Var('b2'))),
                                 Var('false')),
                       app(Var('ih'), Var('b2'), Var('h'), Var('e')))))),
            Var('b')))))
    define(env, 'lt_succ_ne',
           Pi('a', NAT, Pi('b', NAT, arrow(holds(ltb_(Var('a'), succ_(Var('b')))),
                 arrow(app('Eq', BOOL, eqb_(Var('a'), Var('b')), Var('false')),
                       holds(ltb_(Var('a'), Var('b'))))))),
           Lambda('a', NAT, app('Nat.ind', Mls, base_ls, step_ls, Var('a'))))

    # `sub m 0 = m` is an induction, because sub recurses on its *first*
    # argument: `sub (succ j) 1` reduces to `sub j 0` and stops there.  A
    # spec that indexes `i - 1` needs this to talk about position `j` when
    # `i` is `succ j`, which is every inductive step over positions.
    Msz = Lambda('m', NAT, app('Eq', NAT, app('sub', Var('m'), numeral(0)),
                               Var('m')))
    define(env, 'sub_zero',
           Pi('m', NAT, app('Eq', NAT, app('sub', Var('m'), numeral(0)),
                            Var('m'))),
           Lambda('m', NAT, app('Nat.ind', Msz,
                  app('refl', NAT, numeral(0)),
                  Lambda('k', NAT, Lambda('ih', App(Msz, Var('k')),
                         app('refl', NAT, succ_(Var('k'))))),
                  Var('m'))))

    # Totality and antisymmetry of leb, both by induction on the first
    # argument with a case split on the second inside.  Each case is either
    # computation, the inductive hypothesis, or absurd from a `false`
    # hypothesis.  They are what turns a loop's exit condition -- the
    # counter is <= the bound and not < it -- into the counter *being* the
    # bound, which is the step from "every position checked" to "every
    # position".
    notb_ = lambda a: app('notb', a)
    ltb_ = lambda a, b: app('ltb', a, b)
    eqn = lambda a, b: app('Eq', NAT, a, b)
    a_, b_, a2, b2 = Var('a'), Var('b'), Var('a2'), Var('b2')

    # ltb_false_leb : forall a b, Holds (notb (ltb a b)) -> Holds (leb b a)
    Mt = Lambda('a', NAT, Pi('b', NAT, arrow(holds(notb_(ltb_(a_, b_))),
                                              holds(leb_(b_, a_)))))
    # base a = 0, split b: b = 0 computes; b = succ _ has a false hypothesis
    Mt0 = Lambda('b', NAT, arrow(holds(notb_(ltb_(numeral(0), b_))),
                                 holds(leb_(b_, numeral(0)))))
    base_t = Lambda('b', NAT, app('Nat.ind', Mt0,
                Lambda('h', holds(notb_(ltb_(numeral(0), numeral(0)))), yes),
                Lambda('b2', NAT, Lambda('_i', App(Mt0, b2), Lambda(
                    'h', holds(notb_(ltb_(numeral(0), succ_(b2)))),
                    app('absurd', holds(leb_(succ_(b2), numeral(0))), Var('h'))))),
                b_))
    # step a = succ a2, split b: b = 0 computes; b = succ b2 is ih at b2
    Mts = Lambda('b', NAT, arrow(holds(notb_(ltb_(succ_(a2), b_))),
                                 holds(leb_(b_, succ_(a2)))))
    step_t = Lambda('a2', NAT, Lambda('ih', App(Mt, a2), Lambda('b', NAT,
                app('Nat.ind', Mts,
                    Lambda('h', holds(notb_(ltb_(succ_(a2), numeral(0)))), yes),
                    Lambda('b2', NAT, Lambda('_i', App(Mts, b2), Lambda(
                        'h', holds(notb_(ltb_(succ_(a2), succ_(b2)))),
                        app(Var('ih'), b2, Var('h'))))),
                    b_))))
    define(env, 'ltb_false_leb',
           Pi('a', NAT, Pi('b', NAT, arrow(holds(notb_(ltb_(a_, b_))),
                                            holds(leb_(b_, a_))))),
           Lambda('a', NAT, app('Nat.ind', Mt, base_t, step_t, a_)))

    # leb_antisymm : forall a b, Holds (leb a b) -> Holds (leb b a) -> Eq a b
    Ma = Lambda('a', NAT, Pi('b', NAT, arrow(holds(leb_(a_, b_)),
                                              arrow(holds(leb_(b_, a_)), eqn(a_, b_)))))
    Ma0 = Lambda('b', NAT, arrow(holds(leb_(numeral(0), b_)),
                                 arrow(holds(leb_(b_, numeral(0))), eqn(numeral(0), b_))))
    base_a = Lambda('b', NAT, app('Nat.ind', Ma0,
                Lambda('_1', holds(leb_(numeral(0), numeral(0))),
                       Lambda('_2', holds(leb_(numeral(0), numeral(0))),
                              app('refl', NAT, numeral(0)))),
                Lambda('b2', NAT, Lambda('_i', App(Ma0, b2),
                    Lambda('_1', holds(leb_(numeral(0), succ_(b2))),
                           Lambda('h2', holds(leb_(succ_(b2), numeral(0))),
                                  app('absurd', eqn(numeral(0), succ_(b2)), Var('h2')))))),
                b_))
    Mas = Lambda('b', NAT, arrow(holds(leb_(succ_(a2), b_)),
                                 arrow(holds(leb_(b_, succ_(a2))), eqn(succ_(a2), b_))))
    # succ is a congruence: from Eq a2 b2, Eq (succ a2) (succ b2), by Eq.ind
    succ_cong = lambda e: app('Eq.ind', NAT, a2,
                              Lambda('c', NAT, Lambda('_t', eqn(a2, Var('c')),
                                                       eqn(succ_(a2), succ_(Var('c'))))),
                              app('refl', NAT, succ_(a2)), b2, e)
    step_a = Lambda('a2', NAT, Lambda('ih', App(Ma, a2), Lambda('b', NAT,
                app('Nat.ind', Mas,
                    Lambda('h1', holds(leb_(succ_(a2), numeral(0))),
                           Lambda('_2', holds(leb_(numeral(0), succ_(a2))),
                                  app('absurd', eqn(succ_(a2), numeral(0)), Var('h1')))),
                    Lambda('b2', NAT, Lambda('_i', App(Mas, b2),
                        Lambda('h1', holds(leb_(succ_(a2), succ_(b2))),
                               Lambda('h2', holds(leb_(succ_(b2), succ_(a2))),
                                      succ_cong(app(Var('ih'), b2, Var('h1'), Var('h2'))))))),
                    b_))))
    define(env, 'leb_antisymm',
           Pi('a', NAT, Pi('b', NAT, arrow(holds(leb_(a_, b_)),
                                            arrow(holds(leb_(b_, a_)), eqn(a_, b_))))),
           Lambda('a', NAT, app('Nat.ind', Ma, base_a, step_a, a_)))

    define(env, 'andb_both',
           both(arrow(holds(xb), arrow(holds(yb), holds(andb_(xb, yb))))),
           Lambda('x', BOOL, Lambda('y', BOOL, Lambda(
               'hx', holds(xb), Lambda('hy', holds(yb), App(app(
                   'Bool.ind',
                   Lambda('t', BOOL, arrow(holds(Var('t')),
                                           holds(andb_(Var('t'), yb)))),
                   Lambda('_h', holds(Var('true')), Var('hy')),
                   Lambda('h', holds(Var('false')),
                          app('absurd', holds(andb_(Var('false'), yb)),
                              Var('h'))),
                   xb), Var('hx')))))))
    define(env, 'andb_left', both(arrow(holds(andb_(xb, yb)), holds(xb))),
           Lambda('x', BOOL, Lambda('y', BOOL, app(
               'Bool.ind',
               Lambda('t', BOOL, arrow(holds(andb_(Var('t'), yb)),
                                       holds(Var('t')))),
               Lambda('h', holds(yb), yes),
               Lambda('h', holds(Var('false')), Var('h')),
               xb))))
    define(env, 'andb_right', both(arrow(holds(andb_(xb, yb)), holds(yb))),
           Lambda('x', BOOL, Lambda('y', BOOL, app(
               'Bool.ind',
               Lambda('t', BOOL, arrow(holds(andb_(Var('t'), yb)),
                                       holds(yb))),
               Lambda('h', holds(yb), Var('h')),
               Lambda('h', holds(Var('false')),
                      app('absurd', holds(yb), Var('h'))),
               xb))))

    # snoc_le: a list built by appending one item at a time is never longer
    # than the count of the items appended.  What a loop that builds a list
    # needs before its length can be bounded.
    A2 = Var('A')
    len_ = lambda t: app('len', A2, t)
    snoc_of = lambda xs, x: app('snoc', A2, xs, x)
    Msn = Lambda('xs', listof(A2), Pi('x', A2, Pi('n', NAT, arrow(
        holds(leb_(len_(Var('xs')), Var('n'))),
        holds(leb_(len_(snoc_of(Var('xs'), Var('x'))), succ_(Var('n'))))))))
    Msn_n = Lambda('n', NAT, arrow(
        holds(leb_(len_(app('cons', A2, Var('h'), Var('t'))), Var('n'))),
        holds(leb_(len_(snoc_of(app('cons', A2, Var('h'), Var('t')),
                                Var('x'))), succ_(Var('n'))))))
    snoc_nil = Lambda('x', A2, Lambda('n', NAT, Lambda(
        'h', holds(leb_(numeral(0), Var('n'))), yes)))
    snoc_cons = Lambda('h', A2, Lambda('t', listof(A2), Lambda(
        'ih', App(Msn, Var('t')), Lambda('x', A2, Lambda('n', NAT, app(
            'Nat.ind', Msn_n,
            Lambda('hz', holds(leb_(len_(app('cons', A2, Var('h'), Var('t'))),
                                    numeral(0))),
                   app('absurd', holds(leb_(len_(snoc_of(
                       app('cons', A2, Var('h'), Var('t')), Var('x'))),
                       succ_(numeral(0)))), Var('hz'))),
            Lambda('n2', NAT, Lambda('_i', App(Msn_n, Var('n2')), Lambda(
                'hh', holds(leb_(len_(app('cons', A2, Var('h'), Var('t'))),
                                 succ_(Var('n2')))),
                app(Var('ih'), Var('x'), Var('n2'), Var('hh'))))),
            Var('n')))))))
    define(env, 'snoc_le',
           Pi('A', TYPE0, Pi('xs', listof(A2), App(Msn, Var('xs'))),
              implicit=True),
           Lambda('A', TYPE0, app('List.rec' if False else 'List.ind', A2,
                                  Msn, snoc_nil, snoc_cons)))

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

    arithmetic_lemmas(env)
    int_prelude(env)
    return env


INT_OPS = ('int_neg', 'int_add', 'int_sub', 'int_mul', 'int_ltb',
           'int_leb', 'int_eqb', 'int_subNatNat', 'int_negOfNat')


def int_literal(k):
    """The integer k as a term: `Int.ofNat k`, or `Int.negSucc (-k - 1)`."""
    if k >= 0:
        return App(Var('Int.ofNat'), numeral(k))
    return App(Var('Int.negSucc'), numeral(-k - 1))


def int_prelude(env):
    r"""The integers, as Lean has them: `ofNat n` for n, `negSucc n` for
    -(n + 1).  Every operation is a case split on its arguments' shapes
    that lands on `Nat` arithmetic and an `if` on a `Nat` comparison --
    so that once each integer variable is split into its two shapes
    (`by_int_cases`), what is left is a goal `by_bounds` already knows.

    Named `int_add` .. `int_eqb`, not `Int.add`: exported to Lean inside a
    namespace, `Int.add`'s own body would resolve `add` to itself.

    Not trusted: these are definitions like any other, and the kernel
    checks their types; what they *mean* is pinned by the selftest, which
    computes each against Python's integers over a grid.
    """
    ofn = lambda n: App(Var('Int.ofNat'), n)
    negs = lambda n: App(Var('Int.negSucc'), n)
    # `n + 1`, not `succ n`: the accelerator computes it when n is a
    # literal, where `succ LIT` would be walked down one step at a time
    succ_ = lambda n: app('add', n, numeral(1))
    ite = lambda ty, c, a, b: app('ite', ty, c, a, b)
    m, n, a, b = Var('m'), Var('n'), Var('a'), Var('b')
    inductive(env, 'Int', [('Int.ofNat', [NAT]), ('Int.negSucc', [NAT])])

    def cases1(name, ty_out, on_of, on_neg):
        """name : Int -> ty_out, by cases."""
        define(env, name, arrow(INT, ty_out), Lambda('a', INT, app(
            'Int.rec', Lambda('_', INT, ty_out),
            Lambda('m', NAT, on_of(m)), Lambda('m', NAT, on_neg(m)),
            a)))

    def cases2(name, ty_out, oo, on, no, nn):
        """name : Int -> Int -> ty_out, by cases on both."""
        inner = lambda f, g: Lambda('m', NAT, app(
            'Int.rec', Lambda('_', INT, ty_out),
            Lambda('n', NAT, f(m, n)), Lambda('n', NAT, g(m, n)), b))
        define(env, name, arrow(INT, arrow(INT, ty_out)),
               Lambda('a', INT, Lambda('b', INT, app(
                   'Int.rec', Lambda('_', INT, ty_out),
                   inner(oo, on), inner(no, nn), a))))

    # m - n as an integer, from two naturals
    define(env, 'int_subNatNat', arrow(NAT, arrow(NAT, INT)),
           Lambda('m', NAT, Lambda('n', NAT, ite(
               INT, app('leb', n, m), ofn(app('sub', m, n)),
               negs(app('sub', app('sub', n, m), numeral(1)))))))
    # -k, from a natural
    define(env, 'int_negOfNat', arrow(NAT, INT),
           Lambda('m', NAT, ite(INT, app('eqb', m, numeral(0)),
                                ofn(numeral(0)),
                                negs(app('sub', m, numeral(1))))))
    cases1('int_neg', INT, lambda m: app('int_negOfNat', m),
           lambda m: ofn(succ_(m)))
    cases2('int_add', INT,
           lambda m, n: ofn(app('add', m, n)),
           lambda m, n: app('int_subNatNat', m, succ_(n)),
           lambda m, n: app('int_subNatNat', n, succ_(m)),
           lambda m, n: negs(succ_(app('add', m, n))))
    define(env, 'int_sub', arrow(INT, arrow(INT, INT)),
           Lambda('a', INT, Lambda('b', INT, app(
               'int_add', a, app('int_neg', b)))))
    cases2('int_mul', INT,
           lambda m, n: ofn(app('mul', m, n)),
           lambda m, n: app('int_negOfNat', app('mul', m, succ_(n))),
           lambda m, n: app('int_negOfNat', app('mul', succ_(m), n)),
           lambda m, n: ofn(app('mul', succ_(m), succ_(n))))
    cases2('int_ltb', BOOL,
           lambda m, n: app('ltb', m, n),
           lambda m, n: Var('false'),
           lambda m, n: Var('true'),
           lambda m, n: app('ltb', n, m))
    define(env, 'int_leb', arrow(INT, arrow(INT, BOOL)),
           Lambda('a', INT, Lambda('b', INT, app(
               'notb', app('int_ltb', b, a)))))
    cases2('int_eqb', BOOL,
           lambda m, n: app('eqb', m, n),
           lambda m, n: Var('false'),
           lambda m, n: Var('false'),
           lambda m, n: app('eqb', m, n))


def arithmetic_lemmas(env):
    r"""What an overflow obligation needs: `+` against a bound.

    Splitting and computing settles a claim the code's own guards decide.
    `used + n <= max` after the guard `used + n <= sizes[heap]` is not that:
    it needs `sizes[heap] <= max`, which is the element's type, and then
    transitivity.  These are the steps `by_bounds` chains, each proved here
    and none assumed.

      add_le_add_right  x <= y  gives  x + b <= y + b
      add_le_add        x <= y, u <= v  give  x + u <= y + v
      add_le_of_le_sub  n <= s, u <= s - n  give  u + n <= s
      lt_le             a < b  gives  a <= b
      not_lt_le         (a < b) = false  gives  b <= a
      not_le_lt         (a <= b) = false  gives  b < a
      all_le            every element of a list is <= m
      nth_all_le        so is any element read from it

    `add_le_of_le_sub` is the one a checked addition needs: the guard
    `n <= s && used <= s - n` is how `used + n <= s` is tested without
    evaluating `used + n`, and this is what that test establishes.
    """
    holds = lambda x: App(Var('Holds'), x)
    yes = app('refl', BOOL, Var('true'))
    succ_ = lambda a: App(Var('succ'), a)
    leb_ = lambda a, b: app('leb', a, b)
    add_ = lambda a, b: app('add', a, b)
    sub_ = lambda a, b: app('sub', a, b)
    x, y, u, v, b = (Var(n) for n in 'xyuvb')

    # add recurses on its second argument, so b + 1 on both sides is succ on
    # both sides, and leb (succ p) (succ q) is leb p q: the step is the
    # induction hypothesis itself.
    M = Lambda('b', NAT, holds(leb_(add_(x, b), add_(Var('y'), b))))
    define(env, 'add_le_add_right',
           Pi('b', NAT, Pi('x', NAT, Pi('y', NAT, arrow(
               holds(leb_(x, y)), holds(leb_(add_(x, b), add_(y, b))))))),
           Lambda('b', NAT, Lambda('x', NAT, Lambda('y', NAT, Lambda(
               'h', holds(leb_(x, y)),
               app('Nat.ind', M, Var('h'),
                   Lambda('k', NAT, Lambda('ih', App(M, Var('k')),
                                           Var('ih'))),
                   b))))))

    define(env, 'add_le_add',
           Pi('x', NAT, Pi('y', NAT, Pi('u', NAT, Pi('v', NAT, arrow(
               holds(leb_(x, y)), arrow(holds(leb_(u, v)),
                                        holds(leb_(add_(x, u),
                                                   add_(y, v))))))))),
           Lambda('x', NAT, Lambda('y', NAT, Lambda('u', NAT, Lambda(
               'v', NAT, Lambda('h1', holds(leb_(x, y)), Lambda(
                   'h2', holds(leb_(u, v)),
                   app('leb_trans', add_(x, u), add_(y, u), add_(y, v),
                       app('add_le_add_right', u, x, y, Var('h1')),
                       app('add_le_add_left', y, u, v, Var('h2'))))))))))

    # Induction on n, generalising s; at n + 1, s = 0 contradicts n + 1 <= s,
    # and at s = s2 + 1 all three of leb, sub and add step down by one.  At
    # n = 0 the split on s is what makes `sub s 0` compute to s.
    s = Var('s')
    Mn = Lambda('n', NAT, Pi('s', NAT, arrow(
        holds(leb_(Var('n'), s)),
        arrow(holds(leb_(u, sub_(s, Var('n')))),
              holds(leb_(add_(u, Var('n')), s))))))
    B0 = Lambda('s', NAT, arrow(holds(leb_(u, sub_(s, numeral(0)))),
                                holds(leb_(u, s))))
    base = Lambda('s', NAT, Lambda('_h0', holds(leb_(numeral(0), s)),
        app('Nat.ind', B0,
            Lambda('h', holds(leb_(u, sub_(numeral(0), numeral(0)))),
                   Var('h')),
            Lambda('m', NAT, Lambda('_i', App(B0, Var('m')), Lambda(
                'h', holds(leb_(u, sub_(succ_(Var('m')), numeral(0)))),
                Var('h')))),
            s)))
    k = Var('k')
    Bs = Lambda('s', NAT, arrow(
        holds(leb_(succ_(k), s)),
        arrow(holds(leb_(u, sub_(s, succ_(k)))),
              holds(leb_(add_(u, succ_(k)), s)))))
    step = Lambda('k', NAT, Lambda('ih', App(Mn, k), Lambda('s', NAT, app(
        'Nat.ind', Bs,
        Lambda('h1', holds(leb_(succ_(k), numeral(0))), Lambda(
            'h2', holds(leb_(u, sub_(numeral(0), succ_(k)))),
            app('absurd', holds(leb_(add_(u, succ_(k)), numeral(0))),
                Var('h1')))),
        Lambda('s2', NAT, Lambda('_i', App(Bs, Var('s2')), Lambda(
            'h1', holds(leb_(succ_(k), succ_(Var('s2')))), Lambda(
                'h2', holds(leb_(u, sub_(succ_(Var('s2')), succ_(k)))),
                app(Var('ih'), Var('s2'), Var('h1'), Var('h2')))))),
        s))))
    define(env, 'add_le_of_le_sub',
           Pi('u', NAT, Pi('n', NAT, Pi('s', NAT, arrow(
               holds(leb_(Var('n'), s)),
               arrow(holds(leb_(u, sub_(s, Var('n')))),
                     holds(leb_(add_(u, Var('n')), s))))))),
           Lambda('u', NAT, Lambda('n', NAT, Lambda('s', NAT, app(
               App(app('Nat.ind', Mn, base, step, Var('n')), s))))))

    a = Var('a')
    define(env, 'lt_le',
           Pi('a', NAT, Pi('b', NAT, arrow(holds(app('ltb', a, b)),
                                           holds(leb_(a, b))))),
           Lambda('a', NAT, Lambda('b', NAT, Lambda(
               'h', holds(app('ltb', a, b)),
               app('leb_trans', a, succ_(a), b, app('leb_succ', a),
                   Var('h'))))))

    # A guard that went false: `Eq Bool g false`.  Turned round and carried
    # into `notb g`, it is what `ltb_false_leb` reads.
    def notb_of(g):
        return app('Eq.ind', BOOL, Var('false'),
                   Lambda('z', BOOL, Lambda('_e', app('Eq', BOOL,
                                                      Var('false'), Var('z')),
                                            holds(app('notb', Var('z'))))),
                   yes, g, app('eq_symm', BOOL, g, Var('false'), Var('h')))
    is_false = lambda g: app('Eq', BOOL, g, Var('false'))
    define(env, 'not_lt_le',
           Pi('a', NAT, Pi('b', NAT, arrow(is_false(app('ltb', a, b)),
                                           holds(leb_(b, a))))),
           Lambda('a', NAT, Lambda('b', NAT, Lambda(
               'h', is_false(app('ltb', a, b)),
               app('ltb_false_leb', a, b, notb_of(app('ltb', a, b)))))))
    # not (a <= b) is not (a < b + 1), by computation, which is b + 1 <= a.
    define(env, 'not_le_lt',
           Pi('a', NAT, Pi('b', NAT, arrow(is_false(leb_(a, b)),
                                           holds(app('ltb', b, a))))),
           Lambda('a', NAT, Lambda('b', NAT, Lambda(
               'h', is_false(leb_(a, b)),
               app('ltb_false_leb', a, succ_(b), notb_of(leb_(a, b)))))))

    # -- commutativity, for a checked addition written either way round ------
    eqn = lambda l, r: app('Eq', NAT, l, r)

    def congr_succ(l, r, h):
        """Eq Nat (succ l) (succ r) from h : Eq Nat l r."""
        return app('Eq.ind', NAT, l,
                   Lambda('_w', NAT, Lambda('_e', eqn(l, Var('_w')),
                                            eqn(succ_(l), succ_(Var('_w'))))),
                   app('refl', NAT, succ_(l)), r, h)

    Mz = Lambda('b', NAT, eqn(add_(numeral(0), b), b))
    define(env, 'add_zero_left', Pi('b', NAT, eqn(add_(numeral(0), b), b)),
           Lambda('b', NAT, app('Nat.ind', Mz, app('refl', NAT, numeral(0)),
               Lambda('k', NAT, Lambda('ih', App(Mz, Var('k')), congr_succ(
                   add_(numeral(0), Var('k')), Var('k'), Var('ih')))),
               b)))
    Ms = Lambda('b', NAT, eqn(add_(succ_(a), b), succ_(add_(a, b))))
    define(env, 'add_succ_left',
           Pi('a', NAT, Pi('b', NAT, eqn(add_(succ_(a), b),
                                         succ_(add_(a, b))))),
           Lambda('a', NAT, Lambda('b', NAT, app(
               'Nat.ind', Ms, app('refl', NAT, succ_(a)),
               Lambda('k', NAT, Lambda('ih', App(Ms, Var('k')), congr_succ(
                   add_(succ_(a), Var('k')), succ_(add_(a, Var('k'))),
                   Var('ih')))),
               b))))
    Mc = Lambda('b', NAT, eqn(add_(a, b), add_(b, a)))
    k_ = Var('k')
    define(env, 'add_comm',
           Pi('a', NAT, Pi('b', NAT, eqn(add_(a, b), add_(b, a)))),
           Lambda('a', NAT, Lambda('b', NAT, app(
               'Nat.ind', Mc,
               app('symm', NAT, add_(numeral(0), a), a,
                   app('add_zero_left', a)),
               Lambda('k', NAT, Lambda('ih', App(Mc, k_), app(
                   'trans', NAT, succ_(add_(a, k_)), succ_(add_(k_, a)),
                   add_(succ_(k_), a),
                   congr_succ(add_(a, k_), add_(k_, a), Var('ih')),
                   app('symm', NAT, add_(succ_(k_), a), succ_(add_(k_, a)),
                       app('add_succ_left', k_, a))))),
               b))))

    # (a - b) + b = a behind b <= a.  Induction on b, generalising a; at
    # b = 0, `sub_zero`; at b = k + 1, a = 0 contradicts, and at a = a' + 1
    # both sides step down to the hypothesis at (k, a'), under a `succ`.
    Msa = Lambda('b', NAT, Pi('a', NAT, arrow(
        holds(leb_(Var('b'), Var('a'))),
        eqn(add_(sub_(Var('a'), Var('b')), Var('b')), Var('a')))))
    Bsa = Lambda('a', NAT, arrow(
        holds(leb_(succ_(k_), Var('a'))),
        eqn(add_(sub_(Var('a'), succ_(k_)), succ_(k_)), Var('a'))))
    a2 = Var('a2')
    define(env, 'sub_add_cancel',
           Pi('b', NAT, Pi('a', NAT, arrow(
               holds(leb_(Var('b'), Var('a'))),
               eqn(add_(sub_(Var('a'), Var('b')), Var('b')), Var('a'))))),
           Lambda('b', NAT, app(
               'Nat.ind', Msa,
               Lambda('a', NAT, Lambda('_h', holds(leb_(numeral(0), Var('a'))),
                                       app('sub_zero', Var('a')))),
               Lambda('k', NAT, Lambda('ih', App(Msa, k_), Lambda('a', NAT, app(
                   'Nat.ind', Bsa,
                   Lambda('h', holds(leb_(succ_(k_), numeral(0))), app(
                       'absurd', eqn(add_(sub_(numeral(0), succ_(k_)),
                                          succ_(k_)), numeral(0)), Var('h'))),
                   Lambda('a2', NAT, Lambda('_i', App(Bsa, a2), Lambda(
                       'h', holds(leb_(succ_(k_), succ_(a2))),
                       congr_succ(add_(sub_(a2, k_), k_), a2,
                                  app(Var('ih'), a2, Var('h')))))),
                   Var('a'))))),
               Var('b'))))

    # b <= a and a - b < s give a < b + s: the checked `addr - base < size`
    # read as the sum it avoids forming.  a - b + 1 <= s, plus b on both
    # sides, is (a - b) + 1 + b <= s + b; the left is a + 1 by add_succ_left
    # and sub_add_cancel, the right is b + s by add_comm.
    s_ = Var('s')
    d_ = sub_(a, b)
    P1 = app('add_le_add_right', b, succ_(d_), s_, Var('h2'))
    e1 = app('add_succ_left', d_, b)
    e2 = congr_succ(add_(d_, b), a, app('sub_add_cancel', b, a, Var('h1')))
    step1 = app('Eq.ind', NAT, add_(succ_(d_), b),
                Lambda('_w', NAT, Lambda('_e', eqn(add_(succ_(d_), b),
                                                   Var('_w')),
                                         holds(leb_(Var('_w'), add_(s_, b))))),
                P1, succ_(add_(d_, b)), e1)
    step2 = app('Eq.ind', NAT, succ_(add_(d_, b)),
                Lambda('_w', NAT, Lambda('_e', eqn(succ_(add_(d_, b)),
                                                   Var('_w')),
                                         holds(leb_(Var('_w'), add_(s_, b))))),
                step1, succ_(a), e2)
    step3 = app('Eq.ind', NAT, add_(s_, b),
                Lambda('_w', NAT, Lambda('_e', eqn(add_(s_, b), Var('_w')),
                                         holds(leb_(succ_(a), Var('_w'))))),
                step2, add_(b, s_), app('add_comm', s_, b))
    define(env, 'lt_add_of_sub_lt',
           Pi('a', NAT, Pi('b', NAT, Pi('s', NAT, arrow(
               holds(leb_(b, a)),
               arrow(holds(app('ltb', sub_(a, b), s_)),
                     holds(app('ltb', a, add_(b, s_)))))))),
           Lambda('a', NAT, Lambda('b', NAT, Lambda('s', NAT, Lambda(
               'h1', holds(leb_(b, a)), Lambda(
                   'h2', holds(app('ltb', sub_(a, b), s_)), step3))))))

    # x <= y gives x - k <= y - k.  Induction on k, generalising x and y;
    # at 0 both sides are `sub_zero` away from the hypothesis; at k + 1, x = 0
    # gives 0 on the left, and x = x' + 1 forces y = y' + 1 (y = 0 is
    # refuted), when both sides step down to the hypothesis at (k, x', y').
    X, Y, K = Var('x'), Var('y'), Var('k')
    M = Lambda('k', NAT, Pi('x', NAT, Pi('y', NAT, arrow(
        holds(leb_(X, Y)), holds(leb_(sub_(X, K), sub_(Y, K)))))))
    z0 = numeral(0)
    # base: carry h : x <= y along y = y - 0, then along x = x - 0
    h1 = app('Eq.ind', NAT, Y,
             Lambda('_w', NAT, Lambda('_e', eqn(Y, Var('_w')),
                                      holds(leb_(X, Var('_w'))))),
             Var('h'), sub_(Y, z0),
             app('symm', NAT, sub_(Y, z0), Y, app('sub_zero', Y)))
    h2 = app('Eq.ind', NAT, X,
             Lambda('_w', NAT, Lambda('_e', eqn(X, Var('_w')),
                                      holds(leb_(Var('_w'), sub_(Y, z0))))),
             h1, sub_(X, z0),
             app('symm', NAT, sub_(X, z0), X, app('sub_zero', X)))
    base = Lambda('x', NAT, Lambda('y', NAT, Lambda('h', holds(leb_(X, Y)),
                                                    h2)))
    x2, y2 = Var('x2'), Var('y2')
    Bx = Lambda('x', NAT, Pi('y', NAT, arrow(
        holds(leb_(X, Y)), holds(leb_(sub_(X, succ_(K)), sub_(Y, succ_(K)))))))
    By = Lambda('y', NAT, arrow(
        holds(leb_(succ_(x2), Y)),
        holds(leb_(sub_(succ_(x2), succ_(K)), sub_(Y, succ_(K))))))
    step = Lambda('k', NAT, Lambda('ih', App(M, K), app(
        'Nat.ind', Bx,
        # x = 0: 0 - (k+1) is 0, and 0 <= anything
        Lambda('y', NAT, Lambda('_h', holds(leb_(z0, Y)), yes)),
        Lambda('x2', NAT, Lambda('_i', App(Bx, x2), Lambda('y', NAT, app(
            'Nat.ind', By,
            Lambda('h', holds(leb_(succ_(x2), z0)),
                   app('absurd', holds(leb_(sub_(succ_(x2), succ_(K)),
                                            sub_(z0, succ_(K)))), Var('h'))),
            Lambda('y2', NAT, Lambda('_j', App(By, y2), Lambda(
                'h', holds(leb_(succ_(x2), succ_(y2))),
                app(Var('ih'), x2, y2, Var('h'))))),
            Y)))))))
    # a < b is a + 1 <= b by definition -- but by a definition the kernel
    # leaves folded when b is a literal too large to walk, so the edge that
    # reads a `<` fact as a `<=` one goes through this, checked once with
    # variables, where unfolding `ltb` costs nothing
    A_, B_ = Var('a'), Var('b')
    define(env, 'ltb_succ_leb',
           Pi('a', NAT, Pi('b', NAT, arrow(
               holds(app('ltb', A_, B_)), holds(leb_(succ_(A_), B_))))),
           Lambda('a', NAT, Lambda('b', NAT, Lambda(
               'h', holds(app('ltb', A_, B_)), Var('h')))))

    # 0 + n <= n, from add_zero_left: `0 + n` is not `n` by computation
    # (addition recurses on its second argument), and an integer sum with a
    # zero side -- `0 - x` for a negative x, split -- is exactly this
    N_ = Var('n')
    define(env, 'zero_add_le', Pi('n', NAT, holds(leb_(add_(z0, N_), N_))),
           Lambda('n', NAT, app(
               'Eq.ind', NAT, N_,
               Lambda('_w', NAT, Lambda('_e', eqn(N_, Var('_w')),
                                        holds(leb_(Var('_w'), N_)))),
               app('leb_refl', N_), add_(z0, N_),
               app('symm', NAT, add_(z0, N_), N_,
                   app('add_zero_left', N_)))))

    define(env, 'sub_le_sub_right',
           Pi('k', NAT, Pi('x', NAT, Pi('y', NAT, arrow(
               holds(leb_(X, Y)), holds(leb_(sub_(X, K), sub_(Y, K))))))),
           Lambda('k', NAT, app('Nat.ind', M, base, step, K)))

    # a Bool that went false, as `Holds (notb x)`
    x_ = Var('x')
    define(env, 'false_notb',
           Pi('x', BOOL, arrow(app('Eq', BOOL, x_, Var('false')),
                               holds(app('notb', x_)))),
           Lambda('x', BOOL, Lambda('h', app('Eq', BOOL, x_, Var('false')),
               app('Eq.ind', BOOL, Var('false'),
                   Lambda('z', BOOL, Lambda('_e', app('Eq', BOOL,
                                                      Var('false'), Var('z')),
                                            holds(app('notb', Var('z'))))),
                   yes, x_, app('eq_symm', BOOL, x_, Var('false'),
                                Var('h'))))))

    # u <= s and n <= s - u give u + n <= s: add_le_of_le_sub, turned round
    n_ = Var('n')
    define(env, 'add_le_of_le_sub_r',
           Pi('u', NAT, Pi('n', NAT, Pi('s', NAT, arrow(
               holds(leb_(u, s)),
               arrow(holds(leb_(n_, sub_(s, u))),
                     holds(leb_(add_(u, n_), s))))))),
           Lambda('u', NAT, Lambda('n', NAT, Lambda('s', NAT, Lambda(
               'h1', holds(leb_(u, s)), Lambda(
                   'h2', holds(leb_(n_, sub_(s, u))),
                   app('Eq.ind', NAT, add_(n_, u),
                       Lambda('_w', NAT, Lambda('_e', eqn(add_(n_, u),
                                                          Var('_w')),
                                                holds(leb_(Var('_w'), s)))),
                       app('add_le_of_le_sub', n_, u, s, Var('h1'),
                           Var('h2')),
                       add_(u, n_), app('add_comm', n_, u))))))))

    # A comparison refuted: b < a gives not (a <= b), b <= a gives not
    # (a < b).  By a dependent case on the comparison: where it came out
    # true, the two chain by leb_trans into x < x, which ltb_irrefl refutes.
    def refuted(name, g, lo, hi, chain_from, chain_to, irr):
        e = app('Eq', BOOL, g, Var('_x'))
        motive = Lambda('_x', BOOL, arrow(e, holds(app('notb', Var('_x')))))
        when_true = Lambda('_e', app('Eq', BOOL, g, Var('true')), app(
            'absurd', holds(app('notb', Var('true'))),
            app('ltb_irrefl', irr, chain_from(Var('_e')))))
        when_false = Lambda('_e', app('Eq', BOOL, g, Var('false')), yes)
        return app(app('Bool.ind', motive, when_true, when_false, g),
                   app('refl', BOOL, g))
    define(env, 'lt_not_le',
           Pi('a', NAT, Pi('b', NAT, arrow(holds(app('ltb', b, a)),
                                           holds(app('notb', leb_(a, b)))))),
           Lambda('a', NAT, Lambda('b', NAT, Lambda(
               'h', holds(app('ltb', b, a)),
               refuted('lt_not_le', leb_(a, b), None, None,
                       lambda e: app('leb_trans', succ_(b), a, b, Var('h'),
                                     e), None, b)))))
    define(env, 'le_not_lt',
           Pi('a', NAT, Pi('b', NAT, arrow(holds(leb_(b, a)),
                                           holds(app('notb',
                                                     app('ltb', a, b)))))),
           Lambda('a', NAT, Lambda('b', NAT, Lambda(
               'h', holds(leb_(b, a)),
               refuted('le_not_lt', app('ltb', a, b), None, None,
                       lambda e: app('leb_trans', succ_(a), b, a, e,
                                     Var('h')), None, a)))))

    # 0 < i gives i - 1 < i: what makes `xs[i - 1]` in bounds behind `i > 0`
    # and `i < xs.len()`.  At i = k + 1, `sub (k + 1) 1` is `sub k 0`, which
    # is k only once k is split.
    Mk = Lambda('k', NAT, holds(leb_(sub_(k_, numeral(0)), k_)))
    inner = app('Nat.ind', Mk, yes,
                Lambda('m', NAT, Lambda('_i', App(Mk, Var('m')),
                                        app('leb_refl', Var('m')))), k_)
    Mi1 = Lambda('i', NAT, arrow(holds(app('ltb', numeral(0), Var('i'))),
                                 holds(app('ltb', sub_(Var('i'), numeral(1)),
                                           Var('i')))))
    define(env, 'sub_one_lt',
           Pi('i', NAT, arrow(holds(app('ltb', numeral(0), Var('i'))),
                              holds(app('ltb', sub_(Var('i'), numeral(1)),
                                        Var('i'))))),
           Lambda('i', NAT, app(
               'Nat.ind', Mi1,
               Lambda('h', holds(app('ltb', numeral(0), numeral(0))),
                      app('absurd', holds(app('ltb', sub_(numeral(0),
                                                          numeral(1)),
                                                  numeral(0))), Var('h'))),
               Lambda('k', NAT, Lambda('_ih', App(Mi1, k_), Lambda(
                   'h', holds(app('ltb', numeral(0), succ_(k_))), inner))),
               Var('i'))))

    # -- a list of values of one integer type ---------------------------------
    listnat = app('List', NAT)
    m = Var('m')
    define(env, 'all_le', arrow(listnat, arrow(NAT, BOOL)),
           Lambda('xs', listnat, Lambda('m', NAT, app(
               'List.rec', NAT, Lambda('_', listnat, BOOL), Var('true'),
               Lambda('h', NAT, Lambda('t', listnat, Lambda('ih', BOOL, app(
                   'andb', leb_(Var('h'), m), Var('ih'))))),
               Var('xs')))))
    nth0 = lambda xs, i: app('nth', NAT, numeral(0), xs, i)
    all_ = lambda xs: app('all_le', xs, m)
    Mx = Lambda('xs', listnat, Pi('i', NAT, arrow(
        holds(all_(Var('xs'))), holds(leb_(nth0(Var('xs'), Var('i')), m)))))
    hd, tl = Var('h'), Var('t')
    cons_ = app('cons', NAT, hd, tl)
    Mi = Lambda('i', NAT, arrow(holds(all_(cons_)),
                                holds(leb_(nth0(cons_, Var('i')), m))))
    cons_case = Lambda('h', NAT, Lambda('t', listnat, Lambda(
        'ih', App(Mx, tl), Lambda('i', NAT, app(
            'Nat.ind', Mi,
            Lambda('H', holds(all_(cons_)),
                   app('andb_left', leb_(hd, m), all_(tl), Var('H'))),
            Lambda('i2', NAT, Lambda('_j', App(Mi, Var('i2')), Lambda(
                'H', holds(all_(cons_)),
                app(Var('ih'), Var('i2'),
                    app('andb_right', leb_(hd, m), all_(tl), Var('H')))))),
            Var('i'))))))
    define(env, 'nth_all_le',
           Pi('xs', listnat, Pi('m', NAT, Pi('i', NAT, arrow(
               holds(all_(Var('xs'))),
               holds(leb_(nth0(Var('xs'), Var('i')), m)))))),
           Lambda('xs', listnat, Lambda('m', NAT, app(
               'List.ind', NAT, Mx,
               Lambda('i', NAT, Lambda('_H', holds(all_(app('nil', NAT))),
                                       yes)),
               cons_case, Var('xs')))))


# ------------------------------------------------- types of the fragment

BYTES = App(Var('List'), NAT)          # a string is a list of bytes
STRS = App(Var('List'), BYTES)

TYPE_NAMES = {'Nat': NAT, 'Bool': BOOL, 'int': NAT, 'bool': BOOL,
              'Int': INT,
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

BINOPS = {ast.Add: 'add', ast.Sub: 'sub', ast.Mult: 'mul', ast.Mod: 'modb',
          ast.FloorDiv: 'divb'}
INT_BINOPS = {ast.Add: 'int_add', ast.Sub: 'int_sub', ast.Mult: 'int_mul'}
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
            return INT if self.is_int(node.left) or self.is_int(node.right) \
                else NAT
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return INT
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
                if node.func.id == 'Int':
                    return INT
                if node.func.id == 'all_le':
                    return BOOL
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

    def is_int(self, node):
        return same_type(self.type_of_expr(node), INT)

    def int_operand(self, node):
        """An operand of integer arithmetic: an `Int` as it is, a `Nat`
        as `Int.ofNat` of it, so `x - len(xs)` mixes as it would in Rust
        after a cast."""
        if self.is_int(node):
            return self.expr(node)
        return App(Var('Int.ofNat'), self.expr(node))

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

        if isinstance(node, ast.BinOp) and (self.is_int(node.left) or
                                            self.is_int(node.right)):
            op = INT_BINOPS.get(type(node.op))
            if op is None:
                self.fail(node, f"{type(node.op).__name__} on integers is "
                                f"not in this fragment yet")
            return app(op, self.int_operand(node.left),
                       self.int_operand(node.right))

        if isinstance(node, ast.BinOp):
            op = BINOPS.get(type(node.op))
            if op is None:
                self.fail(node, f"{type(node.op).__name__} has no meaning in "
                                f"this fragment")
            return app(op, self.expr(node.left), self.expr(node.right))

        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return app('int_neg', self.int_operand(node.operand))

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
            negate = isinstance(node.ops[0], ast.NotEq)
            entry = COMPARES.get(type(node.ops[0])) if not negate \
                else ('eqb', False)
            if entry is None:
                self.fail(node, f"{type(node.ops[0]).__name__} is not a "
                                f"decidable comparison here")
            name, flip = entry
            if self.is_int(node.left) or self.is_int(node.comparators[0]):
                name = 'int_' + name
                left = self.int_operand(node.left)
                right = self.int_operand(node.comparators[0])
            else:
                left = self.expr(node.left)
                right = self.expr(node.comparators[0])
            if flip:
                left, right = right, left
            out = app(name, left, right)
            return app('notb', out) if negate else out

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
            if name == 'Int':
                # `Int(5)`, `Int(-5)`: an integer literal, as the Rust lift
                # writes one wherever the Rust type is signed
                a = node.args[0] if len(node.args) == 1 else None
                if isinstance(a, ast.UnaryOp) and \
                        isinstance(a.op, ast.USub) and \
                        isinstance(a.operand, ast.Constant):
                    return int_literal(-a.operand.value)
                if isinstance(a, ast.Constant) and isinstance(a.value, int):
                    return int_literal(a.value)
                self.fail(node, "Int(..) takes an integer literal")
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
            if name == 'all_le':
                # every element of an array is at most a bound: the range
                # of an integer slice, which the Rust lift states as a fact
                if len(node.args) != 2:
                    self.fail(node, "all_le takes an array and a bound")
                return app('all_le', self.expr(node.args[0]),
                           self.expr(node.args[1]))
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
            self.fail(stmt, "a `return` inside `if` reached the lowering. "
                            "desugar_returns should have rewritten it into a "
                            "first-wins assignment before this point, so this "
                            "is a bug in that pass rather than in the input.")
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
            self.fail(stmt, "a `return` inside a loop reached the lowering. "
                            "desugar_returns should have rewritten it before "
                            "this point, so this is a bug in that pass.")
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
            self.fail(stmt, "a `return` inside a loop reached the lowering. "
                            "desugar_returns should have rewritten it before "
                            "this point, so this is a bug in that pass.")
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


DONE_FLAG = '_returned'
RESULT_VAR = '_return_value'


def _returns_in(stmts):
    """Every `return` in a block, including nested ones."""
    out = []
    for stmt in stmts:
        if isinstance(stmt, ast.Return):
            out.append(stmt)
        elif isinstance(stmt, (ast.If, ast.For, ast.While)):
            out.extend(_returns_in(stmt.body))
            out.extend(_returns_in(getattr(stmt, 'orelse', [])))
    return out


def _names_outside_asserts(tree):
    """Every name the body mentions anywhere but inside an `assert`."""
    found = set()

    def visit(node):
        if isinstance(node, ast.Assert):
            return
        if isinstance(node, ast.Name):
            found.add(node.id)
        for child in ast.iter_child_nodes(node):
            visit(child)

    visit(tree)
    return found


def _free_names(node):
    """Names a fragment reads as values.

    Anything in call position is excluded: `len(names)` reads `names`, while
    `len` is the prelude's and is bound everywhere.  Counting it would make
    every `return` look like it depended on a variable the body assigns.
    """
    called = {n.func.id for n in ast.walk(node)
              if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)}
    return {n.id for n in ast.walk(node)
            if isinstance(n, ast.Name)} - called


def _rewrite_returns(stmts, final, seen):
    """Replace every `return` but `final` with a first-wins assignment."""
    out = []
    for stmt in stmts:
        if isinstance(stmt, ast.Return) and stmt is not final:
            # `_return_value = _return_value if _returned else e` keeps the
            # first return rather than the last, without needing a branch:
            # the join an `if` would require is the whole reason early
            # returns were refused.
            keep = ast.IfExp(test=ast.Name(id=DONE_FLAG, ctx=ast.Load()),
                             body=ast.Name(id=RESULT_VAR, ctx=ast.Load()),
                             orelse=stmt.value)
            out.append(ast.Assign(
                targets=[ast.Name(id=RESULT_VAR, ctx=ast.Store())], value=keep))
            out.append(ast.Assign(
                targets=[ast.Name(id=DONE_FLAG, ctx=ast.Store())],
                value=ast.Constant(value=True)))
            seen.append(stmt)
            continue
        if isinstance(stmt, (ast.If, ast.For, ast.While)):
            stmt.body = _rewrite_returns(stmt.body, final, seen)
            if getattr(stmt, 'orelse', None):
                stmt.orelse = _rewrite_returns(stmt.orelse, final, seen)
        out.append(stmt)
    return out


def _placeholder_for(tree):
    """A typed value for `_return_value` to hold before one is chosen.

    Never observed: every path that sets the flag overwrites it first, and
    every path that does not ignores it.  So the only thing required of it is
    that it typecheck at the declared return type, which is why it is chosen
    from the annotation rather than from any `return` in the body.

    Taking it from the body instead -- the obvious idea -- does not work: a
    function whose returns all read variables the body assigns, which is most
    of them, would have nothing to start from.
    """
    annotation = tree.returns
    name = None
    if isinstance(annotation, ast.Constant) and isinstance(annotation.value, str):
        name = annotation.value
    elif isinstance(annotation, ast.Name):
        name = annotation.id
    if name is None:
        name = 'Nat'                      # read_procedure's own default
    if name not in TYPE_NAMES:
        raise ContractError(
            f"{tree.name}: an early `return` needs a return annotation whose "
            f"type has a value to stand in until one is chosen, and "
            f"{name!r} is not one (known: {', '.join(sorted(TYPE_NAMES))})")
    target = TYPE_NAMES[name]
    if same_type(target, BOOL):
        return ast.Constant(value=False), name
    if same_type(target, NAT):
        return ast.Constant(value=0), name
    if same_type(target, INT):
        return ast.Call(func=ast.Name(id='Int', ctx=ast.Load()),
                        args=[ast.Constant(value=0)], keywords=[]), name
    return ast.List(elts=[], ctx=ast.Load()), name


SEQ_VAR = '_seq'
POS_VAR = '_pos'


def _is_range_call(node):
    return (isinstance(node, ast.Call) and isinstance(node.func, ast.Name)
            and node.func.id == 'range')


def _marker(stmt, which):
    """The expression inside `assert invariant(e)` / `assert variant(e)`."""
    if (isinstance(stmt, ast.Assert) and isinstance(stmt.test, ast.Call)
            and isinstance(stmt.test.func, ast.Name)
            and stmt.test.func.id == which and len(stmt.test.args) == 1):
        return stmt.test.args[0]
    return None


def _name(id_, ctx=ast.Load):
    return ast.Name(id=id_, ctx=ctx())


def _call(fn, *args):
    return ast.Call(func=_name(fn), args=list(args), keywords=[])


def _assert_marker(which, expr):
    return ast.Assert(test=_call(which, expr), msg=None)


def desugar_for(body, where, depth=0):
    r"""Rewrite `for x in xs` over a list into the `while` it always was.

    `for i in range(n)` lowers to `Nat.rec` and stays as it is.  Iterating a
    list is different only in that the bound is the list's length and the
    element is read out on each pass, so it becomes:

        for url in parts:                 _seq = parts
            body                          _pos = 0
                                          url = _seq[0]
                                          while _pos < len(_seq):
                                              assert variant(len(_seq) - _pos)
                                              assert invariant(_pos <= len(_seq)
                                                               and <yours>)
                                              url = _seq[_pos]
                                              body
                                              _pos = _pos + 1

    and the whole apparatus that `while` already has -- the variant, the
    invariant, `loop_obligations`, `invariant_at_exit` -- applies unchanged.
    That is the point of doing this as a rewrite: the proofs about `while`
    loops are the proofs about `for` loops, with nothing new to trust.

    The variant is supplied, since a list is finite and the text does not
    need to say so.  The invariant's first conjunct is supplied too, because
    `_pos <= len(_seq)` is what makes `_pos == len(_seq)` available at exit,
    and every postcondition about the result argues from that.  An `assert
    invariant(...)` of your own at the top of the body is conjoined after it,
    and may mention `_pos` -- a counter of your own that walks in step with
    the list, as `i` does in `accepted`, is related to the loop's progress by
    saying `i == _pos`, and there is no other way to say it.

    `url = _seq[0]` before the loop is a typed placeholder, never observed:
    the first pass overwrites it before the body reads it.  It is there
    because the lowering asks every variable a loop assigns to have a value
    going in, so that the fold has a starting state.

    Nesting one list loop inside another is refused rather than supported
    with renaming, since the names are what an invariant refers to.
    """
    out = []
    for stmt in body:
        if isinstance(stmt, ast.For) and not _is_range_call(stmt.iter):
            if depth:
                raise ContractError(
                    f"{where}: a `for` over a list inside another is not "
                    f"supported: both would want to be `{POS_VAR}`, and the "
                    f"invariant would not know which it was talking about")
            if stmt.orelse:
                raise ContractError(f"{where}: `for ... else` has no meaning "
                                    f"here")
            if not isinstance(stmt.target, ast.Name):
                raise ContractError(f"{where}: the loop variable must be a "
                                    f"plain name")
            elem = stmt.target.id
            inner = list(stmt.body)
            user_inv = None
            if inner and _marker(inner[0], 'invariant') is not None:
                user_inv = _marker(inner[0], 'invariant')
                inner = inner[1:]
            if inner and _marker(inner[0], 'variant') is not None:
                raise ContractError(
                    f"{where}: a `for` over a list needs no variant; the "
                    f"length of the list is the bound and it is supplied")
            inner = desugar_for(inner, where, depth + 1)

            bound = _call('len', _name(SEQ_VAR))
            in_range = ast.Compare(left=_name(POS_VAR), ops=[ast.LtE()],
                                   comparators=[bound])
            inv = in_range if user_inv is None else ast.BoolOp(
                op=ast.And(), values=[in_range, user_inv])
            read = ast.Assign(
                targets=[_name(elem, ast.Store)],
                value=ast.Subscript(value=_name(SEQ_VAR), slice=_name(POS_VAR),
                                    ctx=ast.Load()))
            advance = ast.Assign(
                targets=[_name(POS_VAR, ast.Store)],
                value=ast.BinOp(left=_name(POS_VAR), op=ast.Add(),
                                right=ast.Constant(value=1)))
            loop = ast.While(
                test=ast.Compare(left=_name(POS_VAR), ops=[ast.Lt()],
                                 comparators=[copy.deepcopy(bound)]),
                body=[_assert_marker('variant',
                                     ast.BinOp(left=copy.deepcopy(bound),
                                               op=ast.Sub(),
                                               right=_name(POS_VAR))),
                      _assert_marker('invariant', inv),
                      read] + inner + [advance],
                orelse=[])
            out.extend([
                ast.Assign(targets=[_name(SEQ_VAR, ast.Store)],
                           value=stmt.iter),
                ast.Assign(targets=[_name(POS_VAR, ast.Store)],
                           value=ast.Constant(value=0)),
                ast.Assign(targets=[_name(elem, ast.Store)],
                           value=ast.Subscript(value=_name(SEQ_VAR),
                                               slice=ast.Constant(value=0),
                                               ctx=ast.Load())),
                loop,
            ])
            continue
        if isinstance(stmt, (ast.If, ast.For, ast.While)):
            stmt.body = desugar_for(stmt.body, where, depth)
            if getattr(stmt, 'orelse', None):
                stmt.orelse = desugar_for(stmt.orelse, where, depth)
        out.append(stmt)
    return out


def desugar_append(body, where):
    r"""`xs.append(x)` is `xs = snoc(xs, x)`.

    A store-passing lowering has no mutation, so a method that mutates has to
    become an assignment.  This is the only one there is: Python's `append`
    pushes one element, which is `snoc`, and not the prelude's `append`,
    which is concatenation and takes two lists.  Written here as a rewrite
    so the model may say what the kernel says.
    """
    out = []
    for stmt in body:
        if (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Call)
                and isinstance(stmt.value.func, ast.Attribute)
                and stmt.value.func.attr == 'append'):
            call = stmt.value
            if not isinstance(call.func.value, ast.Name):
                raise ContractError(f"{where}: `.append` on something other "
                                    f"than a plain variable has no lowering")
            if len(call.args) != 1 or call.keywords:
                raise ContractError(f"{where}: `.append` takes one argument")
            target = call.func.value.id
            out.append(ast.copy_location(ast.Assign(
                targets=[_name(target, ast.Store)],
                value=_call('snoc', _name(target), call.args[0])), stmt))
            continue
        if isinstance(stmt, (ast.If, ast.For, ast.While)):
            stmt.body = desugar_append(stmt.body, where)
            if getattr(stmt, 'orelse', None):
                stmt.orelse = desugar_append(stmt.orelse, where)
        out.append(stmt)
    return out


def desugar_returns(tree, params):
    r"""Rewrite early `return`s into a first-wins accumulator.

    `return` was refused anywhere but the end of a body, because an `if` that
    returns on one side has no store to join and a loop that returns has no
    way to stop a fold.  Both objections are about *control*, and this
    fragment has none to speak of: every expression is pure and every function
    total, loops are folds with a variant, and nothing raises.  So a statement
    after an early return may simply run.  Whatever it computes is discarded
    by the final choice, and the transform costs two variables rather than a
    new lowering:

        def scheme_of(names, url):          def scheme_of(names, url):
            idx = find(url, 58)                 _returned = False
            if idx == 0:                        _return_value = len(names)
                return len(names)               idx = find(url, 58)
            i = 0                               if idx == 0:
            while i < len(names):                   _return_value = ...
                if eqs(names[i], head):             _returned = True
                    return i                    ...
                i = i + 1
            return len(names)

    The loop condition is deliberately left alone.  Adding `and not
    _returned` would make the loop stop early, and then the pass on which the
    flag was set would not decrease the variant, so a loop that plainly
    terminates would fail its own termination obligation.  Running the fold
    out to its bound costs nothing a fold does not already cost, and keeps
    the variant honest.

    `_return_value` needs a value before the first early return, because the
    choice above reads it.  It is initialised from the first `return` whose
    expression can be evaluated at entry -- one mentioning only parameters and
    literals.  That value is never observed: it is replaced on every path that
    sets the flag, and ignored on every path that does not.  When no return
    qualifies, this raises rather than guessing, since the alternative is an
    initialiser that reads a variable the body has not written yet.
    """
    body = tree.body
    returns = _returns_in(body)
    final = body[-1] if body and isinstance(body[-1], ast.Return) else None
    early = [r for r in returns if r is not final]
    if not early:
        return tree                       # untouched: the existing shape

    if final is None:
        raise ContractError(
            f"{tree.name}: a body with an early `return` must still end in "
            f"one, so there is a value on the path that falls through")

    # The two names are reserved against the body *writing* them.  An
    # `assert invariant(...)` may read `_return_value`, as one may read
    # `_pos` from the `for` lowering: a postcondition about a value returned
    # early from a loop is provable only if the invariant can carry a bound
    # on the accumulator that value lands in.
    for name in (DONE_FLAG, RESULT_VAR):
        if name in _names_outside_asserts(tree):
            raise ContractError(
                f"{tree.name}: '{name}' is reserved for lowering early "
                f"returns; please rename it")

    seed = _placeholder_for(tree)

    seen = []
    rewritten = _rewrite_returns(list(body), final, seen)
    # `return e` at the end becomes the same first-wins choice.
    final_choice = ast.Return(value=ast.IfExp(
        test=ast.Name(id=DONE_FLAG, ctx=ast.Load()),
        body=ast.Name(id=RESULT_VAR, ctx=ast.Load()),
        orelse=final.value))
    rewritten[-1] = final_choice

    placeholder, type_name = seed
    prologue = [
        ast.Assign(targets=[ast.Name(id=DONE_FLAG, ctx=ast.Store())],
                   value=ast.Constant(value=False)),
        # Annotated, because an empty list carries no element type of its own
        # -- the same reason schemes.py writes `out: 'Array' = []`.
        ast.AnnAssign(target=ast.Name(id=RESULT_VAR, ctx=ast.Store()),
                      annotation=ast.Constant(value=type_name),
                      value=copy.deepcopy(placeholder), simple=1),
    ]

    # The prologue goes after the docstring and after the leading asserts,
    # not at the very top: those asserts are the precondition, and
    # read_procedure lifts them by looking at the front of the body.  An
    # assignment in front of them would turn the contract into "an assertion
    # in the middle", which is a different thing and refused.
    at = 0
    while at < len(rewritten):
        stmt = rewritten[at]
        docstring = (isinstance(stmt, ast.Expr)
                     and isinstance(stmt.value, ast.Constant)
                     and isinstance(stmt.value.value, str))
        if docstring or isinstance(stmt, ast.Assert):
            at += 1
            continue
        break
    tree.body = rewritten[:at] + prologue + rewritten[at:]
    ast.fix_missing_locations(tree)
    return tree


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

    # Rewrites, before anything is lowered, so the rest of this function sees
    # the shapes it has always seen.  Order matters only in that a `for`
    # over a list becomes a `while` first, so a `return` inside it is then
    # a return inside a while, which the next pass already handles.
    for node in ast.walk(tree):
        if not isinstance(node, ast.Name):
            continue
        if node.id == SEQ_VAR or (node.id == POS_VAR
                                  and isinstance(node.ctx, ast.Store)):
            raise ContractError(
                f"{tree.name}: '{node.id}' is reserved for lowering a `for` "
                f"over a list -- {POS_VAR} may be read in an invariant, "
                f"nothing else; please rename it")
    tree.body = desugar_append(tree.body, tree.name)
    tree.body = desugar_for(tree.body, tree.name)
    ast.fix_missing_locations(tree)
    tree = desugar_returns(tree, [name for name, _ in params])

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


def first_difference(left, right, env=None, path=''):
    """Where two terms first differ, as (path, left part, right part).

    A mismatch between a proof's type and the goal it was meant to have is
    reported by the kernel as two terms of a few thousand characters, and
    reading them side by side is not a diagnosis.  This walks them together
    and stops at the first place they part company, which usually names the
    mistake outright.  None when they agree.
    """
    if env is not None and L.definitionally_equal(left, right, env):
        return None
    if type(left) is not type(right):
        return (path, left, right)
    if isinstance(left, App):
        for side, a, b in (('fn', left.func, right.func),
                           ('arg', left.arg, right.arg)):
            found = first_difference(a, b, env, path + '/' + side)
            if found is not None:
                return found
        return None
    if isinstance(left, Binder):
        for side, a, b in (('type', left.var_type, right.var_type),
                           ('body', left.body, right.body)):
            found = first_difference(a, b, env, path + '/' + side)
            if found is not None:
                return found
        return None
    if left != right:
        return (path, left, right)
    return None


def structural_proof(env, claim):
    """A proof of `Holds claim` from its shape, or None.

    Takes `andb` and `orb` apart, and settles a leaf by computation or by
    reflexivity -- `leb x x` and `eqb x x` hold for any x and do not reduce
    to `true`.  Builds a term and type-checks nothing: the caller may be
    inside lambdas that bind variables the ambient environment has never
    heard of, which is the situation at every leaf of a loop proof.
    """
    claim = reduce_decided_ites(claim)
    head, args = L.spine(claim)
    if not isinstance(head, Var):
        return None
    if head.name == 'andb' and len(args) == 2:
        left = structural_proof(env, args[0])
        right = structural_proof(env, args[1])
        if left is None or right is None:
            return None
        return app('andb_both', args[0], args[1], left, right)
    if head.name == 'orb' and len(args) == 2:
        left = structural_proof(env, args[0])
        if left is not None:
            return app('holds_orb_left', args[0], args[1], left)
        right = structural_proof(env, args[1])
        if right is not None:
            return app('holds_orb_right', args[0], args[1], right)
        return None
    if normalize(claim, env) == Var('true'):
        return app('refl', BOOL, Var('true'))
    if (head.name in ('leb', 'eqb') and len(args) == 2
            and L.definitionally_equal(args[0], args[1], env)):
        return app(head.name + '_refl', args[0])
    return None


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
        # A comparison of a term with itself is true without computing it:
        # `leb x x` and `eqb x x` hold for any x, and a search that ran off
        # the end of a list returns the very length it is bounded by.  The
        # reflexivity lemmas settle these where normalisation cannot, and
        # the search goes under `andb`, since an invariant is a conjunction
        # and only one half is usually the stuck one.
        found = structural_proof(env, args[-1])
        if found is not None:
            for name, ty, _ in reversed(binders):
                found = Lambda(name, ty, found)
            actual = type_check(env, found)
            if not L.definitionally_equal(goal, actual, env):
                raise TheoremError(f"proved {readable(actual)}, "
                                   f"not {readable(goal)}")
            if verbose:
                print("  proved by reflexivity")
            return found
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


class Fields(dict):
    """The values a case split bound, by name or by position.

    Positional access still works, but `f['current']` says what it means and
    `f[3]` does not -- and with a loop state nested as `Prod A (Prod B C)` the
    index that happens to be right is an accident of how the pack nests.
    """

    def __getitem__(self, key):
        if isinstance(key, int):
            return list(self.values())[key]
        if key not in self:
            raise ContractError(
                f"there is no '{key}' here; this split bound "
                f"{', '.join(self) or 'nothing'}")
        return dict.__getitem__(self, key)


def unfold(term, env, names):
    r"""Expand just the named definitions, leaving everything else alone.

    `normalize` is all or nothing: ask it to look inside `accepted.inv1` and
    it will also unfold `andb` and `ite` into the recursors they stand for,
    at which point there is no conjunction left to take apart and no `ite`
    left to split on.  Naming what to expand keeps the shape a proof is
    written against.
    """
    head, args = L.spine(term)
    args = [unfold(a, env, names) for a in args]
    if isinstance(head, Var) and head.name in names:
        value = L.value_of(env, head.name)
        if value is not None:
            out = value
            for arg in args:
                out = App(out, arg)
            return unfold(normalize(out, None), env, names)   # beta only
    if isinstance(term, Binder):
        return term.rebuild(unfold(term.var_type, env, names),
                            unfold(term.body, env, names))
    out = head
    for arg in args:
        out = App(out, arg)
    return out


def first_ite(term):
    """The condition of the first `ite` in a term, or None."""
    head, args = L.spine(term)
    if isinstance(head, Var) and head.name == 'ite' and len(args) >= 2:
        return args[1]
    if isinstance(term, App):
        return first_ite(term.func) or first_ite(term.arg)
    if isinstance(term, Binder):
        return first_ite(term.var_type) or first_ite(term.body)
    return None


def by_bool(env, goal, scrutinee, when_true, when_false):
    r"""Case split on a Bool subterm of a goal that is not a variable.

    A loop body with an `if` in it leaves an `ite` in the state, and the
    condition is some computation rather than something already bound, so a
    split on the state does not touch it.  Abstracting the term out of the
    goal gives a motive, and then `Bool.ind` splits on it like any other.
    """
    if scrutinee is None:
        scrutinee = first_ite(goal)
        if scrutinee is None:
            raise ContractError(f"there is no `ite` in {readable(goal)} to "
                                f"split on; name the condition explicitly")
    motive = Lambda('_x', BOOL, replace_subterm(goal, scrutinee, Var('_x')))
    return app('Bool.ind', motive, when_true, when_false, scrutinee)


def by_bool_with_evidence(env, goal, scrutinee, when_true, when_false,
                          label='_ev'):
    r"""Case split on a Bool term, giving each branch the equation it won.

    `by_bool` abstracts the term out of the goal and applies `Bool.ind`, so
    a branch knows the goal has `true` written into it but not *that the
    term is true*.  That is enough whenever the goal's own occurrences are
    the thing being decided, and not enough the moment the branch has to
    prove something about an occurrence that only appeared after the `ite`
    reduced -- a search that returns `i` must then show the guards hold at
    `i`, and those copies were never substituted.

    Here the motive carries the equation, so `when_true` is called with a
    proof of `Eq Bool scrutinee true` in scope and `when_false` with one of
    `Eq Bool scrutinee false`.  Both are callables taking that proof term.
    The whole is applied to `refl`, which is what discharges the equation
    for the branch actually taken.
    """
    if scrutinee is None:
        scrutinee = first_ite(goal)
        if scrutinee is None:
            raise ContractError(f"there is no `ite` in {readable(goal)} to "
                                f"split on; name the condition explicitly")
    motive = Lambda('_x', BOOL, arrow(
        app('Eq', BOOL, scrutinee, Var('_x')),
        replace_subterm(goal, scrutinee, Var('_x'))))
    # `label` must differ between nested splits: an inner binder called
    # `_ev` would shadow the outer one, and the evidence a leaf reaches for
    # would be the wrong guard's equation, or ill-typed.
    branch = lambda side, body: Lambda(
        label, app('Eq', BOOL, scrutinee, Var(side)), body(Var(label)))
    return app(app('Bool.ind', motive,
                   branch('true', when_true), branch('false', when_false),
                   scrutinee),
               app('refl', BOOL, scrutinee))


def _first_open_ite(term):
    """The condition of the first `ite` not already decided by a literal.

    Innermost first: a guard written in terms of another -- `accept` tests
    `eqb (reg_class_ok cls) 0`, and `reg_class_ok` is itself an `ite` on
    `leb cls 3` -- computes once the inner one is decided, and splitting
    the outer one as an atom would leave `leb cls 3` open everywhere else
    it occurs.
    """
    head, args = L.spine(term)
    if (isinstance(head, Var) and head.name == 'ite' and len(args) >= 2
            and args[1] not in (Var('true'), Var('false'))):
        inner = _first_open_ite(args[1])
        if inner is not None:
            return inner
        return args[1] if not L.has_loose_bound(args[1]) else None
    if isinstance(term, App):
        return _first_open_ite(term.func) or _first_open_ite(term.arg)
    if isinstance(term, Binder):
        # only the binder's type: its body is abstracted, so a guard found
        # in there carries de Bruijn indices that mean nothing outside, and
        # splitting on it would quantify over a variable that does not exist
        return _first_open_ite(term.var_type)
    return None


def by_every_bool(env, goal, unfolding=(), limit=16, verbose=False):
    r"""Prove a goal by splitting on every `ite` it contains, then computing.

    A function that is a chain of guards -- `if x == 0: return 6`, and so on
    -- lowers to a tower of `ite`s over conditions on its parameters, and a
    claim about its result is settled by nothing but which way each one
    went.  `by_bool` splits one; this splits until none is left and then asks
    `discharge`, which is `refl` once the claim is closed.  The limit is a
    ceiling on how many times it will split before deciding the goal is not
    the finite kind this was for.

    `unfolding` names the definitions to open -- the procedure itself, since
    its `ite`s are behind its name -- and only those: normalising would turn
    every `ite` into the recursor it stands for and leave nothing to split.

    Each branch goal is the original with `true` or `false` written in for
    one condition, everywhere it occurs, so the recursion is on the number of
    undecided conditions.  Nothing is assumed about them: `x == 0` and
    `x == 1` are split independently, and their four combinations are four
    cases, two of them vacuous and all of them checked.
    """
    binders, claim = peel(goal)
    claim = unfold(claim, env, set(unfolding))

    def close(term):
        for name, ty, _ in reversed(binders):
            term = Pi(name, ty, L.abstract(term, name))
        return term

    def prove_claim(claim, depth):
        # A guard that computes once earlier splits are written in --
        # `eqb (ite true 1 0) 0` -- is decided, not split.  Splitting it
        # would ask for a proof of the branch computation rules out, and
        # there is none; writing its value in is a definitional step the
        # final `prove` checks.
        while True:
            scrutinee = _first_open_ite(claim)
            if scrutinee is None:
                break
            decided = normalize(scrutinee, env)
            if decided not in (Var('true'), Var('false')):
                break
            claim = replace_subterm(claim, scrutinee, decided)
        if scrutinee is None:
            whole = discharge(close(claim), env, verbose=verbose)
            return app(whole, *[Var(n) for n, _, _ in binders])
        if depth >= limit:
            raise TheoremError(f"more than {limit} conditions to split on; "
                               f"this is not the finite kind of claim "
                               f"by_every_bool is for")
        when_true = prove_claim(
            replace_subterm(claim, scrutinee, Var('true')), depth + 1)
        when_false = prove_claim(
            replace_subterm(claim, scrutinee, Var('false')), depth + 1)
        motive = Lambda('_x', BOOL, replace_subterm(claim, scrutinee, Var('_x')))
        return app('Bool.ind', motive, when_true, when_false, scrutinee)

    proof = prove_claim(claim, 0)
    for name, ty, _ in reversed(binders):
        proof = Lambda(name, ty, L.abstract(proof, name))
    return prove(goal, proof, env, verbose=verbose)


def _simplify_bool(term):
    """Rewrite the Boolean steps that compute on a symbolic argument --
    `andb true x` is `x`, `ite false a b` is `b` -- and nothing else, so the
    result is definitionally the input and a proof of one is a proof of the
    other."""
    while True:
        head, args = L.spine(term)
        if isinstance(head, Var):
            n = head.name
            if n == 'Holds' and len(args) == 1:
                return app('Holds', _simplify_bool(args[0]))
            if n == 'andb' and len(args) == 2:
                a = _simplify_bool(args[0])
                if a == Var('true'):
                    term = args[1]
                    continue
                if a == Var('false'):
                    return Var('false')
            if n == 'orb' and len(args) == 2:
                a = _simplify_bool(args[0])
                if a == Var('true'):
                    return Var('true')
                if a == Var('false'):
                    term = args[1]
                    continue
            if n == 'sub' and len(args) == 2 and args[1] == numeral(1) \
                    and _is(args[0], 'succ', 1) is not None:
                # (x + 1) - 1 is x - 0 by computation
                return app('sub', _simplify_bool(args[0].arg), numeral(0))
            if n == 'add' and len(args) == 2 and args[1] == numeral(1):
                # `x + 1` is `succ x` by computation (`add` recurses on its
                # second argument), and `x < y` is `succ x <= y`: one key
                # for the counter step and the strict bound it came from
                return App(Var('succ'), _simplify_bool(args[0]))
            if n == 'notb' and len(args) == 1:
                a = _simplify_bool(args[0])
                if a == Var('true'):
                    return Var('false')
                if a == Var('false'):
                    return Var('true')
            if n == 'ite' and len(args) == 4:
                c = _simplify_bool(args[1])
                if c in (Var('true'), Var('false')):
                    term = args[2] if c == Var('true') else args[3]
                    continue
        # nothing at the head: the same steps inside the arguments, where
        # a decided `ite Nat true a b` hides a value from the bounds search
        if isinstance(term, App):
            head, args = L.spine(term)
            new = [_simplify_bool(a) for a in args]
            if any(x is not y for x, y in zip(new, args)):
                return app(head, *new)
        return term


def _is(term, name, arity):
    head, args = L.spine(term)
    if isinstance(head, Var) and head.name == name and len(args) == arity:
        return args
    return None


def _succ_of(x):
    """`succ x`, written as the literal when x is one: `1 <= i` and
    `succ 0 <= i` are one fact, and the search compares keys."""
    k = L.as_numeral(x)
    return numeral(k + 1) if k is not None else App(Var('succ'), x)


def _le_edges(facts):
    """Every `x <= y` the facts give, as (x, y, proof of Holds (leb x y)).

    A fact is (proposition, proof).  What is read: `x <= y` itself, `x < y`
    (both as `x <= y` and as `x + 1 <= y`, which is what it is), a guard
    that went false either way round, `x == y` in both directions, and both
    halves of a conjunction."""
    edges, todo = [], list(facts)
    while todo:
        prop, pf = todo.pop()
        body = _is(prop, 'Holds', 1)
        if body is not None:
            b = _simplify_bool(body[0])
            if (args := _is(b, 'leb', 2)) is not None:
                edges.append((args[0], args[1], pf))
            elif (args := _is(b, 'ltb', 2)) is not None:
                x, y = args
                edges.append((_succ_of(x), y, app('ltb_succ_leb', x, y, pf)))
                edges.append((x, y, app('lt_le', x, y, pf)))
            elif (args := _is(b, 'eqb', 2)) is not None:
                x, y = args
                edges.append((x, y, app('andb_left', app('leb', x, y),
                                        app('leb', y, x), pf)))
                edges.append((y, x, app('andb_right', app('leb', x, y),
                                        app('leb', y, x), pf)))
            elif (args := _is(b, 'andb', 2)) is not None:
                todo.append((app('Holds', args[0]),
                             app('andb_left', args[0], args[1], pf)))
                todo.append((app('Holds', args[1]),
                             app('andb_right', args[0], args[1], pf)))
            elif (args := _is(b, 'notb', 1)) is not None:
                inner = _simplify_bool(args[0])
                if (xy := _is(inner, 'ltb', 2)) is not None:
                    edges.append((xy[1], xy[0],
                                  app('ltb_false_leb', xy[0], xy[1], pf)))
            continue
        eq = _is(prop, 'Eq', 3)
        if eq is not None and eq[0] == BOOL and eq[2] == Var('false'):
            g = eq[1]
            if (xy := _is(g, 'ltb', 2)) is not None:
                edges.append((xy[1], xy[0], app('not_lt_le', xy[0], xy[1], pf)))
            elif (xy := _is(g, 'leb', 2)) is not None:
                x, y = xy
                lt = app('not_le_lt', x, y, pf)
                edges.append((_succ_of(y), x, app('ltb_succ_leb', y, x, lt)))
                edges.append((y, x, app('lt_le', y, x, lt)))
    return edges


def _conjuncts(facts):
    """The facts, with every `Holds (andb a b)` also given as `Holds a` and
    `Holds b`: an invariant is a conjunction, and a leaf wants a part."""
    out, todo = [], list(facts)
    while todo:
        prop, pf = todo.pop()
        out.append((prop, pf))
        body = _is(prop, 'Holds', 1)
        if body is None:
            continue
        both = _is(_simplify_bool(body[0]), 'andb', 2)
        if both is not None:
            todo.append((app('Holds', both[0]),
                         app('andb_left', both[0], both[1], pf)))
            todo.append((app('Holds', both[1]),
                         app('andb_right', both[0], both[1], pf)))
    return out


def _subterms(term):
    out, stack = [], [term]
    while stack:
        t = stack.pop()
        out.append(t)
        if isinstance(t, App):
            stack.append(t.func)
            stack.append(t.arg)
    return out


def _prove_le(env, a, b, edges, ranges, depth=6):
    r"""A proof of `Holds (leb a b)` from the edges, or None.

    A search from `a` upward: each step is a fact `x <= y`, a range fact
    (`nth xs i <= m` from `all_le xs m`), or the checked-addition rule
    (`u + n <= s` from `n <= s` and `u <= s - n`), and the steps are joined
    by `leb_trans`.  It stops at `b`, at anything that computes to be below
    `b`, or after `depth` steps.  Every term it returns is checked again by
    the kernel as part of the whole proof, so a wrong step here is refused
    there, never believed."""
    true = Var('true')

    def closes(x):
        """A proof of x <= b needing no search, or None."""
        if x.key() == b.key():
            return app('leb_refl', x)
        try:
            if normalize(app('leb', x, b), env) == true:
                return app('refl', BOOL, true)
        except L.KernelError:
            pass
        # x <= y + 1 from x <= y, by leb_succ
        bs1 = _is(b, 'succ', 1)
        if bs1 is not None and depth > 1:
            below = _prove_le(env, x, bs1[0], edges, ranges, depth - 1)
            if below is not None:
                return app('leb_trans', x, bs1[0], b, below,
                           app('leb_succ', bs1[0]))
        # succ x <= succ y is x <= y, by leb's own step
        xs_, bs_ = _is(x, 'succ', 1), _is(b, 'succ', 1)
        if xs_ is not None and bs_ is not None and depth > 1:
            inner = _prove_le(env, xs_[0], bs_[0], edges, ranges, depth - 1)
            if inner is not None:
                return inner
        # a sum below a sum, term by term
        xa, ba = _is(x, 'add', 2), _is(b, 'add', 2)
        if xa is not None and ba is not None and depth > 1:
            p1 = _prove_le(env, xa[0], ba[0], edges, ranges, depth - 1)
            p2 = p1 and _prove_le(env, xa[1], ba[1], edges, ranges,
                                  depth - 1)
            if p1 is not None and p2 is not None:
                return app('add_le_add', xa[0], ba[0], xa[1], ba[1], p1, p2)
        return None

    def steps(x):
        for lo, hi, pf in edges:
            if lo.key() == x.key():
                yield hi, pf
        # succ x <= succ y from x <= y: the same proof, by leb's own step
        inner = _is(x, 'succ', 1)
        if inner is not None:
            for lo, hi, pf in edges:
                if lo.key() == inner[0].key():
                    yield App(Var('succ'), hi), pf
        for xs, m, pf in ranges:
            nth = _is(x, 'nth', 4)
            if nth is not None and nth[2].key() == xs.key() \
                    and nth[1] == numeral(0):
                yield m, app('nth_all_le', xs, m, nth[3], pf)
        diff = _is(x, 'sub', 2)
        if diff is not None:
            # a - k <= a: truncating subtraction never exceeds what it took
            # from -- an integer sum with a negative part, once split, is one
            yield diff[0], app('sub_le', diff[0], diff[1])
            # and a - k <= b - k from a <= b, for each bound of a
            for lo, hi, pf in edges:
                if lo.key() == diff[0].key():
                    yield (_simplify_bool(app('sub', hi, diff[1])),
                           app('sub_le_sub_right', diff[1], diff[0], hi, pf))
            inner = _is(diff[0], 'sub', 2)
            if inner is not None:
                # (a - j) - k <= a - k, the bound of a - j being a
                yield (_simplify_bool(app('sub', inner[0], diff[1])),
                       app('sub_le_sub_right', diff[1], diff[0], inner[0],
                           app('sub_le', inner[0], inner[1])))
        parts = _is(x, 'add', 2)
        if parts is not None and parts[0] == numeral(0):
            yield parts[1], app('zero_add_le', parts[1])
        if parts is not None:
            # a sum below the sum of bounds: u <= hu and n <= hn give
            # u + n <= hu + hn, by add_le_add (either side may stay put)
            u, n = parts
            ups = lambda t: [(t, app('leb_refl', t))] + [
                (hi, pf) for lo, hi, pf in edges if lo.key() == t.key()]
            for hu, pu in ups(u):
                for hn, pn in ups(n):
                    if hu.key() == u.key() and hn.key() == n.key():
                        continue
                    yield (app('add', hu, hn),
                           app('add_le_add', u, hu, n, hn, pu, pn))
            for lo, hi, pf in edges:
                diff = _is(hi, 'sub', 2)
                if diff is None:
                    continue
                s = diff[0]
                if lo.key() == u.key() and diff[1].key() == n.key():
                    # u <= s - n, the checked form of u + n
                    below = _prove_le(env, n, s, edges, ranges, 1)
                    if below is not None:
                        yield s, app('add_le_of_le_sub', u, n, s, below, pf)
                elif lo.key() == n.key() and diff[1].key() == u.key():
                    # n <= s - u, the same check written the other way
                    below = _prove_le(env, u, s, edges, ranges, 1)
                    if below is not None:
                        yield s, app('add_le_of_le_sub_r', u, n, s, below,
                                     pf)
        # succ (i - 1) <= i behind 0 < i: an index `xs[i - 1]`
        pred = _is(x, 'succ', 1)
        pred = pred and _is(pred[0], 'sub', 2)
        if pred and pred[1] == numeral(1):
            pos = _prove_le(env, numeral(1), pred[0], edges, ranges, 1)
            if pos is not None:
                yield pred[0], app('sub_one_lt', pred[0], pos)

    frontier, seen = [(a, None)], {a.key()}
    for _ in range(depth + 1):
        nxt = []
        for x, pf_ax in frontier:
            done = closes(x)
            if done is not None:
                return done if pf_ax is None else \
                    app('leb_trans', a, x, b, pf_ax, done)
            for y, pf_xy in steps(x):
                if y.key() in seen:
                    continue
                seen.add(y.key())
                pf_ay = pf_xy if pf_ax is None else \
                    app('leb_trans', a, x, y, pf_ax, pf_xy)
                nxt.append((y, pf_ay))
        frontier = nxt
        if not frontier:
            break
    return None


def _open_step(env, name, args):
    """`name args` one step open, when its last argument is `succ x` (or a
    positive literal) and `name` is `fun .. i => Nat.rec C z step i`: the
    step applied to `x` and to `name` at `x`, beta-reduced.  Definitionally
    the input, by iota; None when the shape is not that."""
    value = L.value_of(env, name)
    if value is None:
        return None
    last = args[-1]
    k = L.as_numeral(last)
    if k is not None and k > 0:
        x = numeral(k - 1)
    else:
        inner = _is(last, 'succ', 1)
        if inner is None:
            return None
        x = inner[0]
    body = value
    for a in args[:-1]:
        if not isinstance(body, Lambda):
            return None
        body = L.instantiate(body.body, a)
    if not isinstance(body, Lambda):
        return None
    rec_ = L.instantiate(body.body, Var('_i'))
    head, rargs = L.spine(rec_)
    if not (isinstance(head, Var) and head.name == 'Nat.rec'
            and len(rargs) == 4 and rargs[3] == Var('_i')):
        return None
    step = rargs[2]
    folded = app(name, *(list(args[:-1]) + [x]))
    return normalize(app(step, x, folded), None)        # beta only


def _iota_int(term):
    """`Int.rec C a b (Int.ofNat x)` as `a x`, and `.. (Int.negSucc x)` as
    `b x`, beta-reduced, everywhere in `term`: iota, by hand, for the one
    recursor the integer operations are written with.  Definitionally the
    input."""
    head, args = L.spine(term)
    args = [_iota_int(a) for a in args]
    if isinstance(head, Var) and head.name == 'Int.rec' and len(args) >= 4:
        chead, cargs = L.spine(args[3])
        if isinstance(chead, Var) and len(cargs) == 1 and \
                chead.name in ('Int.ofNat', 'Int.negSucc'):
            case = args[1] if chead.name == 'Int.ofNat' else args[2]
            out = normalize(app(case, cargs[0], *args[4:]), None)  # beta
            return _iota_int(out)
    if isinstance(term, Binder):
        return term.rebuild(_iota_int(term.var_type), _iota_int(term.body))
    return app(head, *args) if args else head


def by_int_cases(env, goal, tactic):
    r"""Prove a goal over integers by its shapes: each `x : Int` binder is
    split by `Int.ind` into `Int.ofNat n` and `Int.negSucc n`, and `tactic`
    proves each goal left over natural numbers.  With every integer a
    constructor, each integer operation (`int_add` .. `int_leb`) reduces to
    `Nat` arithmetic and `if`s on `Nat` comparisons -- what `by_bounds`
    reasons about.  2^k goals for k integers: fine for the functions a
    contract is written on, and the kernel checks every one."""
    pre, body = [], goal
    while isinstance(body, Pi):
        if same_type(body.var_type, INT):
            break
        name = body.var_name
        if name == '_' or any(name == n for n, _ in pre):
            name = f'_pre{len(pre)}'
        pre.append((name, body.var_type))
        body = L.instantiate(body.body, Var(name))
    if not isinstance(body, Pi):
        return tactic(env, goal)
    xname = body.var_name if body.var_name not in ('_',) else '_x'
    rest = L.instantiate(body.body, Var(xname))
    at = lambda t: L.instantiate(L.abstract(rest, xname), t)
    cases = []
    for ctor in ('Int.ofNat', 'Int.negSucc'):
        n = f'{xname}_{"n" if ctor == "Int.ofNat" else "m"}'
        sub = Pi(n, NAT, at(App(Var(ctor), Var(n))))
        for pname, pty in reversed(pre):
            sub = Pi(pname, pty, sub)
        cases.append((n, by_int_cases(env, sub, tactic)))
    pvars = [Var(p) for p, _ in pre]
    motive = Lambda(xname, INT, rest)
    term = app('Int.ind', motive,
               *[Lambda(n, NAT, app(pf, *(pvars + [Var(n)])))
                 for n, pf in cases], Var(xname))
    term = Lambda(xname, INT, term)
    for pname, pty in reversed(pre):
        term = Lambda(pname, pty, term)
    return prove(goal, term, env, verbose=False)


def by_integers(env, goal, unfolding=(), limit=64, facts=(), steps=()):
    """`by_bounds`, after `by_int_cases`: a goal about integers."""
    return by_int_cases(env, goal, lambda e, g: by_bounds(
        e, g, unfolding=set(unfolding) | set(INT_OPS), limit=limit,
        facts=facts, steps=steps))


def _open_steps(env, term, names):
    """Every `name .. (succ x)` in `term`, for `name` in `names`, opened
    one step (see `_open_step`)."""
    if not names:
        return term
    head, args = L.spine(term)
    args = [_open_steps(env, a, names) for a in args]
    if isinstance(head, Var) and head.name in names and args:
        opened = _open_step(env, head.name, [_simplify_bool(a) for a in args])
        if opened is not None:
            return _open_steps(env, opened, names)
    if isinstance(term, Binder):
        return term.rebuild(_open_steps(env, term.var_type, names),
                            _open_steps(env, term.body, names))
    return app(head, *args) if args else head


def by_bounds(env, goal, unfolding=(), limit=64, verbose=False,
              facts=(), steps=()):
    r"""`by_every_bool`, for claims the guards imply but do not decide.

    `by_every_bool` writes `true` or `false` in for a guard and forgets it
    held.  That settles `result <= 23` for a `match`, where each arm computes
    a literal, and not `used + n <= max` behind `if used + n <= s`, where
    the arm computes nothing and the guard is the whole argument.

    This splits the same way but *dependently*: the branch where `g` went
    true gets `h : Holds g`, the other `h : Eq Bool g false`, through the
    motive `fun x => Eq Bool g x -> claim[x]` applied at `refl g`.  Every
    fact that mentions `g` is carried across the split by `Eq.ind`, so a
    fact `orb (notb g) P` becomes `P` in the branch where `g` held, and a
    fact that becomes `Holds false` closes its branch.  The goal's own
    hypotheses -- a `requires`, an integer's range, a loop invariant -- are
    kept, with the named definitions in `unfolding` opened and projections
    of a state tuple reduced, as the claim is.  `facts` are more
    (proposition, proof) pairs from the caller, over the goal's binder
    names: what a loop's invariant says at its exit, say.  At a leaf that
    does not compute, `a <= b` or `a < b` goes to `_prove_le`, and a
    variant step `n - (i + 1) < n - i` to `sub_lt`.

    The limit is on splits, as in `by_every_bool`.
    """
    names = set(unfolding)
    steps = set(steps)

    def settle(t):
        """Unfold the named definitions and reduce `Int.rec` on constructors,
        to a fixpoint: one unfolding exposes the next (`int_leb` opens to
        `int_ltb`, which opens to a case split on its arguments' shapes)."""
        for _ in range(16):
            nxt = reduce_projections(_iota_int(unfold(t, env, names)))
            if nxt.key() == t.key():
                return t
            t = nxt
        return t

    def prep(t):
        # `steps` name specifications defined by recursion on their last
        # argument: at `succ x` each is opened one step, so that the guard
        # it adds at `x` is there to split on
        return _simplify_bool(_open_steps(env, _simplify_bool(settle(
            reduce_projections(t))), steps))

    binders, body = [], goal
    while isinstance(body, Pi):
        head, _ = L.spine(body.var_type)
        hyp = isinstance(head, Var) and head.name in ('Holds', 'Eq')
        name = f'_h{len(binders)}' if hyp else body.var_name
        binders.append((name, body.var_type, hyp))
        body = L.instantiate(body.body, Var(name))
    claim = prep(body)
    base_facts = [(prep(ty), Var(n)) for n, ty, hyp in binders if hyp]
    if callable(facts):
        # facts that need the hypotheses by name: a loop's invariant at
        # exit is stated under the procedure's `requires`
        facts = facts([n for n, _, hyp in binders if hyp])
    base_facts += [(prep(ty), pf) for ty, pf in facts]
    counter = [0]

    def contradiction(facts):
        """A proof of `Holds false` from the facts, or None: a fact that is
        `Holds false` itself, or `Holds g` beside `Eq Bool g false`, where
        `Eq.ind` carries the first along the second to `Eq Bool false
        true`."""
        held = {}
        for prop, pf in facts:
            body = _is(prop, 'Holds', 1)
            if body is not None:
                if _simplify_bool(body[0]) == Var('false'):
                    return pf
                held[body[0].key()] = (body[0], pf)
        for prop, pf in facts:
            eq = _is(prop, 'Eq', 3)
            if eq is not None and eq[0] == BOOL and eq[2] == Var('false') \
                    and eq[1].key() in held:
                g, yes_pf = held[eq[1].key()]
                motive = Lambda('z', BOOL, Lambda('_e', app('Eq', BOOL, g,
                                                            Var('z')),
                                app('Holds', Var('z'))))
                return app('Eq.ind', BOOL, g, motive, yes_pf, Var('false'),
                           pf)
        return None

    def carried(facts, g, value, h):
        """Each fact that mentions `g`, with `value` written in for it and
        the proof carried along `h : Eq Bool g value`."""
        out = list(facts)
        counter[0] += 1
        z = f'_z{counter[0]}'
        for prop, pf in facts:
            moved = replace_subterm(prop, g, value)
            if moved.key() == prop.key():
                continue
            motive = Lambda(z, BOOL, Lambda(
                '_e', app('Eq', BOOL, g, Var(z)),
                replace_subterm(prop, g, Var(z))))
            out.append((_simplify_bool(moved),
                        app('Eq.ind', BOOL, g, motive, pf, value, h)))
        return out

    def variant_step(target, edges, ranges):
        """`n - (i + 1) < n - i` from `i < n`, by `sub_lt`."""
        args = _is(target, 'ltb', 2)
        if args is None:
            return None
        lo, hi = _is(args[0], 'sub', 2), _is(args[1], 'sub', 2)
        if lo is None or hi is None or lo[0].key() != hi[0].key():
            return None
        n, c = hi
        step = _is(lo[1], 'succ', 1)
        plus = _is(lo[1], 'add', 2)
        if not ((step is not None and step[0].key() == c.key()) or
                (plus is not None and plus[0].key() == c.key()
                 and plus[1] == numeral(1))):
            return None
        below = _prove_le(env, App(Var('succ'), c), n, edges, ranges)
        return None if below is None else app('sub_lt', n, c, below)

    def by_antisymmetry(target, facts, edges, ranges):
        head, targs = L.spine(target)
        for prop, pf in _conjuncts(facts):
            body = _is(prop, 'Holds', 1)
            if body is None:
                continue
            fhead, fargs = L.spine(_simplify_bool(body[0]))
            if fhead != head or len(fargs) != len(targs):
                continue
            diff = [p for p, (x, y) in enumerate(zip(fargs, targs))
                    if x.key() != y.key()]
            if len(diff) != 1:
                continue
            p = diff[0]
            was, now = fargs[p], targs[p]
            up = _prove_le(env, was, now, edges, ranges)
            down = up and _prove_le(env, now, was, edges, ranges)
            if not down:
                continue
            counter[0] += 1
            z = f'_q{counter[0]}'
            at = lambda v: app('Holds', app(head, *(
                list(fargs[:p]) + [v] + list(fargs[p + 1:]))))
            return app('Eq.ind', NAT, was,
                       Lambda(z, NAT, Lambda('_e', app('Eq', NAT, was,
                                                        Var(z)), at(Var(z)))),
                       pf, now, app('leb_antisymm', was, now, up, down))
        return None

    def leaf(claim, facts):
        claim = _simplify_bool(settle(claim))
        inner = _is(claim, 'Holds', 1)
        if inner is not None and normalize(inner[0], env) == Var('true'):
            return app('refl', BOOL, Var('true'))
        absurd_pf = contradiction(facts)
        if absurd_pf is not None:
            return app('absurd', claim, absurd_pf)
        if inner is None:
            raise TheoremError(f"not a Holds claim: {readable(claim)}")
        edges = _le_edges(facts)
        ranges = []
        for prop, pf in facts:
            h = _is(prop, 'Holds', 1)
            r = h and _is(_simplify_bool(h[0]), 'all_le', 2)
            if r:
                ranges.append((r[0], r[1], pf))
        target = _simplify_bool(inner[0])
        proof = None
        if (args := _is(target, 'andb', 2)) is not None:
            left = leaf(app('Holds', args[0]), facts)
            right = leaf(app('Holds', args[1]), facts)
            return app('andb_both', args[0], args[1], left, right)
        if (args := _is(target, 'orb', 2)) is not None:
            for k, side in enumerate(args):
                try:
                    one = leaf(app('Holds', side), facts)
                except TheoremError:
                    continue
                return app('holds_orb_left' if k == 0 else
                           'holds_orb_right', args[0], args[1], one)
        if (args := _is(target, 'leb', 2)) is not None:
            proof = _prove_le(env, args[0], args[1], edges, ranges)
        elif (args := _is(target, 'ltb', 2)) is not None:
            proof = variant_step(target, edges, ranges)
            if proof is None:
                proof = _prove_le(env, App(Var('succ'), args[0]), args[1],
                                  edges, ranges)
            summed = _is(args[1], 'add', 2)
            if proof is None and summed is not None:
                # a < b + s from b <= a and a - b < s: the checked form of
                # the sum, `lt_add_of_sub_lt`
                a_, (b_, s_) = args[0], summed
                below = _prove_le(env, b_, a_, edges, ranges)
                fits = below and _prove_le(
                    env, App(Var('succ'), app('sub', a_, b_)), s_, edges,
                    ranges)
                proof = fits and app('lt_add_of_sub_lt', a_, b_, s_, below,
                                     fits)
        elif (neg := _is(target, 'notb', 1)) is not None and \
                ((args := _is(_simplify_bool(neg[0]), 'leb', 2)) is not None
                 or (args := _is(_simplify_bool(neg[0]), 'ltb', 2))
                 is not None):
            # not (a <= b) from b < a; not (a < b) from b <= a
            a_, b_ = args
            if _is(_simplify_bool(neg[0]), 'leb', 2) is not None:
                below = _prove_le(env, _succ_of(b_), a_, edges, ranges)
                proof = below and app('lt_not_le', a_, b_, below)
            else:
                below = _prove_le(env, b_, a_, edges, ranges)
                proof = below and app('le_not_lt', a_, b_, below)
        elif (neg := _is(target, 'notb', 1)) is not None and \
                (args := _is(_simplify_bool(neg[0]), 'eqb', 2)) is not None:
            # not (a == b) from a < b
            below = _prove_le(env, _succ_of(args[0]), args[1], edges, ranges)
            proof = below and app('false_notb', app('eqb', *args),
                                  app('lt_ne', args[0], args[1], below))
        elif (args := _is(target, 'eqb', 2)) is not None and \
                args[0].key() == args[1].key():
            return app('eqb_refl', args[0])
        if proof is None:
            # a claim that is itself one of the facts, or a part of one
            for prop, pf in _conjuncts(facts):
                body = _is(prop, 'Holds', 1)
                if body is not None and \
                        _simplify_bool(body[0]).key() == target.key():
                    return pf
            # or a fact that differs from it in one number the facts pin
            # both ways: `P t'` with t' <= t and t <= t' is `P t`
            proof = by_antisymmetry(target, facts, edges, ranges)
        if proof is None:
            raise TheoremError(f"no chain of facts settles "
                               f"{readable(claim)}")
        return proof

    def split(scrutinee, claim, facts, depth):
        """Both branches of a dependent split on `scrutinee`."""
        counter[0] += 1
        h = f'_g{counter[0]}'
        is_ = lambda val: app('Eq', BOOL, scrutinee, val)
        when_true = Lambda(h, is_(Var('true')), prove_claim(
            replace_subterm(claim, scrutinee, Var('true')),
            carried(facts, scrutinee, Var('true'), Var(h))
            + [(app('Holds', scrutinee), Var(h))], depth + 1))
        when_false = Lambda(h, is_(Var('false')), prove_claim(
            replace_subterm(claim, scrutinee, Var('false')),
            carried(facts, scrutinee, Var('false'), Var(h))
            + [(is_(Var('false')), Var(h))], depth + 1))
        motive = Lambda('_x', BOOL, arrow(
            is_(Var('_x')), replace_subterm(claim, scrutinee, Var('_x'))))
        return app(app('Bool.ind', motive, when_true, when_false, scrutinee),
                   app('refl', BOOL, scrutinee))

    def disjuncts(facts):
        """The left side of each `Holds (orb a b)` fact not yet decided:
        what a case split on a disjunction splits on."""
        out, seen = [], set()
        for prop, _ in _conjuncts(facts):
            body = _is(prop, 'Holds', 1)
            either = body and _is(_simplify_bool(body[0]), 'orb', 2)
            if not either:
                continue
            a = _simplify_bool(either[0])
            neg = _is(a, 'notb', 1)
            a = neg[0] if neg else a
            if a in (Var('true'), Var('false')) or a.key() in seen:
                continue
            seen.add(a.key())
            out.append(a)
        return out

    def prove_claim(claim, facts, depth):
        while True:
            # decided `ite`s out first, so that two copies of one call --
            # one reached through a substitution, one not -- are one key
            claim = _simplify_bool(_open_steps(env, _simplify_bool(
                settle(claim)), steps))
            scrutinee = _first_open_ite(claim)
            if scrutinee is None:
                break
            decided = normalize(scrutinee, env)
            if decided not in (Var('true'), Var('false')):
                break
            claim = replace_subterm(claim, scrutinee, decided)
        if scrutinee is None:
            try:
                return leaf(claim, facts)
            except TheoremError:
                # a fact `a or b` the leaf could not use whole: split on `a`,
                # so one branch has `a` and the other has `b`
                if depth >= limit:
                    raise
                for a in disjuncts(facts):
                    try:
                        return split(a, claim, facts, depth)
                    except TheoremError:
                        continue
                raise
        if depth >= limit:
            raise TheoremError(f"more than {limit} conditions to split on")
        return split(scrutinee, claim, facts, depth)

    proof = prove_claim(claim, base_facts, 0)
    for name, ty, _ in reversed(binders):
        proof = Lambda(name, ty, proof)
    return prove(goal, proof, env, verbose=verbose)


def _prod_fields(ty):
    """The component types of a right-nested `Prod`: [A, B, C] for
    `Prod A (Prod B C)`; [ty] for anything else."""
    parts = _is(ty, 'Prod', 2)
    if parts is None:
        return [ty]
    return [parts[0]] + _prod_fields(parts[1])


def _mk(fields_ty, values):
    """`mk` down a right-nested tuple: the inverse of `_prod_fields`."""
    if len(values) == 1:
        return values[0]
    return app('mk', fields_ty[0], _prod_of(fields_ty[1:]), values[0],
               _mk(fields_ty[1:], values[1:]))


def _prod_of(tys):
    if len(tys) == 1:
        return tys[0]
    return app('Prod', tys[0], _prod_of(tys[1:]))


def by_state(env, goal, names, tactic):
    r"""Prove `forall .. (s : Prod A (Prod B C)), P s` by `tactic` on
    `forall .. (a : A) (b : B) (c : C), P (mk a (mk b c))`.

    A loop's state is a tuple, and until it is known to be built by `mk`
    its projections are stuck: `fst s` does not reduce, so nothing about
    the counter it holds can be computed or compared.  One `Prod.ind` per
    `mk` unsticks them all, and the fields get the loop variables' names.
    The first binder whose type is a `Prod` is the one split.
    """
    pre, body = [], goal
    while isinstance(body, Pi):
        if _is(body.var_type, 'Prod', 2) is not None:
            break
        # hypotheses from `arrow` are all named `_`; two of them opened
        # under one name would be one variable
        name = body.var_name
        if name == '_' or any(name == n for n, _ in pre):
            name = f'_pre{len(pre)}'
        pre.append((name, body.var_type))
        body = L.instantiate(body.body, Var(name))
    if not isinstance(body, Pi):
        return tactic(env, goal)
    state_ty = body.var_type
    rest = L.instantiate(body.body, Var('_s'))
    tys = _prod_fields(state_ty)
    fields = [f'{n}_' if n else f'_f{k}' for k, n in
              enumerate(list(names) + [None] * (len(tys) - len(names)))]
    at = lambda t: L.instantiate(L.abstract(rest, '_s'), t)
    opened = at(_mk(tys, [Var(f) for f in fields]))
    for f, ty in reversed(list(zip(fields, tys))):
        opened = Pi(f, ty, opened)
    for n, ty in reversed(pre):
        opened = Pi(n, ty, opened)
    inner = tactic(env, opened)
    whole = app(inner, *[Var(n) for n, _ in pre])

    if len(tys) == 1:
        term = app(whole, Var('_s'))
    else:
        term = _split_chain(tys, fields, whole, at)
    term = Lambda('_s', state_ty, term)
    for n, ty in reversed(pre):
        term = Lambda(n, ty, term)
    return prove(goal, term, env, verbose=False)


def _split_chain(tys, fields, whole, at):
    """`Prod.ind` down a right-nested tuple held in `_s`, binding each field
    by name and ending in `whole` applied to them all."""
    def go(k, prefix, var):
        if k == len(tys) - 1:
            # the last field is the remainder itself
            return app(whole, *[Var(f) for f in fields[:k]], var)
        here, there = tys[k], _prod_of(tys[k + 1:])
        motive = Lambda(f'_t{k}', app('Prod', here, there),
                        at(prefix(Var(f'_t{k}'))))
        rest_name = fields[k + 1] if k + 1 == len(tys) - 1 else f'_r{k}'
        minor = Lambda(fields[k], here, Lambda(rest_name, there, go(
            k + 1, lambda u, x=Var(fields[k]), p=prefix, h=here, t=there:
                p(app('mk', h, t, x, u)), Var(rest_name))))
        return app('Prod.ind', here, there, motive, minor, var)
    return go(0, lambda t: t, Var('_s'))


def by_loop(env, proc, goal=None, unfolding=(), verbose=False, steps=()):
    r"""A postcondition through `while` loops, from their own annotations.

    For each loop in order: the invariant holds on entry, a guarded pass
    keeps it, and the variant comes down -- each by `by_bounds`, the last two
    after `by_state` has split the loop's state into named fields.  Then
    `progress_by_loop` and `invariant_at_exit` turn those into two facts
    about the value the loop produced: the invariant still holds of it, and
    the condition is false.  The goal -- `proc.obligation` unless another is
    given -- is proved by `by_bounds` with those facts, for every loop, in
    hand.  A later loop's entry is proved with the earlier loops' facts.

    Nothing about a loop is assumed: the four obligations are the ones
    `read_procedure` states, and each is a kernel proof.  What this does
    not do is invent an invariant; the one written is the one used, and if
    it is too weak to carry the goal, the goal stays open.  Nested loops are
    not reached.
    """
    name = proc.name
    goal = proc.obligation if goal is None else goal
    base = set(unfolding) | {name}
    exits = []                      # (statement of `at_exit`, its proof)

    def fact_list(hyps):
        out = []
        params = {p for p, _ in proc.params}
        for prop, pf, shape in exits:
            if any(b not in params for b, _ in shape['binders']):
                continue            # stated over locals the goal cannot name
            args = [Var(b) for b, _ in shape['binders']]
            args += [Var(h) for h in hyps[:len(shape['assumptions'])]]
            out.append((prop, app(pf, *args)))
        return out

    for k, shape in enumerate(proc.shapes):
        n = k + 1
        goals = dict(proc.loop_obligations[4 * k:4 * k + 4]) \
            if len(proc.loop_obligations) >= 4 * (k + 1) \
            else dict(proc.loop_obligations)
        mine = base | {f'{name}.inv{n}', f'{name}.cond{n}',
                       f'{name}.pass{n}', f'{name}.rank{n}'}
        entry = by_bounds(env, goals['invariant holds on entry'],
                          unfolding=mine, facts=fact_list, steps=steps)
        tactic = lambda e, g: by_bounds(e, g, unfolding=mine, steps=steps)
        kept = by_state(env, goals['invariant is preserved'],
                        shape['carried'], tactic)
        down = by_state(env, goals['variant decreases'], shape['carried'],
                        tactic)
        progress = progress_by_loop(env, proc, entry, kept, down, which=k,
                                    verbose=False)
        at_exit = invariant_at_exit(env, proc, entry, kept, which=k)
        # Stated as written, over the loop's binder names -- not read back
        # from `type_check`, which answers with the normal form, where the
        # invariant's `andb`s and `leb`s have become recursors
        holds = lambda t: App(Var('Holds'), t)
        exits.append((holds(App(shape['inv'], shape['result'])), at_exit,
                      shape))
        exits.append((holds(app('notb', App(shape['cond'],
                                            shape['result']))),
                      progress, shape))
        base |= {f'{name}.inv{n}', f'{name}.cond{n}'}
    return by_bounds(env, goal, unfolding=base, facts=fact_list,
                     verbose=verbose, steps=steps)


def by_cases(env, record_name, goal, verbose=False, what='this', using=None,
             names=(), explain=False):
    r"""Prove a goal by splitting on the one constructor of its subject.

    A projection of an update is stuck on a variable -- `Context.current
    (Context.with_ticks c v)` cannot reduce, because until the value is known
    to be built by its constructor there is nothing for iota to fire on.  One
    case split unsticks every projection at once, and what is left is often
    one of the hypotheses already to hand: for a scheduler advancing
    `current`, the goal after a pass is `current + 1 <= nthreads`, and the
    condition going in was `current < nthreads`, which is the same
    proposition, since `ltb a b` is `leb (succ a) b` by definition.

    The subject need not be a record.  A loop carrying several variables
    carries a right-nested `Prod`, which is a one-constructor type too, and
    `names` (the carried variables, in order) makes the split bind them by
    name however deep the nesting goes.

    `using(fields, hypotheses, claim)` supplies a term to try first, for the
    cases where the goal follows from a lemma rather than from something
    already in scope -- a `n - i` variant comes down for an arithmetic reason,
    not a contextual one.
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

    rest = goal
    for _ in range(where):
        rest = L.instantiate(rest.body, Var(rest.var_name))
    claim_at = lambda value: L.instantiate(rest.body, value)

    head, _ = L.spine(normalize(subject_type, env))
    wanted = list(names) or (
        [f for f, _ in RECORDS[head.name]]
        if isinstance(head, Var) and head.name in RECORDS else [])

    def assemble(finish):
        """Split as deep as the names go, then hand the bindings to finish."""
        def build(ty, labels, goal_of, depth):
            info = fields_of(env, ty)
            if info is None:
                label = labels[0] if labels else f'_v{depth}'
                return Lambda(label, ty,
                              finish({label: Var(label)}, goal_of(Var(label))))
            tname, ctor, params, fields = info
            motive = Lambda('_s', ty, goal_of(Var('_s')))
            if len(labels) > len(fields) and len(fields) == 2:
                lead, tail = labels[0], labels[1:]
                inner = build(fields[1], tail,
                              lambda v, lead=lead: goal_of(
                                  app(ctor, *params, Var(lead), v)),
                              depth + 1)
                case = Lambda(lead, fields[0],
                              Lambda(f'_rest{depth}', fields[1],
                                     App(inner, Var(f'_rest{depth}'))))
                # the deeper split reports its own bindings; add this one
                case = _remember(case, lead)
            else:
                picked = list(labels)[:len(fields)]
                picked += [f'_f{depth}_{i}'
                           for i in range(len(picked), len(fields))]
                built = app(ctor, *params, *[Var(x) for x in picked])
                case = finish({x: Var(x) for x in picked}, claim_at(built)
                              if goal_of is claim_at else goal_of(built))
                for label, ftype in reversed(list(zip(picked, fields))):
                    case = Lambda(label, ftype, case)
            return Lambda('_s', ty, app(f'{tname}.ind', *params, motive, case,
                                        Var('_s')))
        return build(subject_type, wanted, claim_at, 0)

    def attempt(pick):
        collected = {}

        def finish(bindings, claim):
            collected.update(bindings)
            hypotheses, walk = [], claim
            while isinstance(walk, Pi):
                hypotheses.append(walk.var_type)
                walk = L.instantiate(walk.body, Var('_unused'))
            hyp_vars = [Var(f'_h{i}') for i in range(len(hypotheses))]
            if pick == 'lemma':
                chosen = using(Fields(collected), hyp_vars, walk)
            else:
                chosen = hyp_vars[pick]
            for i in reversed(range(len(hypotheses))):
                chosen = Lambda(f'_h{i}', hypotheses[i], chosen)
            return chosen

        term = assemble(finish)
        for bname, ty, _ in reversed(binders[:where]):
            term = Lambda(bname, ty, term)
        return term

    picks = (['lemma'] if using else []) + list(range(4))
    for pick in picks:
        if pick == 'lemma':
            # a mistake in the caller's own lemma is theirs to see, not
            # something to quietly fall past on the way to a hypothesis
            term = attempt(pick)
        else:
            try:
                term = attempt(pick)
            except IndexError:
                continue
        try:
            proof = prove(goal, term, env, verbose=False)
            if verbose:
                how = ('the lemma given' if pick == 'lemma'
                       else f'hypothesis {pick + 1}')
                print(f"  proved by cases, from {how}")
            return proof
        except KernelError as exc:
            if explain:
                print(f"  [{pick}] {str(exc)[:400]}")
            continue
    raise TheoremError(
        f"{what} does not follow from a case split: neither the lemma given "
        f"nor any hypothesis is the goal. Prove {readable(goal)} directly and "
        f"pass it in.")


def _remember(case, label):
    """A no-op marker: the binding is recorded by the recursive call."""
    return case


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


def _supply(shape):
    """Apply a loop proof to the binders and hypotheses it was stated under."""
    binders, assumptions = shape['binders'], shape['assumptions']
    args = [Var(n) for n, _ in binders]
    hypotheses = [f'_p{i}' for i in range(len(assumptions))]
    give = lambda proof: app(proof, *args, *[Var(h) for h in hypotheses])
    def wrap(term):
        for name, clause in reversed(list(zip(hypotheses, assumptions))):
            term = Lambda(name, App(Var('Holds'), clause), term)
        for name, ty in reversed(binders):
            term = Lambda(name, ty, term)
        return term
    return give, wrap


def reduce_projections(term):
    """`fst A B (mk A B a b)` is `a`, `snd` is `b`, everywhere, to a fixpoint.

    The one weak-head step a proof about a loop needs and `normalize` cannot
    give: after a pass the claim arrives as projections of the state tuple,
    and normalising it opens `leb` and `ite` into recursors there is nothing
    left to match against.  Unfolding `fst` and `snd` makes it larger, not
    smaller, since each is `Prod.rec` in a lambda.  Bottom-up, so that
    `fst (snd (mk ...))` sees the `mk` once the inner projection is gone.
    """
    if isinstance(term, App):
        reduced = App(reduce_projections(term.func), reduce_projections(term.arg))
        head, args = L.spine(reduced)
        if (isinstance(head, Var) and head.name in ('fst', 'snd')
                and len(args) == 3):
            ctor, parts = L.spine(args[2])
            if isinstance(ctor, Var) and ctor.name == 'mk' and len(parts) == 4:
                return parts[2] if head.name == 'fst' else parts[3]
        return reduced
    if isinstance(term, Binder):
        return term.__class__(term.var_name, reduce_projections(term.var_type),
                              reduce_projections(term.body), raw=True,
                              implicit=term.implicit)
    return term


def reduce_decided_ites(term):
    """`ite T true a b` is `a` and `ite T false a b` is `b`, to a fixpoint.

    Splitting a guard writes `true` or `false` into the scrutinee but leaves
    the `ite` standing, so a leaf still looks like a branch.  Reducing them
    is what turns a leaf into the value that branch actually produced.
    """
    if isinstance(term, App):
        reduced = App(reduce_decided_ites(term.func),
                      reduce_decided_ites(term.arg))
        head, args = L.spine(reduced)
        if (isinstance(head, Var) and head.name == 'ite' and len(args) == 4
                and args[1] in (Var('true'), Var('false'))):
            return args[2] if args[1] == Var('true') else args[3]
        return reduced
    if isinstance(term, Binder):
        return term.__class__(term.var_name, reduce_decided_ites(term.var_type),
                              reduce_decided_ites(term.body), raw=True,
                              implicit=term.implicit)
    return term


def bound_by_ites(env, goal, hypothesis, hypothesis_claim, others=(),
                  _subs=(), _evidence=None):
    """Prove a goal whose subject is a tree of `ite`s over the loop state.

    Splits every open guard.  At a leaf the branch has produced one value,
    and there are three ways the claim can hold without looking at how the
    leaf was reached: it is the one the hypothesis proves, and the branch
    left the state alone; it is some other term already known -- the loop
    counter, for a search that returns *where* it found something -- which
    `others` carries as (claim, proof) pairs; or it computes.

    A fourth way needs the guards themselves.  A search that returns `i`
    must show the guards hold *at i*, and those occurrences appear only
    once the `ite` has reduced, so no substitution reaches them.  That
    needs each branch to carry the equation it won, which costs a bigger
    proof term, so it is not the default: `_evidence` is None on the plain
    path and a tuple once the caller has retried.  `bound_by_ites_or_guards`
    is that retry.

    Splitting substitutes into the goal, so the same substitutions are
    applied to the hypothesis before comparing: a leaf reached by deciding
    `_returned` is about `_returned = true`, while the invariant the
    hypothesis proves is about the variable.
    """
    def specialise(term):
        for scrutinee, value in _subs:
            term = replace_subterm(term, scrutinee, value)
        return term

    def carry(proof, claim):
        # A hypothesis in scope is about the variables as they were; the
        # leaf is about them with the splits written in.  Comparing after
        # `specialise` says the two agree *once the equations hold*, but
        # the proof term's type does not know that: it has to be transported
        # along each equation, which is what the evidence is for.  Without
        # evidence only a literal match is sound.
        if _evidence is None:
            return proof
        for scrutinee, side, equation in _evidence:
            if replace_subterm(claim, scrutinee, Var(side)) == claim:
                continue
            motive = Lambda('_c', BOOL, Lambda(
                '_t', app('Eq', BOOL, scrutinee, Var('_c')),
                replace_subterm(claim, scrutinee, Var('_c'))))
            proof = app('Eq.ind', BOOL, scrutinee, motive, proof, Var(side),
                        equation)
            claim = replace_subterm(claim, scrutinee, Var(side))
        return proof

    open_ite = _first_open_ite(goal)
    if open_ite is None:
        settled = reduce_decided_ites(goal)
        if L.definitionally_equal(settled, hypothesis_claim, env):
            return hypothesis
        if (_evidence is not None and L.definitionally_equal(
                settled, specialise(hypothesis_claim), env)):
            return carry(hypothesis, hypothesis_claim)
        for claim, proof in others:
            if L.definitionally_equal(settled, claim, env):
                return proof
            if (_evidence is not None and L.definitionally_equal(
                    settled, specialise(claim), env)):
                return carry(proof, claim)
        if _evidence is not None:
            from_guards = by_decided_guards(env, settled, _evidence)
            if from_guards is not None:
                return from_guards
        # by shape first, since a leaf sits inside binders the ambient
        # environment does not know and `discharge` would type-check against
        # it; `discharge` is the fallback for what computation alone settles
        head, args = L.spine(settled)
        if isinstance(head, Var) and head.name == 'Holds' and args:
            shaped = structural_proof(env, args[-1])
            if shaped is not None:
                return shaped
        return discharge(settled, env, verbose=False)
    decided = normalize(open_ite, env)
    if decided in (Var('true'), Var('false')):
        return bound_by_ites(env, replace_subterm(goal, open_ite, decided),
                             hypothesis, hypothesis_claim, others, _subs,
                             _evidence)
    step = lambda value, evidence: bound_by_ites(
        env, replace_subterm(goal, open_ite, Var(value)), hypothesis,
        hypothesis_claim, others, tuple(_subs) + ((open_ite, Var(value)),),
        None if _evidence is None
        else tuple(_evidence) + ((open_ite, value, evidence),))
    if _evidence is None:
        return by_bool(env, goal, open_ite,
                       step('true', None), step('false', None))
    return by_bool_with_evidence(
        env, goal, open_ite,
        lambda ev: step('true', ev), lambda ev: step('false', ev),
        label='_ev%d' % len(_evidence))


def bound_by_ites_or_guards(env, goal, hypothesis, hypothesis_claim,
                            others=()):
    """`bound_by_ites`, retried with the guards in hand if it will not close.

    The plain split is enough for every claim whose leaves are about the
    state the split substituted into.  When a leaf is about an occurrence
    that only exists after reduction, it is not, and the equations each
    branch won are what settles it.  Trying the cheap way first keeps the
    proof terms small where they can be.
    """
    try:
        return bound_by_ites(env, goal, hypothesis, hypothesis_claim, others)
    except (TheoremError, ContractError):
        return bound_by_ites(env, goal, hypothesis, hypothesis_claim, others,
                             _evidence=())


def by_decided_guards(env, goal, evidence):
    """Prove `Holds b` from the guards a branch decided on the way here.

    Each entry of `evidence` is a guard, the side it went, and a proof of
    the equation.  Writing every one into the goal leaves a claim with no
    undecided guards in it; if the branch really did establish the goal,
    that claim now holds by its shape.  Transporting back along each
    equation turns a proof of the rewritten claim into one of the original.

    This is what a leaf needs when the goal mentions a guard at a
    *different occurrence* than the one that was split: a search returning
    `i` must show the guards hold at `i`, and those copies appear only once
    the `ite` has reduced, so no substitution reaches them.

    Everything is built and nothing is type-checked here.  The leaf sits
    inside the lambdas `by_cases` wrapped around it, which bind the loop's
    carried names; the ambient environment has never heard of them, and
    checking against it would fail on the first mention of the counter.
    Returns None if the guards do not settle the goal.
    """
    # the chain of claims, each one guard further rewritten
    chain = [goal]
    for scrutinee, side, _equation in evidence:
        chain.append(replace_subterm(chain[-1], scrutinee, Var(side)))
    head, args = L.spine(chain[-1])
    if not (isinstance(head, Var) and head.name == 'Holds' and args):
        return None
    proof = structural_proof(env, args[-1])
    if proof is None:
        return None
    # walk back: the motive abstracts *that guard* out of the claim as it
    # stood before the rewrite, so nothing else that happens to be `true`
    # is generalised with it
    for index in range(len(evidence) - 1, -1, -1):
        scrutinee, side, equation = evidence[index]
        before = chain[index]
        if replace_subterm(before, scrutinee, Var(side)) == before:
            continue
        motive = Lambda('_c', BOOL, Lambda(
            '_t', app('Eq', BOOL, Var(side), Var('_c')),
            replace_subterm(before, scrutinee, Var('_c'))))
        # `Eq.ind`'s motive takes the point and the equation, and its base
        # is the motive at the point itself: the proof in hand, of the
        # claim with `side` written in.  The result is the motive at the
        # guard, which is the claim with the guard back.
        proof = app('Eq.ind', BOOL, Var(side), motive, proof, scrutinee,
                    app('eq_symm', BOOL, scrutinee, Var(side), equation))
    return proof


def _project(term, state_type, k):
    """Component `k` of a state tuple typed `Prod A (Prod B ...)`."""
    head, args = L.spine(state_type)
    if not (isinstance(head, Var) and head.name == 'Prod' and len(args) == 2):
        return term
    a, b = args
    if k == 0:
        return app('fst', a, b, term)
    return _project(app('snd', a, b, term), b, k - 1)


def early_return_bound(env, proc, bound, over, fallthrough, counter='i',
                       verbose=False):
    r"""`result <= bound` for a loop that returns a literal early.

    The shape:  `while counter < len(over)`, a body that may `return k` for
    literals `k <= bound`, a fall-through `return fallthrough` after it, and

        assert invariant(counter <= len(over) and _return_value <= bound)

    Each step is a kernel proof.  Entry splits the pre-loop guards, since the
    accumulator's seed is an `ite` over them.  Preservation splits the body's
    guards and then `_returned`: a branch that assigned a literal computes, a
    branch that did not is the hypothesis, and the counter half is the loop
    condition by definition of `ltb`.  The variant is `sub_lt`.  Exit splits
    the final `_returned`.  Returns the proof of `proc.obligation`.
    """
    name = proc.name
    goals = dict(proc.loop_obligations)
    shape = proc.shapes[0]
    carried = shape['carried']
    bound_t = L.numeral(bound) if isinstance(bound, int) else bound
    n = app('len', NAT, Var(over))
    rv, rt = Var(RESULT_VAR), Var(DONE_FLAG)
    inv_names = {f'{name}.inv1', f'{name}.pass1'}

    entry = by_every_bool(env, goals['invariant holds on entry'],
                          unfolding={f'{name}.inv1'}, verbose=verbose)

    def keeps_it(f, h, claim):
        conj = reduce_projections(
            unfold(L.spine(claim)[1][-1], env, inv_names))
        after_A, after_B = L.spine(conj)[1]
        A = app('leb', f[counter], n)
        B = app('leb', rv, bound_t)
        have_B = app('andb_right', A, B, h[0])
        counter_bounded = (app('Holds', app('leb', f[counter], bound_t)),
                           app('andb_left', A, B, h[0])
                           if L.definitionally_equal(bound_t, n, env)
                           else None)
        others = ([counter_bounded] if counter_bounded[1] is not None else [])
        keep_B = bound_by_ites(env, app('Holds', after_B), have_B,
                               app('Holds', B), others)
        return app('andb_both', after_A, after_B, h[1], keep_B)

    kept = by_cases(env, None, goals['invariant is preserved'],
                    what='preservation', names=carried, using=keeps_it)
    down = by_cases(env, None, goals['variant decreases'], what='the variant',
                    names=carried,
                    using=lambda f, h, g: app('sub_lt', n, f[counter], h[1]))
    progress_by_loop(env, proc, entry, kept, down, verbose=verbose)
    at_exit = invariant_at_exit(env, proc, entry, kept)

    final = shape['result']
    state = shape['state']
    rv_f = _project(final, state, carried.index(RESULT_VAR))
    rt_f = _project(final, state, carried.index(DONE_FLAG))
    i_f = _project(final, state, carried.index(counter))
    held = app(at_exit, *[Var(p) for p, _ in proc.params])
    have_B = app('andb_right', app('leb', i_f, n), app('leb', rv_f, bound_t),
                 held)
    fall = (L.numeral(fallthrough) if isinstance(fallthrough, int)
            else fallthrough)
    motive = Lambda('_x', BOOL, app('Holds', app(
        'leb', app('ite', proc.result_type, Var('_x'), rv_f, fall), bound_t)))
    # the fall-through value against the bound: computation when both are
    # literals, reflexivity when the fall-through *is* the bound (a search
    # that ran off the end returns the length it was bounded by)
    if L.definitionally_equal(fall, bound_t, env):
        other = app('leb_refl', fall)
    else:
        other = discharge(app('Holds', app('leb', fall, bound_t)), env,
                          verbose=False)
    post = app('Bool.ind', motive, have_B, other, rt_f)
    for p, ty in reversed(proc.params):
        post = Lambda(p, ty, post)
    return prove(proc.obligation, post, env, verbose=verbose)


def invariant_at_exit(env, proc, entry, preserved, which=0):
    r"""A term proving the loop invariant still holds when the loop is done.

    `loop_preserves` says a guarded pass keeps the invariant, so any number of
    them do.  Applied at this loop's starting state, that is a statement about
    the value the loop produced -- which is what a postcondition about the
    result has to be argued from. Whatever the invariant was strong enough to
    say on the way round, it still says at the end.
    """
    shape = proc.shapes[which]
    give, wrap = _supply(shape)
    return wrap(App(app('loop_preserves', shape['state'], shape['inv'],
                        shape['pass'], shape['cond'], give(preserved),
                        shape['fuel'], shape['init']), give(entry)))


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
    give, wrap = _supply(shape)
    term = wrap(app('fold_terminates', shape['state'], shape['inv'],
                    shape['pass'], shape['cond'], shape['rank'],
                    give(preserved), give(decreases), shape['fuel'],
                    shape['init'], give(entry),
                    app('leb_refl', shape['fuel'])))

    # four obligations per loop, in order; `dict(..)['progress']` would be
    # the last loop's whichever loop this is
    label, goal = proc.loop_obligations[4 * which]
    assert label == 'progress', label
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
    # A literal is one node however large, and the accelerators read and
    # produce literals: u32::MAX and u64::MAX cost what 5 does.
    u32max, u64max = numeral(2 ** 32 - 1), numeral(2 ** 64 - 1)
    computes("leb at u32::MAX", app('leb', numeral(1998), u32max), T)
    computes("add past u32::MAX", app('add', u32max, numeral(1)),
             numeral(2 ** 32))
    computes("mul to u64::MAX", app('mul', numeral(2 ** 32 + 1), u32max),
             u64max)
    computes("ltb at u64::MAX", app('ltb', u64max, u64max), F)
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

    # Early returns were refused for years; `desugar_returns` now rewrites
    # them, so what used to be two refusals are two acceptances.  They are
    # kept as tests rather than deleted: the point is that the shapes still
    # compile and still mean what the Python means.
    ok("return inside a loop is accepted", read('''
        def f(n: 'Nat') -> 'Nat':
            v = 0
            for i in range(n):
                if eqb(i, 3):
                    return i
            return v
        ''') is not None)
    ok("return inside a branch is accepted", read('''
        def f(n: 'Nat') -> 'Nat':
            if n < 2:
                return 1
            return 0
        ''') is not None)
    # First return wins, which is what makes it a `return` and not a `break`
    # that keeps going.  0 is returned on the spot; the later assignment to v
    # is evaluated and discarded.
    first = read_procedure('''
        def f(n: 'Nat') -> 'Nat':
            v = 0
            if n < 2:
                return 1
            v = 7
            return v
        ''', env, None, ['result == 0'])
    computes("the first return wins, not the last",
             app(first.fn_term, numeral(1)), numeral(1))
    computes("and the fall-through path still returns its own value",
             app(first.fn_term, numeral(5)), numeral(7))
    ok("an early return whose every value is body-assigned still works", read('''
        def f(n: 'Nat') -> 'Nat':
            v = 0
            if n < 2:
                return v
            v = 9
            return v
        ''') is not None)
    # -- for over a list, and .append -------------------------------------
    refuses("iterating something that is not a list is refused", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            v = 0
            for i in n:
                v = v + 1
            return v
        '''), "be indexed")
    total = read_procedure('''
        def total(xs: 'Array') -> 'Nat':
            acc = 0
            for x in xs:
                acc = acc + x
            return acc
        ''', env, None, ['result == 0'])
    ok("a for over a list is a fold over it",
       normalize(app(total.fn_term, array([2, 3, 4])), env) == numeral(9))
    ok("and over the empty list it is the start",
       normalize(app(total.fn_term, array([])), env) == numeral(0))
    ok("the loop has the obligations a while has",
       {n for n, _ in total.loop_obligations} == {
           'progress', 'invariant holds on entry',
           'invariant is preserved', 'variant decreases'})
    pushed = read_procedure('''
        def evens(xs: 'Array') -> 'Array':
            out: 'Array' = []
            for x in xs:
                if eqb(x, 2):
                    out.append(x)
            return out
        ''', env, None, ['len(result) <= len(xs)'])
    ok(".append is snoc, in the order the elements came",
       normalize(app(pushed.fn_term, array([2, 1, 2])), env)
       == normalize(array([2, 2]), env))
    refuses("a variant on a list loop is refused: it is supplied", lambda: read('''
        def f(xs: 'Array') -> 'Nat':
            v = 0
            for x in xs:
                assert variant(len(xs))
                v = v + 1
            return v
        '''), "needs no variant")
    refuses("nested list loops are refused", lambda: read('''
        def f(xs: 'Array', ys: 'Array') -> 'Nat':
            v = 0
            for x in xs:
                for y in ys:
                    v = v + 1
            return v
        '''), "inside another")
    refuses("assigning the loop position is refused", lambda: read('''
        def f(xs: 'Array') -> 'Nat':
            _pos = 0
            return _pos
        '''), "reserved")
    # -- by_every_bool: a tower of guards, settled by cases -----------------
    guards = read_procedure('''
        def regs(cls: 'Nat') -> 'Nat':
            if eqb(cls, 0):
                return 6
            if eqb(cls, 1):
                return 10
            return 23
        ''', env, None, ['result <= 23'])
    ok("a bound on a chain of guards is proved for every input",
       by_every_bool(env, guards.obligation, unfolding={'regs'}) is not None)
    refuses("and a bound that one branch breaks is refused", lambda: by_every_bool(
        env, read_procedure('''
        def regs2(cls: 'Nat') -> 'Nat':
            if eqb(cls, 0):
                return 6
            if eqb(cls, 1):
                return 10
            return 23
        ''', env, None, ['result <= 10']).obligation, unfolding={'regs2'}),
        "does not compute to true")
    refuses("a goal with no ite and no computation is not this kind of claim",
            lambda: by_every_bool(env, read_procedure('''
        def ident(n: 'Nat') -> 'Nat':
            return n
        ''', env, None, ['result <= 5']).obligation, unfolding={'ident'}),
            "arbitrary")

    refuses(".append on a prelude list function is not confused with it",
            lambda: read('''
        def f(xs: 'Array') -> 'Array':
            append(xs).append(1)
            return xs
        '''), "plain variable")
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
                        using=lambda f, h, g: app('sub_lt', f['nthreads'], f['current'],
                                                h[1]))
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
            assert invariant(len(out) <= i and i <= len(parts))
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

    # -- accepted, proved for every input rather than for a batch ----------
    ok("a two-variable loop carries a Prod",
       'Prod' in readable(accepted.lean_procedure.shapes[0]['state']))
    acc_goals = dict(accepted.lean_procedure.loop_obligations)
    acc_entry = discharge(acc_goals['invariant holds on entry'], env,
                          verbose=False)
    ok("the entry invariant computes, whatever the input",
       acc_entry is not None)

    batch_len = app('len', BYTES, app('split', Var('urls'), numeral(44)))
    plus = lambda t: App(Var('succ'), t)
    count = lambda t: app('len', NAT, t)

    def keeps_it(f, h, claim):
        # len(out) <= i survives a pass whether or not this url is accepted:
        # if it is, the list grows by one and so does i; if not, neither
        # bound moves except i, which only makes room.
        conjunction = unfold(L.spine(claim)[1][-1], env,
                             {'accepted.inv1', 'accepted.pass1'})
        first, second = L.spine(conjunction)[1]
        so_far = app('andb_left', app('leb', count(f['out']), f['i']),
                     app('leb', f['i'], batch_len), h[0])
        return app('andb_both', first, second,
                   by_bool(env, App(Var('Holds'), first), None,
                           app('snoc_le', NAT, f['out'], f['i'], f['i'],
                               so_far),
                           app('leb_trans', count(f['out']), f['i'],
                               plus(f['i']), so_far,
                               app('leb_succ', f['i']))),
                   h[1])

    acc_kept = by_cases(env, None, acc_goals['invariant is preserved'],
                        what='preservation', names=['out', 'i'],
                        using=keeps_it)
    ok("one pass keeps both halves of the invariant", acc_kept is not None)
    acc_down = by_cases(env, None, acc_goals['variant decreases'],
                        what='the variant', names=['out', 'i'],
                        using=lambda f, h, g: app('sub_lt', batch_len, f['i'],
                                                  h[1]))
    ok("the variant comes down", acc_down is not None)
    ok("so the loop finishes for every input, not just tested ones",
       progress_by_loop(env, accepted.lean_procedure, acc_entry, acc_kept,
                        acc_down, verbose=False) is not None)

    # and the postcondition, argued from the invariant at the loop's exit
    at_exit = invariant_at_exit(env, accepted.lean_procedure, acc_entry,
                                acc_kept)
    ending = accepted.lean_procedure.shapes[0]['result']
    final_out = app('fst', BYTES, NAT, ending)
    final_i = app('snd', BYTES, NAT, ending)
    held = app(at_exit, Var('names'), Var('urls'))
    left = app('leb', count(final_out), final_i)
    right = app('leb', final_i, batch_len)
    post = Lambda('names', STRS, Lambda('urls', BYTES, app(
        'leb_trans', count(final_out), final_i, batch_len,
        app('andb_left', left, right, held),
        app('andb_right', left, right, held))))
    ok("and the result is never longer than the batch, for every input",
       prove(accepted.lean_procedure.obligation, post, env, verbose=False)
       is not None)
    refuses("a field name that is not bound says so",
            lambda: by_cases(env, None, acc_goals['variant decreases'],
                             what='the variant', names=['out', 'i'],
                             using=lambda f, h, g: f['index']),
            "there is no 'index' here")

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
                       using=lambda f, h, g: app('sub_lt', f['nthreads'], f['current'],
                                                h[1]))
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

    # -- the accelerators, against the definitions they stand in for --------
    # An accelerator is Python that the kernel takes the word of, so it is
    # exactly the thing not to take on trust. Each one is run against the
    # definition it replaces, in an environment built without them.
    slow = prelude(fast=False)
    ok("without acceleration the definitions are still there",
       L.as_decl('leb', slow['leb']).rule is None)
    ok("and with it they carry a rule",
       L.as_decl('leb', PRELUDE_ENV['leb']).rule is not None)
    disagreed = []
    span = list(range(0, 8))
    for name, (arity, _compute) in sorted(ACCELERATED.items()):
        pairs = ([(a,) for a in span] if arity == 1
                 else [(a, b) for a in span for b in span])
        for values in pairs:
            term = app(name, *[numeral(v) for v in values])
            quick = normalize(term, PRELUDE_ENV)
            slowly = normalize(term, slow)
            if quick != slowly:
                disagreed.append((name, values, readable(quick),
                                  readable(slowly)))
    ok("every accelerator agrees with its definition", not disagreed)
    if disagreed:
        for entry in disagreed[:4]:
            print(f"    {entry[0]}{entry[1]}: accelerated {entry[2]}, "
                  f"defined {entry[3]}")
    ok("a symbolic argument still goes through the definition",
       normalize(app('leb', numeral(1), Var('n')), PRELUDE_ENV)
       == normalize(app('leb', numeral(1), Var('n')), slow))

    # -- bounds: the arithmetic an overflow obligation needs ----------------
    for name in ('add_le_add_right', 'add_le_add', 'add_le_of_le_sub',
                 'lt_le', 'not_lt_le', 'not_le_lt', 'nth_all_le'):
        ok(f"{name} is a theorem of the prelude",
           name in PRELUDE_ENV and L.value_of(PRELUDE_ENV, name) is not None)
    ok("all_le reads every element",
       normalize(app('all_le', array([3, 9, 4]), numeral(9)), PRELUDE_ENV)
       == T and
       normalize(app('all_le', array([3, 10, 4]), numeral(9)), PRELUDE_ENV)
       == F)

    def bounds(src, ensures):
        env = prelude()
        proc = read_procedure(src, env, None, ensures)
        return by_bounds(env, proc.obligation, unfolding={proc.name})

    guarded_add = ("def g(u: 'Nat', n: 'Nat', s: 'Nat', m: 'Nat') -> 'Bool':\n"
                   "    assert (s <= m)\n"
                   "    if n <= s:\n"
                   "        if u <= s - n:\n"
                   "            return u + n <= m\n"
                   "    return True\n")
    ok("by_bounds: a checked addition stays below the bound",
       bounds(guarded_add, ["result"]) is not None)
    refuses("by_bounds: an unchecked addition is refused",
            lambda: bounds(guarded_add.replace("if u <= s - n",
                                               "if u <= s"), ["result"]),
            "no chain of facts")
    through_guard = ("def h(u: 'Nat', n: 'Nat', xs: 'Array', i: 'Nat', "
                     "m: 'Nat') -> 'Bool':\n"
                     "    assert (all_le(xs, m))\n"
                     "    if u + n <= xs[i]:\n"
                     "        return u + n <= m\n"
                     "    return True\n")
    ok("by_bounds: a guard against an element, and the element's range",
       bounds(through_guard, ["result"]) is not None)
    refuses("by_bounds: without the range, the element bounds nothing",
            lambda: bounds(through_guard.replace(
                "    assert (all_le(xs, m))\n", ""), ["result"]),
            "no chain of facts")
    vacuous = ("def v(x: 'Nat', m: 'Nat') -> 'Bool':\n"
               "    assert (x <= m)\n"
               "    if x <= m:\n"
               "        return True\n"
               "    return m < x\n")
    ok("by_bounds: a branch its own hypotheses rule out is closed",
       bounds(vacuous, ["result"]) is not None)
    for name in ('add_zero_left', 'add_succ_left', 'add_comm',
                 'add_le_of_le_sub_r', 'sub_one_lt', 'lt_not_le',
                 'le_not_lt'):
        ok(f"{name} is a theorem of the prelude",
           name in PRELUDE_ENV and L.value_of(PRELUDE_ENV, name) is not None)
    mirrored = ("def r(u: 'Nat', n: 'Nat', m: 'Nat') -> 'Bool':\n"
                "    assert (u <= m)\n"
                "    if n <= m - u:\n"
                "        return u + n <= m\n"
                "    return True\n")
    ok("by_bounds: the checked addition written the other way round",
       bounds(mirrored, ["result"]) is not None)
    previous = ("def p(xs: 'Array', i: 'Nat') -> 'Bool':\n"
                "    if i < len(xs):\n"
                "        if i > 0:\n"
                "            return (i - 1) < len(xs)\n"
                "    return True\n")
    ok("by_bounds: i - 1 is an index behind 0 < i and i < len",
       bounds(previous, ["result"]) is not None)
    refuses("by_bounds: without 0 < i it is not",
            lambda: bounds(previous.replace("        if i > 0:\n"
                                            "            return",
                                            "        if True:\n"
                                            "            return"),
                           ["result"]),
            "no chain of facts")

    for name in ('sub_add_cancel', 'lt_add_of_sub_lt', 'false_notb'):
        ok(f"{name} is a theorem of the prelude",
           name in PRELUDE_ENV and L.value_of(PRELUDE_ENV, name) is not None)
    pinned = ("def a(xs: 'Array', i: 'Nat', n: 'Nat') -> 'Bool':\n"
              "    assert (i <= n)\n"
              "    assert (n <= i)\n"
              "    assert (all_le(xs, i))\n"
              "    return all_le(xs, n)\n")
    ok("by_bounds: a fact at i is a fact at n, when i and n are pinned",
       bounds(pinned, ["result"]) is not None)
    refuses("by_bounds: and not when only i <= n",
            lambda: bounds(pinned.replace("    assert (n <= i)\n", ""),
                           ["result"]), "no chain of facts")
    unequal = ("def e(x: 'Nat', y: 'Nat') -> 'Bool':\n"
               "    if x < y:\n"
               "        return not (x == y)\n"
               "    return True\n")
    ok("by_bounds: x < y refutes x == y",
       bounds(unequal, ["result"]) is not None)
    checked = ("def c(a: 'Nat', b: 'Nat', s: 'Nat') -> 'Bool':\n"
               "    if b <= a:\n"
               "        if a - b < s:\n"
               "            return a < b + s\n"
               "    return True\n")
    ok("by_bounds: a - b < s behind b <= a is a < b + s",
       bounds(checked, ["result"]) is not None)
    refuses("by_bounds: not without b <= a, where a - b truncates",
            lambda: bounds(checked.replace("    if b <= a:\n",
                                           "    if True:\n"), ["result"]),
            "no chain of facts")
    senv = prelude()
    define(senv, 'upto', arrow(NAT, BOOL), Lambda('i', NAT, rec(
        NAT, BOOL, Var('true'),
        Lambda('k', NAT, Lambda('ih', BOOL, app(
            'andb', app('leb', Var('k'), numeral(5)), Var('ih')))),
        Var('i'))))
    opened = _open_step(senv, 'upto', [App(Var('succ'), Var('x'))])
    ok("a recursive specification opens one step at succ x",
       opened is not None and opened.key() == app(
           'andb', app('leb', Var('x'), numeral(5)),
           app('upto', Var('x'))).key())
    ok("... and only at succ x or a positive literal",
       _open_step(senv, 'upto', [Var('x')]) is None
       and _open_step(senv, 'upto', [numeral(3)]) is not None)

    # -- loops, by their own invariant ---------------------------------------
    def looped(src, ensures):
        env = prelude()
        proc = read_procedure(src, env, None, ensures)
        return by_loop(env, proc)

    counting = ("def c(xs: 'Array', v: 'Nat') -> 'Nat':\n"
                "    n = 0\n"
                "    i = 0\n"
                "    while i < len(xs):\n"
                "        assert invariant(i <= len(xs) and n <= i)\n"
                "        assert variant(len(xs) - i)\n"
                "        if xs[i] == v:\n"
                "            n = n + 1\n"
                "        i = i + 1\n"
                "    return n\n")
    ok("by_loop: a count is at most the length, by the loop's invariant",
       looped(counting, ["result <= len(xs)"]) is not None)
    refuses("by_loop: and not at most zero",
            lambda: looped(counting, ["result <= 0"]), "no chain of facts")
    refuses("by_loop: an invariant too weak to carry it is not strengthened",
            lambda: looped(counting.replace(" and n <= i", ""),
                           ["result <= len(xs)"]), "no chain of facts")
    searching = ("def s(xs: 'Array') -> 'Nat':\n"
                 "    i = 0\n"
                 "    while i < len(xs):\n"
                 "        assert invariant((i <= len(xs)) and ((not _returned)"
                 " or (_return_value <= 1)))\n"
                 "        assert variant(len(xs) - i)\n"
                 "        if xs[i] == 0:\n"
                 "            return 0\n"
                 "        i = i + 1\n"
                 "    return 1\n")
    ok("by_loop: through a loop that returns early",
       looped(searching, ["result <= 1"]) is not None)
    two = ("def t(xs: 'Array', ys: 'Array') -> 'Nat':\n"
           "    i = 0\n"
           "    while i < len(xs):\n"
           "        assert invariant(i <= len(xs))\n"
           "        assert variant(len(xs) - i)\n"
           "        i = i + 1\n"
           "    j = 0\n"
           "    while j < len(ys):\n"
           "        assert invariant(j <= len(ys))\n"
           "        assert variant(len(ys) - j)\n"
           "        j = j + 1\n"
           "    return j\n")
    ok("by_loop: two loops, each proved by its own obligations",
       looped(two, ["result <= len(ys)"]) is not None)

    # -- the kernel meets a huge literal inside a lemma's type -----------------
    big = numeral(2 ** 64 - 1)
    ok("leb_trans at 2^64 - 1 type-checks without unfolding the literal",
       L.definitionally_equal(
           type_check(PRELUDE_ENV, app('leb_trans', Var('zero'), big, big)),
           arrow(app('Holds', app('leb', Var('zero'), big)),
                 arrow(app('Holds', app('leb', big, big)),
                       app('Holds', app('leb', Var('zero'), big)))),
           PRELUDE_ENV))
    ok("a huge literal beside a symbol stays folded",
       normalize(app('sub', big, Var('u')), PRELUDE_ENV)
       == app('sub', big, Var('u')))
    ok("and still computes when both sides are literals",
       normalize(app('sub', big, numeral(5)), PRELUDE_ENV)
       == numeral(2 ** 64 - 6))

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

    # -- integers: each operation against Python's, at the 63-bit edges too
    def int_value(t):
        head, args = L.spine(normalize(t, PRELUDE_ENV))
        if isinstance(head, Var) and len(args) == 1:
            k = L.as_numeral(args[0])
            if head.name == 'Int.ofNat':
                return k
            if head.name == 'Int.negSucc' and k is not None:
                return -k - 1
        return head.name if isinstance(head, Var) and not args else None
    grid = [-3, -1, 0, 1, 3, 2 ** 62 - 1, -(2 ** 62)]
    wrong = 0
    for xv in grid:
        for yv in grid:
            X_, Y_ = int_literal(xv), int_literal(yv)
            for op, want in (('int_add', xv + yv), ('int_sub', xv - yv),
                             ('int_mul', xv * yv)):
                wrong += int_value(app(op, X_, Y_)) != want
            for op, want in (('int_ltb', xv < yv), ('int_leb', xv <= yv),
                             ('int_eqb', xv == yv)):
                wrong += int_value(app(op, X_, Y_)) != \
                    ('true' if want else 'false')
    ok("integer arithmetic agrees with Python's on a grid to +-2^62",
       wrong == 0)

    def int_theorem(src, ensures):
        env = prelude()
        proc = read_procedure(src, env, None, ensures)
        return by_integers(env, proc.obligation, unfolding={proc.name})
    absolute = ("def iabs(x: 'Int') -> 'Int':\n    if x < Int(0):\n"
                "        return -x\n    return x\n")
    ok("|x| >= 0 over the integers",
       int_theorem(absolute, ["result >= Int(0)"]) is not None)
    refuses("|x| >= 1 is refused (x = 0)",
            lambda: int_theorem(absolute, ["result >= Int(1)"]), "")
    ranged = ("def s(a: 'Int', b: 'Int') -> 'Int':\n    assert a >= Int(0) "
              "and a <= Int(10) and b >= Int(-3) and b <= Int(4)\n"
              "    return a + b\n")
    ok("a sum of ranged integers is in the summed range",
       int_theorem(ranged, ["result >= Int(-3) and result <= Int(14)"])
       is not None)
    refuses("... and not one tighter",
            lambda: int_theorem(ranged, ["result <= Int(13)"]), "")

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
