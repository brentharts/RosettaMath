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
from lean4 import (App, Bound, Expr, KernelError, Lambda, Pi, REC,
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


# ----------------------------------------------------------------- prelude

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
    define(env, 'sub', arrow(NAT, arrow(NAT, NAT)),
           Lambda('m', NAT, Lambda('n', NAT,
                  rec(NAT, NAT, Var('m'),
                      Lambda('k', NAT, Lambda('ih', NAT,
                             app('pred', Var('ih')))),
                      Var('n')))))
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

    # -- an array is a list of Nat: `len` and indexing are the two operations
    # a contract ever mentions, and both are definable by recursion.
    inductive(env, 'List', [('nil', []), ('cons', [NAT, REC])])
    define(env, 'alen', arrow(Var('List'), NAT),
           app('List.rec', Lambda('_', Var('List'), NAT), numeral(0),
               Lambda('h', NAT, Lambda('t', Var('List'), Lambda('ih', NAT,
                      App(Var('succ'), Var('ih')))))))
    # out of range reads 0, so `aget` is total -- the bound is what the
    # contract is *for*, not something the definition may assume.
    define(env, 'aget', arrow(Var('List'), arrow(NAT, NAT)),
           app('List.rec', Lambda('_', Var('List'), arrow(NAT, NAT)),
               Lambda('i', NAT, numeral(0)),
               Lambda('h', NAT, Lambda('t', Var('List'),
                      Lambda('ih', arrow(NAT, NAT), Lambda('i', NAT,
                             rec(NAT, NAT, Var('h'),
                                 Lambda('i2', NAT, Lambda('_', NAT,
                                        App(Var('ih'), Var('i2')))),
                                 Var('i'))))))))

    # -- the proposition a contract makes -----------------------------------
    define(env, 'Holds', arrow(BOOL, PROP),
           Lambda('b', BOOL, app('Eq', BOOL, Var('b'), Var('true'))))
    return env


PRELUDE_ENV = prelude()


# ------------------------------------------------- types of the fragment

TYPE_NAMES = {'Nat': NAT, 'Bool': BOOL, 'int': NAT, 'bool': BOOL,
              'List': Var('List'), 'Array': Var('List')}

# name -> ([argument types], result type), for calls the fragment understands
SIGNATURES = {
    'add': ([NAT, NAT], NAT), 'mul': ([NAT, NAT], NAT),
    'sub': ([NAT, NAT], NAT), 'pred': ([NAT], NAT),
    'succ': ([NAT], NAT),
    'alen': ([Var('List')], NAT), 'len': ([Var('List')], NAT),
    'aget': ([Var('List'), NAT], NAT),
    'leb': ([NAT, NAT], BOOL), 'ltb': ([NAT, NAT], BOOL),
    'eqb': ([NAT, NAT], BOOL), 'dvdb': ([NAT, NAT], BOOL),
    'modb': ([NAT, NAT], NAT),
    'notb': ([BOOL], BOOL), 'andb': ([BOOL, BOOL], BOOL),
    'orb': ([BOOL, BOOL], BOOL),
}

BINOPS = {ast.Add: 'add', ast.Sub: 'sub', ast.Mult: 'mul', ast.Mod: 'modb'}
COMPARES = {ast.Lt: ('ltb', False), ast.Gt: ('ltb', True),
            ast.LtE: ('leb', False), ast.GtE: ('leb', True),
            ast.Eq: ('eqb', False)}


def same_type(a, b):
    return normalize(a, PRELUDE_ENV) == normalize(b, PRELUDE_ENV)


# --------------------------------------------------- symbolic execution

class ImpToLean:
    r"""Evaluate an imperative body into a pure kernel term.

    The store is a Python dict from variable name to the term it currently
    holds, so an assignment is a substitution performed here rather than a
    `let` node the kernel would have to understand.  Nothing about this is
    trusted: whatever it produces is handed to `type_check`, which knows
    nothing of Python.
    """

    def __init__(self, where='<body>', signatures=None):
        self.where = where
        self.store = {}          # name -> kernel term
        self.types = {}          # name -> kernel type
        self.signatures = dict(SIGNATURES)
        self.signatures.update(signatures or {})
        self.counter = 0

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
            return NAT
        if isinstance(node, ast.IfExp):
            return self.type_of_expr(node.body)
        if isinstance(node, ast.Call):
            if isinstance(node.func, ast.Name):
                sig = self.signatures.get(node.func.id)
                if sig:
                    return sig[1]
            self.fail(node, "the result type of this call is not declared; "
                            "add it to SIGNATURES")
        self.fail(node, f"cannot give a type to {type(node).__name__}")

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
            return app('aget', self.expr(node.value), self.expr(node.slice))

        if isinstance(node, ast.Call):
            if node.keywords:
                self.fail(node, "keyword arguments have no meaning here")
            if not isinstance(node.func, ast.Name):
                self.fail(node, "only a plain name may be called")
            name = node.func.id
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
                    if isinstance(t, ast.Name) and t.id not in acc:
                        acc.append(t.id)
            elif isinstance(s, ast.If):
                self.assigned(s.body, acc)
                self.assigned(s.orelse, acc)
            elif isinstance(s, ast.For):
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
            if not isinstance(target, ast.Name):
                self.fail(stmt, "only a plain variable may be assigned; "
                                "there is no mutable heap in this fragment")
            if stmt.value is None:
                self.fail(stmt, "a declaration without a value has no meaning")
            ty = (self.read_type(stmt.annotation, 'the annotation')
                  if isinstance(stmt, ast.AnnAssign) and stmt.annotation
                  else self.type_of_expr(stmt.value))
            term = self.expr(stmt.value)
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
            self.fail(stmt,
                      "a `while` loop is refused: it terminates for a reason "
                      "the text does not state, so lowering one means "
                      "inventing a variant or a fuel bound -- a guess where a "
                      "guess is an unproved theorem. Write `for i in "
                      "range(bound)`, which carries its own.")

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
                   (isinstance(s, (ast.If, ast.For)) and
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

        folded = rec(NAT, acc_type, init,
                     Lambda(index, NAT, Lambda(acc, acc_type, step_body)),
                     bound)

        if len(carried) == 1:
            self.store[carried[0]] = folded
        else:
            # bind the fold once, then project, rather than recomputing it
            # per variable -- k copies of a loop is not the same program.
            whole = self.fresh('loop')
            self.store['#' + whole] = folded
            for pos, name in enumerate(carried):
                self.store[name] = App(Lambda(whole, acc_type,
                                              self.project(Var(whole), types,
                                                           pos)),
                                       folded)
        return None

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
                 obligation):
        self.name = name
        self.params = params                # [(name, type)]
        self.result_type = result_type
        self.body = body                    # the pure term the body computes
        self.requires = requires            # [Bool term]
        self.ensures = ensures              # [Bool term], `result` substituted
        self.obligation = obligation        # the Pi type to be proved

    def __repr__(self):
        return f"<procedure {self.name} : {readable(self.obligation)}>"


def read_procedure(func, env=None, signatures=None, ensures=()):
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

    reader = ImpToLean(where=tree.name, signatures=signatures)
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

    term = reader.block(body)
    if term is None:
        raise ContractError(f"{tree.name}: the body falls off the end without "
                            f"returning")
    result_type = (reader.read_type(tree.returns, 'the return annotation')
                   if tree.returns is not None else NAT)

    # the postcondition is read in a scope where `result` is the body
    post = []
    for clause in ensures:
        node = ast.parse(clause, mode='eval').body
        saved_store, saved_types = dict(reader.store), dict(reader.types)
        reader.store = {n: Var(n) for n, _ in params}
        reader.types = {n: t for n, t in params}
        reader.store['result'] = term
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

    # the body must be a well-formed term of the declared type before any of
    # this means anything: state the function, then check it
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
    type_check(env, goal)

    proc = Procedure(tree.name, params, result_type, term, pre, post, goal)
    proc.fn_term, proc.fn_type = fn_term, fn_type
    return proc


def procedure(env=None, ensures=(), signatures=None, verbose=True, define_as=None):
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
        proc = read_procedure(func, scope, signatures, ensures)
        if define_as or proc.name not in scope:
            define(scope, define_as or proc.name, proc.fn_type, proc.fn_term)
        func.lean_procedure = proc
        func.lean_term = proc.body
        func.lean_obligation = proc.obligation
        if verbose:
            print(f"read {proc.name} : {readable(proc.fn_type)}")
            print(f"  obligation: {readable(proc.obligation)}")
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
    """Prove an obligation that computes: `refl` is the whole proof.

    A precondition is peeled off and named, since the proof of the conclusion
    does not need to look at it.  A remaining `forall` is refused: it does not
    compute, and pretending otherwise is the one thing a checker must not do.
    """
    env = PRELUDE_ENV if env is None else env
    goal = proc.obligation if isinstance(proc, Procedure) else proc
    original = goal
    hypotheses = []
    while isinstance(goal, Pi) and not L.occurs(goal.body, 0):
        hypotheses.append(goal.var_type)
        goal = L.instantiate(goal.body, Var('true'))    # unused: it cannot occur
    if isinstance(goal, Pi):
        raise ContractError(
            f"{readable(original)} is universally quantified, so it does not "
            f"compute. Give it a value with at(), or prove it by induction.")

    _, args = L.spine(goal)
    if not args:
        raise ContractError(f"{readable(goal)} is not a Holds(...) claim")
    value = normalize(args[-1], env)
    if value != Var('true'):
        raise TheoremError(f"the contract does not hold: it computes to "
                           f"{readable(value)}, not true")

    proof = app('refl', BOOL, Var('true'))
    for i, hyp in enumerate(reversed(hypotheses)):
        proof = Lambda(f'_h{len(hypotheses) - i}', hyp, proof)
    actual = type_check(env, proof)
    if not L.definitionally_equal(original, actual, env):
        raise TheoremError(f"proved {readable(actual)}, "
                           f"not {readable(original)}")
    if verbose:
        note = (f" (given {len(hypotheses)} precondition(s), which the "
                f"conclusion does not need)" if hypotheses else "")
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


def array(values):
    """A concrete Array, as the List the prelude defines."""
    out = Var('nil')
    for v in reversed(values):
        out = app('cons', numeral(v), out)
    return out


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
    length = app('alen', Var(param))
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
    computes("alen", app('alen', array([5, 6, 7])), numeral(3))
    computes("aget", app('aget', array([5, 6, 7]), numeral(1)), numeral(6))
    computes("aget past the end reads 0",
             app('aget', array([5, 6, 7]), numeral(9)), numeral(0))
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
       'Nat.rec' in readable(double.lean_procedure.body))
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
       'mk' in readable(two_carried.lean_procedure.body))
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
                              kw.get('ensures', ['result == 0']))

    refuses("while is refused, with the reason", lambda: read('''
        def f(n: 'Nat') -> 'Nat':
            v = 0
            while v < n:
                v = v + 1
            return v
        '''), "inventing a variant")
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
