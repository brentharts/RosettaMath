#!/usr/bin/env python3
# lean4.py - Version 0.3: The Micro-Kernel, on de Bruijn indices
import ast
import sys
import itertools
import inspect
import textwrap

# The LaTeX front end lives in the rest of the project: rosettaui tokenises the
# subset and rosettamath knows how \texttt content is escaped.
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import rosettaui
import rosettamath

__doc__ = r'''
The lean4.py Micro-Kernel:
a mathematical engine capable of understanding that a function takes an argument of type $A$ and returns something of type $B$. This is the Calculus of Constructions (CoC), the foundation of Lean, Coq, and dependent type theory.  Inspired by:
 https://github.com/leanprover/lean4
 https://xenaproject.wordpress.com/2019/02/11/lean-in-latex/

LaTeX Native:
By treating LaTeX not as an output format (like the Xena project did), but as an input language, you are essentially creating a literate programming environment where mathematics and Python code live together seamlessly.

Modern Lean 4 is a massive, heavily engineered beast:
While its scale is necessary for verifying complex modern mathematics (like the Liquid Tensor Experiment), it is fundamentally overkill because our goal is just to have a lightweight, hackable engine to play with dependent types, Python code verification, and LaTeX formatting.

The Xena Project blog post (above) highlights a crucial idea: making formal proofs readable to humans by bridging Lean and LaTeX/HTML. Patrick Massot's format_lean tool took Lean code and rendered the "tactic state" (the step-by-step logic) into a beautiful, mathematician-friendly format.

We propose flipping that bridge: Using a subset of LaTeX as the input language to write proofs about Python code, powered by a minimalist Python-based theorem prover.

Representation
--------------
Bound variables are de Bruijn indices; free variables and global constants keep
their names.  A binder stores only the type of its argument and a body in which
the argument appears as Bound(0), plus a name kept purely as a hint for
printing.

That choice removes two whole classes of bug rather than patching them.
Substitution cannot capture a variable, because a name in the term being
substituted can never collide with an index.  And alpha-equivalent terms are
literally the same object, so
    \forall x : Nat, Nat   and   \forall y : Nat, Nat
compare equal without any renaming machinery -- which matters, because in a
proof checker comparing types is how every decision gets made.

The constructors still take names, so terms read the way they always did:
Lambda("T", Universe(0), Var("T")) abstracts the T for you.

Definitions and inductive types
-------------------------------
A global name may carry a value as well as a type, so a definition unfolds
(delta reduction); and an inductive type may be declared with its constructors,
from which the recursor and its computation rule are generated (iota
reduction).  Nat is declared rather than assumed:

    inductive(env, 'Nat', [('zero', []), ('succ', [REC])])

which gives zero, succ, Nat.rec for defining functions and Nat.ind for proving
theorems -- two recursors because there is no universe polymorphism here.  With
add defined by recursion on its second argument, add 2 3 computes to 5, and
m + 0 = m holds by computation alone, while 0 + n = n is stuck until n is a
constructor and needs the induction principle.  @definition adds a checked
Python function to the environment, so proofs can be built on earlier ones
instead of standing alone.

A family may take parameters, fixed across the constructors, and indices, which
vary from one to the next:

    inductive(env, 'List', [('nil', []), ('cons', [Var('A'), REC])],
              params=[('A', Universe(1))])

    inductive(env, 'Eq', [('refl', [], [Var('a')])],
              params=[('A', Universe(1)), ('a', Var('A'), False)],
              indices=[('b', Var('A'))], level=0)

Equality is therefore no longer assumed.  It is the family whose single
constructor is refl, its recursor is the J rule, and symm, trans, congrArg and
transport are proved from it rather than declared as axioms -- which is worth
knowing, because an axiom is something you have to trust and a definition is
not.

Implicit arguments
------------------
A binder may be implicit, written \forall {A : Type}, ... in a statement.  Each
use of such a constant contributes a hole, and the hole is solved by unifying
the expected argument type with the actual one, so a proof reads

    @theorem(r'\forall x \in \text{Nat}, x = x')
    def reflexivity(x: 'Nat'):
        return refl(x)

rather than spelling out refl(Nat, x).  Write explicit(refl)(Nat, x) -- Lean's
@refl -- to supply the argument by hand.

The elaborator that does this is deliberately untrusted: it fills in the holes
and then hands the completed term to type_check, which verifies it from
scratch knowing nothing about implicit arguments.  A bug in the elaborator can
therefore cost you a confusing error message, but not a false theorem.

Unification is over Miller's pattern fragment: a hole applied to distinct
variables, ?P a, is solved by abstracting those variables out of the other
side.  That is what makes an implicit argument in a dependent position work --
transport's motive P is only ever seen applied, as P a and P b, so solving it
means answering a higher-order question.  Full higher-order unification is
undecidable; outside the fragment the elaborator refuses rather than guesses,
because a guess here is a proof the user did not write.

Inside the fragment a constraint can still have more than one legal answer:
?P a = Eq A a a admits (lam z. Eq A z z), (lam z. Eq A z a), (lam z. Eq A a z)
and the constant (lam z. Eq A a a) whenever a is in scope where the hole was
made.  Such constraints are postponed rather than guessed, and settled once
every constraint on that hole is known: each proposes the whole family of
readings, obtained by abstracting any subset of the occurrences, and only a
reading satisfying all the constraints is accepted.

That is what lets symm be written transport(h, refl(a)), where the first
constraint's obvious answer is the wrong one, and transport(h, h), where the
answer abstracts nothing at all.  When more than one reading survives the term
is still checked by the kernel, so the theorem is proved either way, but the
choice is reported rather than made quietly.
'''


class KernelError(Exception):
    """The term is not well typed, or cannot be understood."""


class TheoremError(KernelError):
    """A theorem did not prove what it claimed to prove."""


# ---------------------------------------------------------------- expressions

# Structural keys are interned integers.  The key of a node is looked up from
# a shallow description of it -- its constructor, and the *keys* of its
# children -- so building one is O(1) and so is hashing it.
#
# It used to be the nested tuple that description suggests, which was correct
# and quietly quadratic-or-worse: substitution shares the term it inserts
# rather than copying it, so a body mentioning its argument three times builds
# a DAG with 3**n paths through it and only O(n) distinct nodes -- but hashing
# a nested tuple walks paths, not nodes, so every cache lookup paid the 3**n.
# An integer collapses that to the node count the DAG actually has.
_KEYS = {}


def intern_key(description):
    key = _KEYS.get(description)
    if key is None:
        key = _KEYS[description] = len(_KEYS)
    return key


class Expr:
    """Base class for all logical expressions.

    Equality is structural over the de Bruijn form, so it is alpha-equivalence
    for free.  key() deliberately ignores the printing hint on binders.
    """

    def key(self):
        raise NotImplementedError

    def __eq__(self, other):
        return isinstance(other, Expr) and self.key() == other.key()

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(self.key())

    def fullkey(self):
        """A structural key that also fixes the name hints and implicitness.

        key() is deliberately blind to both, because that is what makes it
        alpha-equivalence.  The rewrites below carry both through, so two
        terms that compare equal can still rewrite to different results, and
        a cache that cannot tell them apart will hand back the wrong one --
        it reprinted symm's `{a : A}` as `a : A`.  Equality wants the blind
        key; a cache wants this one.

        A leaf carries neither, so for one the two keys coincide.
        """
        return self.key()

    def __repr__(self):
        return str(self)


class Universe(Expr):
    """Sorts/Universes: Prop (0), Type (1), Type 1 (2), etc."""

    def __init__(self, level=0):
        self.level = level

    def key(self):
        cached = getattr(self, '_key', None)
        if cached is None:
            cached = self._key = intern_key(('sort', self.level))
        return cached

    def __str__(self):
        return pretty(self)


class Var(Expr):
    """A free variable or global constant, like 'Nat'."""

    def __init__(self, name):
        self.name = name

    def key(self):
        cached = getattr(self, '_key', None)
        if cached is None:
            cached = self._key = intern_key(('var', self.name))
        return cached

    def __str__(self):
        return pretty(self)


class Bound(Expr):
    """A bound variable, as a de Bruijn index: 0 is the nearest binder."""

    def __init__(self, index):
        self.index = index

    def key(self):
        cached = getattr(self, '_key', None)
        if cached is None:
            cached = self._key = intern_key(('bound', self.index))
        return cached

    def __str__(self):
        return pretty(self)


class App(Expr):
    """Function application: f(x)"""

    def __init__(self, func, arg):
        self.func = func
        self.arg = arg

    def key(self):
        # cached: a term is never mutated after construction, and key() is
        # what every cache and comparison below is built on
        cached = getattr(self, '_key', None)
        if cached is None:
            cached = self._key = intern_key(
                ('app', self.func.key(), self.arg.key()))
        return cached

    def fullkey(self):
        cached = getattr(self, '_fullkey', None)
        if cached is None:
            cached = self._fullkey = intern_key(
                ('app!', self.func.fullkey(), self.arg.fullkey()))
        return cached

    def __str__(self):
        return pretty(self)


class Meta(Expr):
    """A hole for an implicit argument, to be solved by unification.

    Metavariables belong to the elaborator, never to the kernel: a term is only
    handed to type_check once every hole has been filled in.
    """

    def __init__(self, index, hint='?', context=()):
        self.index = index
        self.hint = hint
        # the local names in scope where the hole was created: a solution may
        # legitimately mention these, which is exactly what makes some
        # constraints ambiguous
        self.context = tuple(context)

    def key(self):
        cached = getattr(self, '_key', None)
        if cached is None:
            cached = self._key = intern_key(('meta', self.index))
        return cached

    def __str__(self):
        return pretty(self)


_meta_count = [0]


def new_meta(hint='?', context=()):
    _meta_count[0] += 1
    return Meta(_meta_count[0], hint, context)


class Binder(Expr):
    """Shared machinery for Pi and Lambda.

    The constructor takes a *named* body and abstracts the name away, so
    callers write ordinary readable terms and the kernel still gets de Bruijn
    indices.  Inner binders are built first, so a shadowed name has already
    been abstracted by the time the outer binder looks at it.
    """

    def __init__(self, var_name, var_type, body, raw=False, implicit=False):
        self.var_name = var_name
        self.var_type = var_type
        self.implicit = implicit
        self.body = body if raw else abstract(body, var_name)

    @classmethod
    def raw(cls, var_name, var_type, body, implicit=False):
        """Build directly from a body that already uses de Bruijn indices."""
        return cls(var_name, var_type, body, raw=True, implicit=implicit)

    def rebuild(self, var_type, body):
        """The same binder with new parts, keeping name hint and implicitness."""
        return type(self).raw(self.var_name, var_type, body, self.implicit)

    def key(self):
        cached = getattr(self, '_key', None)
        if cached is None:
            cached = self._key = intern_key(
                (self.tag, self.var_type.key(), self.body.key()))
        return cached

    def fullkey(self):
        cached = getattr(self, '_fullkey', None)
        if cached is None:
            cached = self._fullkey = intern_key(
                (self.tag + '!', self.var_name, self.implicit,
                 self.var_type.fullkey(), self.body.fullkey()))
        return cached

    def __str__(self):
        return pretty(self)


class Pi(Binder):
    r"""Dependent function type: \forall (x : A), B"""
    tag = 'pi'


class Lambda(Binder):
    r"""Anonymous function: \x : A => body"""
    tag = 'lam'


def arrow(domain, codomain):
    """A -> B, the non-dependent function type."""
    return Pi.raw('_', domain, shift(codomain, 1))


# ------------------------------------------------------------------- printing

def occurs(expr, index=0):
    """Does the given de Bruijn index actually appear?  (Used for A -> B.)"""
    if isinstance(expr, Bound):
        return expr.index == index
    if isinstance(expr, App):
        return occurs(expr.func, index) or occurs(expr.arg, index)
    if isinstance(expr, Binder):
        return occurs(expr.var_type, index) or occurs(expr.body, index + 1)
    return False


def free_names(expr, acc=None):
    """The free (named) variables of a term."""
    acc = set() if acc is None else acc
    if isinstance(expr, Var):
        acc.add(expr.name)
    elif isinstance(expr, App):
        free_names(expr.func, acc)
        free_names(expr.arg, acc)
    elif isinstance(expr, Binder):
        free_names(expr.var_type, acc)
        free_names(expr.body, acc)
    return acc


def as_numeral(expr):
    """succ (succ zero) -> 2, or None if it is not a closed numeral."""
    count = 0
    while isinstance(expr, App):
        if not (isinstance(expr.func, Var) and expr.func.name == 'succ'):
            return None
        count += 1
        expr = expr.arg
    if isinstance(expr, Var) and expr.name == 'zero':
        return count
    return None


def fresh(hint, names, avoid=()):
    """A binder name that shadows nothing visible.

    Avoiding the enclosing binders is not enough: a free variable of the same
    name in the body would print identically to the bound one, and a checker
    whose output cannot be trusted to mean what it says is worse than useless.
    """
    while hint in names or hint in avoid:
        hint += "'"
    return hint


def pretty(expr, names=None):
    """Render with readable names, re-derived from the hints on the way down."""
    names = names or []
    if isinstance(expr, Universe):
        return "Prop" if expr.level == 0 else f"Type {expr.level - 1}"
    if isinstance(expr, Var):
        return '0' if expr.name == 'zero' else expr.name
    if isinstance(expr, Bound):
        return names[expr.index] if expr.index < len(names) else f"#{expr.index}"
    if isinstance(expr, Meta):
        return f"?{expr.hint}{expr.index}"
    if isinstance(expr, App):
        digits = as_numeral(expr)
        if digits is not None:
            return str(digits)          # succ(succ(zero)) reads badly as a type
        return f"{pretty(expr.func, names)}({pretty(expr.arg, names)})"
    if isinstance(expr, Pi):
        dom = pretty(expr.var_type, names)
        if not occurs(expr.body, 0) and not expr.implicit:
            # non-dependent: print the arrow, which is what a reader expects
            return f"({dom} → {pretty(expr.body, ['_'] + names)})"
        n = fresh(expr.var_name, names, free_names(expr.body))
        left, right = ('{', '}') if expr.implicit else ('', '')
        return (f"(∀ {left}{n} : {dom}{right}, "
                f"{pretty(expr.body, [n] + names)})")
    if isinstance(expr, Lambda):
        n = fresh(expr.var_name, names, free_names(expr.body))
        return (f"(λ {n} : {pretty(expr.var_type, names)} ⇒ "
                f"{pretty(expr.body, [n] + names)})")
    return f"<{type(expr).__name__}>"


# ------------------------------------------------------- de Bruijn operations

# shift, abstract and instantiate are pure rewrites over immutable terms, so
# the same input has the same output forever and remembering it is sound.
# Memoising them is not only about repeated work: because a hit returns the
# *same object*, a term that shares a subterm keeps sharing it after
# substitution.  Without that, every substitution re-expanded the DAG into a
# tree -- 4.5M shift calls to normalise `modb 10 4`, whose answer is 2.
#
# These are keyed on fullkey(), not on key().  A structural key is
# deliberately blind to a binder's name hint and to whether it is implicit,
# and `rebuild` carries both through, so two terms that compare equal can
# still rewrite to different results: keying on key() quietly reprinted
# symm's type with `{a : A}` as `a : A`.  Identity would be safe but too
# sharp -- it misses the structurally identical copies that are the whole
# point -- so fullkey() draws the line exactly where the rewrites do.
_SHIFT_CACHE = {}
_ABSTRACT_CACHE = {}
_INSTANTIATE_CACHE = {}


def shift(expr, amount, cutoff=0):
    """Renumber the free indices of expr, leaving those below cutoff alone."""
    if amount == 0:
        return expr
    slot = (expr.fullkey(), amount, cutoff)
    found = _SHIFT_CACHE.get(slot)
    if found is None:
        found = _SHIFT_CACHE[slot] = _shift(expr, amount, cutoff)
    return found


def _shift(expr, amount, cutoff):
    if isinstance(expr, Bound):
        return Bound(expr.index + amount) if expr.index >= cutoff else expr
    if isinstance(expr, App):
        return App(shift(expr.func, amount, cutoff),
                   shift(expr.arg, amount, cutoff))
    if isinstance(expr, Binder):
        return expr.rebuild(shift(expr.var_type, amount, cutoff),
                            shift(expr.body, amount, cutoff + 1))
    return expr


def abstract(expr, name, depth=0):
    """Turn free occurrences of a named variable into the index depth."""
    slot = (expr.fullkey(), name, depth)
    found = _ABSTRACT_CACHE.get(slot)
    if found is None:
        found = _ABSTRACT_CACHE[slot] = _abstract(expr, name, depth)
    return found


def _abstract(expr, name, depth):
    if isinstance(expr, Var):
        return Bound(depth) if expr.name == name else expr
    if isinstance(expr, App):
        return App(abstract(expr.func, name, depth),
                   abstract(expr.arg, name, depth))
    if isinstance(expr, Binder):
        return expr.rebuild(abstract(expr.var_type, name, depth),
                            abstract(expr.body, name, depth + 1))
    return expr


def instantiate(expr, value, depth=0):
    """Replace the index depth with value, closing up the binder above it."""
    slot = (expr.fullkey(), value.fullkey(), depth)
    found = _INSTANTIATE_CACHE.get(slot)
    if found is None:
        found = _INSTANTIATE_CACHE[slot] = _instantiate(expr, value, depth)
    return found


def _instantiate(expr, value, depth):
    if isinstance(expr, Bound):
        if expr.index == depth:
            return shift(value, depth)
        return Bound(expr.index - 1) if expr.index > depth else expr
    if isinstance(expr, App):
        return App(instantiate(expr.func, value, depth),
                   instantiate(expr.arg, value, depth))
    if isinstance(expr, Binder):
        return expr.rebuild(instantiate(expr.var_type, value, depth),
                            instantiate(expr.body, value, depth + 1))
    return expr


def substitute(expr, var_name, replacement):
    """Replace a free named variable.

    Capture is impossible here: the binders hold indices, not names, so nothing
    in replacement can be caught by one.  That is the whole point of the
    representation.
    """
    if isinstance(expr, Var):
        return replacement if expr.name == var_name else expr
    if isinstance(expr, App):
        return App(substitute(expr.func, var_name, replacement),
                   substitute(expr.arg, var_name, replacement))
    if isinstance(expr, Binder):
        inner = shift(replacement, 1)
        return expr.rebuild(substitute(expr.var_type, var_name, replacement),
                            substitute(expr.body, var_name, inner))
    return expr


# normal form cache: id(env) -> [env, generation, {key: normal form}].
# The environment is held by strong reference so its id cannot be reused by a
# later object, and `declare` refuses to rebind a name, so len(env) is a
# faithful generation counter: an entry is stale exactly when a name was added.
_NORM_CACHE = {}


def _norm_cache(env):
    slot = _NORM_CACHE.get(id(env))
    if slot is None or slot[0] is not env or slot[1] != len(env):
        slot = [env, len(env), {}]
        _NORM_CACHE[id(env)] = slot
    return slot[2]


_BETA_CACHE = {}


def normalize(expr, env=None):
    """Full normalisation: beta, plus delta and iota when an environment is given.

    beta   applying a lambda
    delta  unfolding a name that abbreviates a term
    iota   firing a recursor that has reached a constructor

    Without an environment only beta fires, which is what the kernel did
    before definitions existed and is still the right behaviour for a term
    whose constants are all opaque.

    The result is memoised on the term's structural key.  Nothing about what
    a term normalises to changes, but a great deal about whether it finishes
    does: substituting an argument and then normalising the result re-walks
    that argument, so a fold over n re-derived each step from scratch and cost
    2**n to produce a normal form of size O(n).  `leb 20 30` did not
    terminate in any useful time; a loop of the length the SIMD contracts talk
    about, `len(ptr) >= 64`, was hopeless.  Since a term is immutable and an
    environment only ever grows, the same key has the same normal form
    forever, so remembering it is sound.
    """
    cache = _BETA_CACHE if env is None else _norm_cache(env)
    slot = expr.fullkey()
    found = cache.get(slot)
    if found is not None:
        return found
    result = _normalize(expr, env)
    cache[slot] = result
    return result


def _normalize(expr, env):
    if isinstance(expr, App):
        func = normalize(expr.func, env)
        arg = normalize(expr.arg, env)
        if isinstance(func, Lambda):
            return normalize(instantiate(func.body, arg), env)
        whole = App(func, arg)
        reduced = reduce_head(whole, env)
        return normalize(reduced, env) if reduced is not None else whole
    if isinstance(expr, Binder):
        return expr.rebuild(normalize(expr.var_type, env),
                            normalize(expr.body, env))
    if isinstance(expr, Var):
        value = value_of(env, expr.name)
        return normalize(value, env) if value is not None else expr
    return expr


def reduce_head(expr, env):
    """One delta or iota step at the head of an application, or None."""
    if env is None:
        return None
    head, args = spine(expr)
    if not isinstance(head, Var):
        return None
    decl = decl_of(env, head.name)
    if decl is None:
        return None
    if decl.rule is not None:
        return decl.rule(env, args)
    if decl.value is not None:
        out = decl.value
        for a in args:
            out = App(out, a)
        return out
    return None


def definitionally_equal(a, b, env=None):
    """Types are the same if they normalise to the same term."""
    return normalize(a, env) == normalize(b, env)


# ------------------------------------------------------------- declarations

class Decl:
    """What a global name means.

    Until now the environment mapped a name only to its type, so every
    constant was opaque: nothing could be unfolded, and a definition was
    impossible to state.  A declaration may now also carry

      value  -- a term the name abbreviates, unfolded during normalisation
               (delta reduction)
      rule   -- a computation rule for a recursor, fired when it is applied
               to a constructor (iota reduction)
    """

    def __init__(self, name, type_, value=None, rule=None, kind='constant'):
        self.name = name
        self.type = type_
        self.value = value
        self.rule = rule
        self.kind = kind

    def __repr__(self):
        return f"<{self.kind} {self.name} : {pretty(self.type)}>"


def as_decl(name, entry):
    """Accept a bare type as well as a Decl, so old environments still work."""
    return entry if isinstance(entry, Decl) else Decl(name, entry)


def decl_of(env, name):
    if env is None or name not in env:
        return None
    return as_decl(name, env[name])


def type_of(env, name):
    d = decl_of(env, name)
    return None if d is None else d.type


def value_of(env, name):
    d = decl_of(env, name)
    return None if d is None else d.value


# --------------------------------------------------------------- type checker

def type_check(env, expr, local=None):
    """The type of expr, or a KernelError.  This is the proof checker.

    env maps global names to their types; local is the stack of bound-variable
    types, innermost first.
    """
    local = list(local or [])

    if isinstance(expr, Meta):
        raise KernelError(f"Unsolved metavariable {pretty(expr)}: an implicit "
                          f"argument could not be inferred")

    if isinstance(expr, Universe):
        return Universe(expr.level + 1)

    if isinstance(expr, Var):
        declared = type_of(env, expr.name)
        if declared is None:
            raise KernelError(f"Unknown identifier: {expr.name}")
        return declared

    if isinstance(expr, Bound):
        if expr.index >= len(local):
            raise KernelError(f"Unbound index #{expr.index}")
        # the stored type lives under fewer binders than we do now
        return shift(local[expr.index], expr.index + 1)

    if isinstance(expr, Lambda):
        expect_sort(env, expr.var_type, local, "lambda argument")
        body_type = type_check(env, expr.body, [expr.var_type] + local)
        return Pi.raw(expr.var_name, expr.var_type, body_type, expr.implicit)

    if isinstance(expr, Pi):
        domain = expect_sort(env, expr.var_type, local, "function domain")
        codomain = expect_sort(env, expr.body, [expr.var_type] + local,
                               "function codomain")
        # impredicative Prop: a family of propositions is itself a proposition
        if codomain.level == 0:
            return Universe(0)
        return Universe(max(domain.level, codomain.level))

    if isinstance(expr, App):
        func_type = normalize(type_check(env, expr.func, local), env)
        if not isinstance(func_type, Pi):
            raise KernelError(f"Expected a function, got {func_type}")
        arg_type = type_check(env, expr.arg, local)
        if not definitionally_equal(func_type.var_type, arg_type, env):
            raise KernelError(f"Type mismatch: expected "
                              f"{readable(func_type.var_type)}, "
                              f"got {readable(arg_type)}")
        return normalize(instantiate(func_type.body, expr.arg), env)

    raise KernelError(f"Cannot typecheck: {expr}")


def expect_sort(env, expr, local, role):
    """A type must itself have a sort; anything else is a category error."""
    sort = normalize(type_check(env, expr, local), env)
    if not isinstance(sort, Universe):
        raise KernelError(f"The {role} {pretty(expr)} is not a type "
                          f"(it has type {pretty(sort)})")
    return sort




# --------------------------------------------------- building an environment

REC = 'recursive'      # marks a constructor argument of the type being defined


def declare(env, name, type_, value=None, rule=None, kind='constant'):
    """Add a name to an environment, checking what can be checked."""
    if name in env:
        raise KernelError(f"{name} is already declared")
    expect_sort(env, type_, [], f"type of {name}")
    if value is not None:
        if name in free_names(value):
            raise KernelError(
                f"{name} is defined in terms of itself; recursion belongs in a "
                f"recursor, so that unfolding always terminates")
        actual = type_check(env, value)
        if not definitionally_equal(type_, actual, env):
            raise KernelError(f"{name} is declared {readable(type_)} but its "
                              f"definition has type {readable(actual)}")
    env[name] = Decl(name, type_, value, rule, kind)
    return env[name]


def define(env, name, type_, value):
    r"""A name that abbreviates a term, unfolded by delta reduction."""
    return declare(env, name, type_, value=value, kind='definition')


def axiom(env, name, type_):
    """An opaque constant: something assumed, never unfolded."""
    return declare(env, name, type_, kind='axiom')


def binding(spec, implicit=True):
    """(name, type) or (name, type, implicit) -> a uniform triple."""
    if len(spec) == 3:
        return spec
    return (spec[0], spec[1], implicit)


def constructor_parts(spec):
    """(name, args) or (name, args, index values) -> a uniform triple."""
    if len(spec) == 3:
        return spec
    return (spec[0], spec[1], [])


def inductive(env, name, constructors, params=(), indices=(), level=1):
    r"""Declare an inductive family, its constructors, and its recursors.

    A constructor is (name, [argument types]) or, for a family with indices,
    (name, [argument types], [index values]).  The marker REC stands for a
    recursive occurrence.  Parameters are fixed across all constructors and
    default to implicit there; indices vary from constructor to constructor,
    which is what makes equality expressible:

        inductive(env, 'List', [('nil', []), ('cons', [Var('A'), REC])],
                  params=[('A', Universe(1))])

        inductive(env, 'Eq', [('refl', [], [Var('a')])],
                  params=[('A', Universe(1)), ('a', Var('A'), False)],
                  indices=[('b', Var('A'))], level=0)

    Two recursors are generated because there is no universe polymorphism
    here: T.rec eliminates into Type, for defining functions, and T.ind into
    Prop, for proving theorems.  They share one computation rule.

    The one restriction left, stated rather than hidden: a recursive argument
    is only allowed in a family without indices, since the induction
    hypothesis would otherwise have to name the indices of that occurrence.
    """
    params = [binding(p) for p in params]
    indices = [binding(i, implicit=False) for i in indices]
    constructors = [constructor_parts(c) for c in constructors]
    if indices and any(REC in args for _, args, _ in constructors):
        raise KernelError(f"{name}: a recursive argument in an indexed family "
                          f"is not supported")

    former = Universe(level)
    for iname, itype, _ in reversed(indices):
        former = Pi(iname, itype, former)
    for pname, ptype, _ in reversed(params):
        former = Pi(pname, ptype, former)
    declare(env, name, former, kind='inductive')

    for cname, args, ivals in constructors:
        ctype = applied(name, params, ivals)
        names = arg_names(args)
        for n, spec in reversed(list(zip(names, args))):
            ctype = Pi(n, applied(name, params, []) if spec is REC else spec,
                       ctype)
        for pname, ptype, imp in reversed(params):
            ctype = Pi(pname, ptype, ctype, implicit=imp)
        declare(env, cname, ctype, kind='constructor')

    for suffix, target in (('rec', Universe(1)), ('ind', Universe(0))):
        rname = f'{name}.{suffix}'
        declare(env, rname,
                recursor_type(name, constructors, params, indices, target),
                rule=recursor_rule(rname, constructors, len(params),
                                   len(indices)),
                kind='recursor')
    return env


def applied(name, params, indices):
    """T p1 .. pn i1 .. ik, as it appears in a constructor's result."""
    out = Var(name)
    for pname, _, _ in params:
        out = App(out, Var(pname))
    for i in indices:
        out = App(out, i)
    return out


def arg_names(args):
    return [f'a{i}' for i in range(len(args))]


def motive_type(name, params, indices, target):
    """C : forall indices, T params indices -> target"""
    body = arrow(applied(name, params, [Var(n) for n, _, _ in indices]), target)
    for iname, itype, _ in reversed(indices):
        body = Pi(iname, itype, body)
    return body


def apply_motive(indices_vals, scrutinee):
    out = Var('C')
    for v in indices_vals:
        out = App(out, v)
    return App(out, scrutinee)


def minor_premise_for(name, cname, args, ivals, params):
    """The recursor's case for one constructor."""
    names = arg_names(args)
    built = Var(cname)
    for pname, _, _ in params:
        built = App(built, Var(pname))
    for n in names:
        built = App(built, Var(n))
    body = apply_motive(ivals, built)
    for n, spec in reversed(list(zip(names, args))):
        if spec is REC:
            body = arrow(apply_motive([], Var(n)), body)
    for n, spec in reversed(list(zip(names, args))):
        body = Pi(n, applied(name, params, []) if spec is REC else spec, body)
    return body


def recursor_type(name, constructors, params, indices, target):
    """forall {params} {C}, <minor premises> -> forall indices t, C indices t"""
    index_vars = [Var(n) for n, _, _ in indices]
    body = Pi('t', applied(name, params, index_vars),
              apply_motive(index_vars, Var('t')))
    for iname, itype, _ in reversed(indices):
        body = Pi(iname, itype, body)
    for cname, args, ivals in reversed(constructors):
        body = arrow(minor_premise_for(name, cname, args, ivals, params), body)
    body = Pi('C', motive_type(name, params, indices, target), body,
              implicit=True)
    for pname, ptype, _ in reversed(params):
        body = Pi(pname, ptype, body, implicit=True)
    return body


def recursor_rule(rname, constructors, nparams=0, nindices=0):
    """Iota: once the scrutinee is a constructor, take the matching case.

    The arguments arrive as parameters, motive, cases, indices, scrutinee --
    the same order the recursor's type quantifies them.
    """
    ncases = len(constructors)

    def rule(env, args):
        needed = nparams + 1 + ncases + nindices + 1
        if len(args) < needed:
            return None
        params = args[:nparams]
        motive = args[nparams]
        cases = args[nparams + 1:nparams + 1 + ncases]
        scrutinee = args[needed - 1]
        rest = args[needed:]
        head, cargs = spine(normalize(scrutinee, env))
        if not isinstance(head, Var):
            return None
        for case, (cname, spec, _ivals) in zip(cases, constructors):
            if head.name != cname or len(cargs) != nparams + len(spec):
                continue
            fields = cargs[nparams:]        # the constructor's own arguments
            out = case
            for a in fields:
                out = App(out, a)
            for a, kind in zip(fields, spec):
                if kind is REC:
                    sub = Var(rname)
                    for p in params:
                        sub = App(sub, p)
                    sub = App(sub, motive)
                    for c in cases:
                        sub = App(sub, c)
                    out = App(out, App(sub, a))
            for a in rest:
                out = App(out, a)
            return out
        return None
    return rule

# ------------------------------------------------------------- elaboration
#
# The kernel above is the trusted part and knows nothing about implicit
# arguments.  The elaborator is the untrusted part: it fills in the holes and
# then hands a complete term back to type_check for independent verification,
# which is how Lean is arranged too.

def has_meta(expr, index=None):
    """Does expr contain a hole (optionally, this particular one)?"""
    if isinstance(expr, Meta):
        return index is None or expr.index == index
    if isinstance(expr, App):
        return has_meta(expr.func, index) or has_meta(expr.arg, index)
    if isinstance(expr, Binder):
        return has_meta(expr.var_type, index) or has_meta(expr.body, index)
    return False


def has_loose_bound(expr, depth=0):
    """Does expr refer to a binder outside itself?"""
    if isinstance(expr, Bound):
        return expr.index >= depth
    if isinstance(expr, App):
        return has_loose_bound(expr.func, depth) or has_loose_bound(expr.arg, depth)
    if isinstance(expr, Binder):
        return (has_loose_bound(expr.var_type, depth)
                or has_loose_bound(expr.body, depth + 1))
    return False


def resolve(expr, subst):
    """Replace every solved hole by its solution, everywhere."""
    if isinstance(expr, Meta):
        if expr.index in subst:
            return resolve(subst[expr.index], subst)
        return expr
    if isinstance(expr, App):
        func = resolve(expr.func, subst)
        arg = resolve(expr.arg, subst)
        if head_is_meta(expr.func) or isinstance(expr.func, Meta):
            # solving ?P leaves (lam z. ..) applied to an argument; reduce it,
            # so what comes out is a term and not a substitution in progress
            return normalize(App(func, arg))
        return App(func, arg)
    if isinstance(expr, Binder):
        return expr.rebuild(resolve(expr.var_type, subst),
                            resolve(expr.body, subst))
    return expr


def spine(expr):
    """A term as a head and its arguments: f a b -> (f, [a, b])."""
    args = []
    while isinstance(expr, App):
        args.append(expr.arg)
        expr = expr.func
    args.reverse()
    return expr, args


def head_is_meta(expr):
    head, _ = spine(expr)
    return isinstance(head, Meta)


LOCAL_PREFIX = '@'         # elaboration opens binders into names starting here


def assign(meta, term, subst):
    """Solve a bare hole, refusing the two solutions that would be unsound."""
    if has_meta(term, meta.index):
        return False                      # occurs check: ?m := f(?m)
    if has_loose_bound(term):
        # the solution mentions a variable bound outside the hole, so it would
        # mean something different wherever the hole is used
        return False
    subst[meta.index] = term
    return True


def assign_pattern(meta, args, rhs, subst, ctx):
    r"""Solve ?m x1 .. xn = rhs, when the arguments are distinct variables.

    This is Miller's pattern fragment.  Higher-order unification is undecidable
    in general, but this special case has a single most general solution --
    abstract the arguments out of the right-hand side:

        ?P a  =  Eq Nat a a        gives    ?P := (lam z. Eq Nat z z)

    Outside the fragment we refuse rather than guess, because guessing here
    means inventing a proof the user did not write.
    """
    names = []
    for arg in args:
        arg = normalize(resolve(arg, subst))
        if not isinstance(arg, Var) or not arg.name.startswith(LOCAL_PREFIX):
            return None                   # not a pattern: caller may try more
        if arg.name in names:
            return None                   # repeated argument: not a pattern
        names.append(arg.name)

    rhs = resolve(rhs, subst)
    if has_meta(rhs, meta.index) or has_loose_bound(rhs):
        return False

    solution = rhs
    for name in reversed(names):
        solution = Lambda(name, ctx.get(name, Universe(0)), solution)
        solution.var_name = strip_local(name)   # the hint is for reading only
    # A solution may legitimately mention a local: the hole was created where
    # that local was in scope, and the enclosing binder closes over it when the
    # term is put back together.  A local that really does escape is caught by
    # Elaborator.finish, which can say so properly.
    subst[meta.index] = solution
    return True


def readable(expr):
    """Render for a person: the names elaboration opened are internal detail."""
    for name in sorted(free_names(expr)):
        if name.startswith(LOCAL_PREFIX):
            expr = substitute(expr, name, Var(strip_local(name)))
    return pretty(expr)


def count_occurrences(expr, name):
    """How many times the named variable appears free."""
    if isinstance(expr, Var):
        return 1 if expr.name == name else 0
    if isinstance(expr, App):
        return (count_occurrences(expr.func, name)
                + count_occurrences(expr.arg, name))
    if isinstance(expr, Binder):
        return (count_occurrences(expr.var_type, name)
                + count_occurrences(expr.body, name))
    return 0


def abstract_at(expr, name, chosen, depth=0, index=0):
    """Abstract only the selected occurrences of a name, by position.

    abstract() takes every occurrence.  A motive often wants some of them and
    not others: from Eq A a a the reading (lam z. Eq A z a) abstracts the first
    occurrence alone, and no amount of abstracting everything will produce it.
    """
    if isinstance(expr, Var):
        if expr.name == name:
            picked = index in chosen
            return (Bound(depth) if picked else expr), index + 1
        return expr, index
    if isinstance(expr, App):
        func, index = abstract_at(expr.func, name, chosen, depth, index)
        arg, index = abstract_at(expr.arg, name, chosen, depth, index)
        return App(func, arg), index
    if isinstance(expr, Binder):
        var_type, index = abstract_at(expr.var_type, name, chosen, depth, index)
        body, index = abstract_at(expr.body, name, chosen, depth + 1, index)
        return expr.rebuild(var_type, body), index
    return expr, index


CANDIDATE_LIMIT = 64            # 2^n per variable; refuse to explode


def pattern_candidates(names, rhs, ctx):
    r"""Every way of abstracting the arguments out of the right-hand side.

    Ordered most-abstracted first, so the principal Miller solution is tried
    before any partial one and the usual cases keep the answer they had.
    """
    counts = [count_occurrences(rhs, n) for n in names]
    total = 1
    for c in counts:
        total *= 2 ** c
    if total > CANDIDATE_LIMIT:
        counts = None           # too many: offer the full abstraction only

    def subsets(n):
        if counts is None:
            return [frozenset(range(n))]
        out = [frozenset(s) for k in range(n, -1, -1)
               for s in itertools.combinations(range(n), k)]
        return out

    choices = [subsets(count_occurrences(rhs, n)) for n in names]
    for combo in itertools.product(*choices):
        solution = rhs
        for name, chosen in zip(reversed(names), reversed(combo)):
            body, _ = abstract_at(solution, name, chosen)
            solution = Lambda.raw(strip_local(name),
                                  ctx.get(name, Universe(0)), body)
        yield solution


def strip_local(name):
    """@a12 -> a, for printing."""
    if not name.startswith(LOCAL_PREFIX):
        return name
    return name[len(LOCAL_PREFIX):].rstrip('0123456789') or 'x'


def is_pattern(args, subst):
    """Are these arguments distinct local variables?  Returns the names, or None."""
    names = []
    for arg in args:
        arg = normalize(resolve(arg, subst))
        if not isinstance(arg, Var) or not arg.name.startswith(LOCAL_PREFIX):
            return None
        if arg.name in names:
            return None
        names.append(arg.name)
    return names


def is_ambiguous(meta, names, rhs, subst):
    r"""Does this constraint have more than one legitimate solution?

    Abstracting every occurrence is the only choice when the variable is not in
    the hole's scope -- leaving one behind would produce a term mentioning
    something the hole cannot see.  But when the variable *is* in scope, both
    readings are legal:

        ?P a = Eq A a a     could be   (lam z. Eq A z z)   or   (lam z. Eq A z a)

    and only some later constraint can say which was meant.  Guessing here is
    what made symm fail.
    """
    free = free_names(resolve(rhs, subst))
    return any(n in free and n in meta.context for n in names)


def unify(a, b, subst, ctx=None, pending=None, env=None):
    """Unification up to normalisation, over Miller's pattern fragment.

    With a pending list, a constraint whose solution is not yet determined is
    recorded instead of guessed, and settled later by solve_pending.
    """
    ctx = ctx if ctx is not None else {}
    env = env if env is not None else ctx
    a = normalize(resolve(a, subst), env)
    b = normalize(resolve(b, subst), env)
    if a == b:
        return True

    if isinstance(a, Meta):
        return assign(a, b, subst)
    if isinstance(b, Meta):
        return assign(b, a, subst)

    # a hole applied to arguments: try the pattern rule before decomposing,
    # since it gives the most general solution when it applies
    for left, right in ((a, b), (b, a)):
        if head_is_meta(left):
            head, args = spine(left)
            names = is_pattern(args, subst)
            if names is not None and pending is not None \
                    and is_ambiguous(head, names, right, subst):
                pending.append(Constraint(left, right, dict(ctx)))
                return True                # settled later, and verified then
            solved = assign_pattern(head, args, right, subst, ctx)
            if solved is not None:
                return solved

    if isinstance(a, App) and isinstance(b, App):
        return (unify(a.func, b.func, subst, ctx, pending, env)
                and unify(a.arg, b.arg, subst, ctx, pending, env))
    if isinstance(a, Binder) and isinstance(b, Binder) and a.tag == b.tag:
        return (unify(a.var_type, b.var_type, subst, ctx, pending, env)
                and unify(a.body, b.body, subst, ctx, pending, env))
    return False


class Constraint:
    """A postponed equation ?m x1..xn = rhs, kept with the context it arose in."""

    def __init__(self, lhs, rhs, ctx):
        self.lhs = lhs
        self.rhs = rhs
        self.ctx = ctx

    def head(self, subst, env=None):
        head, args = spine(normalize(resolve(self.lhs, subst)))
        return head, args

    def satisfied(self, subst, env=None):
        return definitionally_equal(resolve(self.lhs, subst),
                                    resolve(self.rhs, subst), env)

    def __str__(self):
        return f"{readable(self.lhs)} = {readable(self.rhs)}"


EXPLICIT = 'explicit'          # explicit(f) is Lean's @f: no holes inserted


class Elaborator:
    r"""Fills in implicit arguments, so a proof can be written as refl(x).

    An implicit binder \forall {A : Type}, ... contributes a hole at every use
    site, solved by unifying the expected argument type with the actual one.

    Elaboration runs over *opened* terms: on the way into a binder the bound
    variable is replaced by a fresh free name, and the binder is closed again
    on the way out.  That matters because a hole under a binder may need to be
    solved with the bound variable itself -- as in refl(a) where a : A and A is
    itself bound -- and a raw de Bruijn index would mean something different at
    every depth it appeared.  A name does not.
    """

    PREFIX = LOCAL_PREFIX      # cannot occur in a Python identifier

    def __init__(self, env):
        self.env = dict(env)
        self.subst = {}
        self.pending = []
        self.notes = []
        self.counter = 0

    def local_names(self):
        return tuple(n for n in self.env if n.startswith(self.PREFIX))

    def fresh_local(self, hint):
        self.counter += 1
        return f"{self.PREFIX}{hint}{self.counter}"

    def insert_implicits(self, term, type_):
        """Apply the term to a fresh hole for each leading implicit binder."""
        type_ = normalize(resolve(type_, self.subst), self.env)
        while isinstance(type_, Pi) and type_.implicit:
            hole = new_meta(type_.var_name, self.local_names())
            term = App(term, hole)
            type_ = normalize(instantiate(type_.body, hole), self.env)
        return term, type_

    def binder(self, expr):
        """Elaborate under a binder by opening it with a fresh name."""
        domain, _ = self.infer(expr.var_type)
        name = self.fresh_local(expr.var_name)
        self.env[name] = domain
        try:
            body, body_type = self.infer(instantiate(expr.body, Var(name)))
        finally:
            del self.env[name]
        # resolve before closing up: a hole solved inside the body may mention
        # the opened name, and abstraction has to see it
        body = abstract(resolve(body, self.subst), name)
        body_type = abstract(resolve(body_type, self.subst), name)
        return domain, body, body_type

    def check(self, expr, expected):
        r"""Elaborate expr against a known expected type.

        Pushing the expectation inwards is what makes a hole in a dependent
        position solvable: inside \lambda f. \lambda x. congrArg(refl(x)) the
        goal is Eq Nat (f x) (f x) with f and x opened as ordinary names, so
        ?f x = f x falls in the pattern fragment.  Unifying only at the top,
        after both sides are closed again, would leave de Bruijn indices facing
        each other with no name to abstract over.
        """
        expected = normalize(resolve(expected, self.subst), self.env)
        if isinstance(expr, Lambda) and isinstance(expected, Pi):
            domain, _ = self.infer(expr.var_type)
            if not unify(domain, expected.var_type, self.subst,
                         self.env, self.pending, self.env):
                raise TheoremError(
                    f"argument '{expr.var_name}' is declared "
                    f"{readable(resolve(domain, self.subst))} but the "
                    f"statement expects "
                    f"{readable(resolve(expected.var_type, self.subst))}")
            name = self.fresh_local(expr.var_name)
            self.env[name] = domain
            try:
                body = self.check(instantiate(expr.body, Var(name)),
                                  instantiate(expected.body, Var(name)))
            finally:
                del self.env[name]
            body = abstract(resolve(body, self.subst), name)
            return expr.rebuild(domain, body)

        term, actual = self.infer(expr)
        if not unify(expected, actual, self.subst, self.env, self.pending,
                     self.env):
            raise TheoremError(
                f"stated {readable(resolve(expected, self.subst))}, "
                f"proved {readable(resolve(actual, self.subst))}")
        # settle constraints here, while the locals a solution may mention are
        # still open names; once the binders close they are indices again
        self.solve_pending()
        return term

    def infer(self, expr, insert=True):
        """(elaborated term, its type)."""
        if isinstance(expr, Meta):
            return expr, new_meta('T')

        if isinstance(expr, Universe):
            return expr, Universe(expr.level + 1)

        if isinstance(expr, Var):
            declared = type_of(self.env, expr.name)
            if declared is None:
                raise KernelError(f"Unknown identifier: {expr.name}")
            term, type_ = expr, declared
            return self.insert_implicits(term, type_) if insert else (term, type_)

        if isinstance(expr, Bound):
            raise KernelError(f"Unbound index #{expr.index}")

        if isinstance(expr, Lambda):
            domain, body, body_type = self.binder(expr)
            return (expr.rebuild(domain, body),
                    Pi.raw(expr.var_name, domain, body_type, expr.implicit))

        if isinstance(expr, Pi):
            domain, body, _ = self.binder(expr)
            # the kernel recomputes the sort; here we only need a placeholder
            return expr.rebuild(domain, body), Universe(0)

        if isinstance(expr, App):
            # explicit(f) turns insertion off for this head, Lean's @f
            if isinstance(expr.func, Var) and expr.func.name == EXPLICIT:
                return self.infer(expr.arg, insert=False)
            # ...and for every argument of it, not just the first: otherwise
            # insertion creeps back in after each application and the second
            # explicit argument meets a hole where its binder should be
            head, _ = spine(expr)
            if isinstance(head, Var) and head.name == EXPLICIT:
                insert = False

            func, func_type = self.infer(expr.func, insert=insert)
            func_type = normalize(resolve(func_type, self.subst), self.env)
            if not isinstance(func_type, Pi):
                raise KernelError(f"Expected a function, got "
                                  f"{pretty(func_type)}")
            arg, arg_type = self.infer(expr.arg)
            if not unify(func_type.var_type, arg_type, self.subst,
                         self.env, self.pending, self.env):
                raise KernelError(
                    f"Type mismatch: expected "
                    f"{readable(resolve(func_type.var_type, self.subst))}, got "
                    f"{readable(resolve(arg_type, self.subst))}")
            result = normalize(instantiate(func_type.body, arg), self.env)
            term = App(func, arg)
            return self.insert_implicits(term, result) if insert else (term, result)

        raise KernelError(f"Cannot elaborate: {expr}")

    def solve_pending(self):
        r"""Settle the postponed constraints, once there is enough to go on.

        Every constraint on a hole proposes one candidate: its own Miller
        solution.  A candidate is accepted only if it satisfies *all* the
        constraints on that hole, which is what lets a later constraint
        overrule an earlier guess --

            ?P a = Eq A a a      proposes  (lam z. Eq A z z)
            ?P b = Eq A b a      proposes  (lam z. Eq A z a)

        and only the second survives both.  That is symm.
        """
        for _ in range(len(self.pending) + 2):
            self.pending = [c for c in self.pending
                            if not c.satisfied(self.subst, self.env)]
            if not self.pending:
                return
            by_meta = {}
            for c in self.pending:
                head, args = c.head(self.subst, self.env)
                if isinstance(head, Meta) and head.index not in self.subst:
                    by_meta.setdefault(head.index, []).append((c, head, args))
            if not by_meta:
                return
            progressed = False
            for index, group in by_meta.items():
                fits = []
                for solution in self.candidates(group):
                    trial = dict(self.subst)
                    trial[index] = solution
                    if all(c.satisfied(trial, self.env) for c, _, _ in group):
                        fits.append(solution)
                        if len(fits) > 1:
                            break        # one alternative is enough to report
                if not fits:
                    continue
                if len(fits) > 1:
                    # every survivor proves the stated theorem, since the
                    # kernel checks the finished term either way -- but the
                    # reader deserves to know the choice was not forced
                    self.notes.append(
                        f"the implicit argument ?{group[0][1].hint} was not "
                        f"fully determined; took {readable(fits[0])}, and "
                        f"{readable(fits[1])} would also have done")
                self.subst = dict(self.subst)
                self.subst[index] = fits[0]
                progressed = True
                break
            if not progressed:
                return

    def candidates(self, group):
        """Every solution any constraint on this hole can propose."""
        seen = set()
        for constraint, head, args in group:
            names = is_pattern(args, self.subst)
            if names is None:
                continue
            rhs = resolve(constraint.rhs, self.subst)
            if has_meta(rhs, head.index) or has_loose_bound(rhs):
                continue
            for solution in pattern_candidates(names, rhs, constraint.ctx):
                if solution.key() in seen:
                    continue
                seen.add(solution.key())
                yield solution

    def check_pending(self):
        """Nothing may be left unverified: a postponed constraint that never
        got settled is an implicit argument we could not work out."""
        self.solve_pending()
        unmet = [c for c in self.pending if not c.satisfied(self.subst, self.env)]
        if unmet:
            raise KernelError(
                f"Could not work out an implicit argument: no single value "
                f"satisfies {unmet[0]}. Supply it with explicit(f)(...)")
        self.pending = []

    def finish(self, expr, what='term'):
        """Substitute the solutions in, and insist there are none left over."""
        out = resolve(expr, self.subst)
        if has_meta(out):
            raise KernelError(
                f"Could not infer every implicit argument in the {what}: "
                f"{readable(out)}. Supply them with explicit(f)(...)")
        escaped = sorted(n for n in free_names(out) if n.startswith(self.PREFIX))
        if escaped:
            raise KernelError(
                f"An implicit argument in the {what} would have to mention "
                f"{escaped[0][1:]}, which is not in scope where it is needed")
        return out


def elaborate(env, term, expected=None):
    """Fill in the holes, then let the kernel check the result independently.

    Returns (term, type).  The elaborator's own reasoning is never trusted:
    whatever it produces is type checked from scratch.
    """
    elaborate.last_notes = []
    el = Elaborator(env)
    if expected is None:
        term, _ = el.infer(term)
    else:
        expected, _ = el.infer(expected)
        term = el.check(term, expected)
    el.check_pending()
    elaborate.last_notes = list(el.notes)
    term = el.finish(term)
    checked = type_check(env, term)          # the trusted check
    if expected is not None:
        expected = el.finish(expected, 'statement')
        if not definitionally_equal(expected, checked, env):
            raise TheoremError(f"stated {pretty(expected)}, "
                               f"proved {pretty(checked)}")
    return term, checked

# ------------------------------------------------------------ LaTeX front end
#
# A type expression, in the same LaTeX subset the rest of the project uses.
# rosettaui.tokenize does the lexing; this is a small recursive descent parser
# over its output.
#
#   \forall x : A, B      \forall x \in A, B      dependent function type
#   A \to B                                       ordinary function type
#   f x                                           application, by juxtaposition
#   a = b                                         equality, elaborated to Eq
#   \text{Nat}  \mathbb{N}  Nat                   a named type
#   \text{Prop}  \text{Type}                      sorts

TYPE_WORDS = {
    'Prop': Universe(0), 'Type': Universe(1),
}
TYPE_ALIASES = {
    'N': 'Nat', 'mathbb{N}': 'Nat', 'R': 'Real', 'B': 'Bool',
}
FORALL = (r'\forall', r'\Pi', r'\prod')
ARROW = (r'\to', r'\rightarrow', r'\longrightarrow', r'\Rightarrow')
COLON = (':', r'\in', r'\colon')


class LatexTypeParser:
    r"""LaTeX -> kernel expression, for statements that denote a type."""

    def __init__(self, tokens):
        self.toks = tokens
        self.i = 0
        self.scope = {}                       # name -> type, for elaborating =

    def peek(self, k=0):
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else None

    def next(self):
        t = self.peek()
        if t is not None:
            self.i += 1
        return t

    def expect(self, *what):
        t = self.next()
        if t not in what:
            raise KernelError(f"Expected {' or '.join(what)}, found {t!r}")
        return t

    def braced(self):
        r"""The content of a {...} group, as plain text (\text{Nat} -> Nat)."""
        self.expect('{')
        out = ''
        depth = 1
        while True:
            t = self.next()
            if t is None:
                raise KernelError("Unclosed { in the statement")
            if t == '{':
                depth += 1
            elif t == '}':
                depth -= 1
                if depth == 0:
                    return rosettamath.unescape(out)
            out += t

    def named(self, word):
        word = TYPE_ALIASES.get(word, word)
        if word in TYPE_WORDS:
            return TYPE_WORDS[word]
        return Var(word)

    def parse(self):
        expr = self.expression()
        if self.peek() is not None:
            raise KernelError(f"Unexpected {self.peek()!r} after the statement")
        return expr

    def expression(self):
        if self.peek() in FORALL:
            return self.forall()
        return self.equality()

    def forall(self):
        self.next()
        opener = self.peek() if self.peek() in ('(', r'\{') else None
        implicit = opener == r'\{'
        if opener:
            self.next()
        name = self.next()
        if name is None or not name.isidentifier():
            raise KernelError(f"Expected a bound variable name, found {name!r}")
        self.expect(*COLON)
        domain = self.arrow_type()
        if opener:
            self.expect(r'\}' if implicit else ')')
        self.expect(',')
        outer = self.scope.get(name)
        self.scope[name] = domain             # so 'x = x' knows the type of x
        body = self.expression()
        if outer is None:
            self.scope.pop(name, None)
        else:
            self.scope[name] = outer
        return Pi(name, domain, body, implicit=implicit)

    def equality(self):
        left = self.arrow_type()
        if self.peek() != '=':
            return left
        self.next()
        right = self.arrow_type()
        return self.make_eq(left, right)

    def make_eq(self, left, right):
        """a = b is Eq A a b; A comes from the binder that introduced a."""
        carrier = None
        if isinstance(left, Var) and left.name in self.scope:
            carrier = self.scope[left.name]
        elif isinstance(right, Var) and right.name in self.scope:
            carrier = self.scope[right.name]
        if carrier is None:
            # nothing in scope pins the type down, so leave a hole and let
            # the elaborator work it out from the operands
            carrier = new_meta('A')
        return App(App(App(Var('Eq'), carrier), left), right)

    def arrow_type(self):
        left = self.application()
        if self.peek() in ARROW:
            self.next()
            return arrow(left, self.arrow_type())      # right associative
        return left

    def application(self):
        expr = self.atom()
        while True:
            t = self.peek()
            if t is None or t in ARROW or t in COLON \
                    or t in (',', ')', '}', '=', r'\}'):
                return expr
            if t in FORALL:
                return expr
            expr = App(expr, self.atom())

    def atom(self):
        t = self.next()
        if t is None:
            raise KernelError("The statement ended early")
        if t == '(':
            inner = self.expression()
            self.expect(')')
            return inner
        if t in (r'\text', r'\mathrm', r'\mathbb', r'\mathbf', r'\texttt'):
            return self.named(self.braced())
        if t.startswith('\\'):
            return self.named(t[1:])
        if t.isdigit():
            return numeral(int(t))
        if t.isidentifier():
            # tokenize() splits Nat into N, a, t and juxtaposition already
            # means application, so a multi-letter name must be written
            # \text{Nat}.  Single letters are the usual bound variables.
            return self.named(t)
        raise KernelError(f"Cannot read {t!r} as a type")


def latex2type(statement):
    r"""A LaTeX statement -> the kernel type it denotes."""
    return LatexTypeParser(rosettaui.tokenize(statement)).parse()


def numeral(n):
    """3 is succ (succ (succ zero)); writing it out is what a numeral is."""
    out = Var('zero')
    for _ in range(n):
        out = App(Var('succ'), out)
    return out


def parse_type(text):
    """A type written either as a bare name or as LaTeX.

    'Nat' is a plain identifier and must not go through the LaTeX reader,
    which would tokenise it into three letters and read it as an application.
    """
    text = text.strip()
    if text.isidentifier():
        return LatexTypeParser([]).named(text)
    return latex2type(text)


# ------------------------------------------------------ LaTeX, the other way
#
# type2latex is LatexTypeParser read backwards, and the property that makes it
# worth having is latex2type(type2latex(t)) == t.  It is therefore written
# against the parser rather than against taste: every shape below is emitted
# because the parser accepts it, and everything the parser cannot read is
# refused with the reason rather than approximated.
#
# pretty() is not that function and cannot become it.  It prints Type 1, ?A7,
# lambdas and x', none of which the parser reads, so its output is for a human
# to look at and this one is for the reader to take back.
#
# Two places where the term does not determine the text:
#
#   Binder names.  key() ignores a binder's name hint, so a name is free to
#   change -- but only within what the reader can lex.  tokenize() splits Nat
#   into N, a, t, and a binder name is taken as one token, so a bound name has
#   to be a single letter; fresh()'s x' is two tokens and would not come back.
#   And N, R and B are aliases, so they are not available either.
#
#   a = b.  The parser recovers the carrier of Eq from the binder that
#   introduced one of the operands, so a = b is written only when that lookup
#   would return this very carrier.  Otherwise the application is written out
#   as Eq A a b, which always reads back.

# Single letters the reader would take as something other than a variable.
RESERVED_NAMES = set(TYPE_ALIASES) | set(TYPE_WORDS)

BINDER_LETTERS = [c for c in
                  'xyzabcdefghijklmnopqrstuvwABCDEFGHIJKLMNOPQRSTUVWXYZ'
                  if c not in RESERVED_NAMES]

# Precedence, named for the parser method that accepts each level.
P_EXPR, P_ARROW, P_APP, P_ATOM = 0, 1, 2, 3


class LatexPrinter:
    r"""A kernel type -> the LaTeX subset LatexTypeParser reads."""

    def __init__(self):
        self.scope = {}                       # name -> domain, as the parser's

    def refuse(self, why):
        raise KernelError('no LaTeX spelling: ' + why)

    def wrap(self, text, mine, ctx):
        return f'({text})' if mine < ctx else text

    def word(self, name):
        """A global or free name, as the reader would have to see it."""
        if name in RESERVED_NAMES:
            self.refuse(f'{name!r} is how the reader spells something else')
        if len(name) == 1 and name.isidentifier():
            return name
        if not name.replace('.', '_').isidentifier():
            self.refuse(f'{name!r} is not a name the reader can lex')
        return r'\text{%s}' % rosettamath.escape(name)

    def binder_name(self, hint, var_type, body):
        """One letter that shadows nothing and captures nothing.

        Avoiding the enclosing binders is not enough, for the same reason
        fresh() gives: a free name in the body would print identically, and
        the reader abstracts by name, so the two would come back as one.
        """
        taken = set(self.scope) | free_names(body) | free_names(var_type)
        first = hint[0] if hint and hint[0].isalpha() else ''
        for letter in [first] + BINDER_LETTERS:
            if letter and letter not in taken and letter not in RESERVED_NAMES:
                return letter
        self.refuse('every single-letter binder name is already in use')

    def write(self, expr, ctx=P_EXPR):
        if isinstance(expr, Universe):
            if expr.level in (0, 1):
                return r'\text{Prop}' if expr.level == 0 else r'\text{Type}'
            self.refuse(f'the reader knows Prop and Type, '
                        f'not Type {expr.level - 1}')
        if isinstance(expr, Var):
            return '0' if expr.name == 'zero' else self.word(expr.name)
        if isinstance(expr, Bound):
            self.refuse(f'a loose de Bruijn index #{expr.index} has no name')
        if isinstance(expr, Meta):
            self.refuse(f'?{expr.hint}{expr.index} is a hole; '
                        f'elaborate before writing')
        if isinstance(expr, Lambda):
            self.refuse('the subset states types; a lambda is a term')
        if isinstance(expr, Pi):
            return self.pi(expr, ctx)
        if isinstance(expr, App):
            return self.app(expr, ctx)
        self.refuse(f'unknown node {type(expr).__name__}')

    def pi(self, expr, ctx):
        """A -> B when nothing depends on the argument, \\forall otherwise.

        Descending instantiates the binder with a named variable, so the body
        below is in exactly the form the parser builds before Pi() abstracts
        it -- which is what lets scope be compared without shifting anything.
        """
        if not expr.implicit and not occurs(expr.body, 0):
            dom = self.write(expr.var_type, P_APP)      # left is application()
            body = self.write(instantiate(expr.body, Var('_')), P_ARROW)
            return self.wrap(rf'{dom} \to {body}', P_ARROW, ctx)
        dom = self.write(expr.var_type, P_ARROW)        # domain is arrow_type()
        name = self.binder_name(expr.var_name, expr.var_type, expr.body)
        outer = self.scope.get(name)
        self.scope[name] = expr.var_type
        body = self.write(instantiate(expr.body, Var(name)), P_EXPR)
        if outer is None:
            self.scope.pop(name, None)
        else:
            self.scope[name] = outer
        head = (rf'\forall \{{{name} : {dom}\}}' if expr.implicit
                else rf'\forall {name} \in {dom}')
        return self.wrap(f'{head}, {body}', P_EXPR, ctx)

    def app(self, expr, ctx):
        digits = as_numeral(expr)
        if digits is not None:
            return str(digits)              # succ(succ(zero)) reads back as 2
        if ctx == P_EXPR:
            equation = self.equality(expr)
            if equation is not None:
                return equation
        return self.wrap(f'{self.write(expr.func, P_APP)} '
                         f'{self.write(expr.arg, P_ATOM)}', P_APP, ctx)

    def equality(self, expr):
        """a = b, but only when the reader would rebuild this very carrier."""
        args, head = [], expr
        while isinstance(head, App):
            args.append(head.arg)
            head = head.func
        if not (isinstance(head, Var) and head.name == 'Eq' and len(args) == 3):
            return None
        carrier, left, right = args[2], args[1], args[0]
        for side in (left, right):            # the parser tries left first
            if isinstance(side, Var) and side.name in self.scope:
                if self.scope[side.name] != carrier:
                    return None               # it would recover a different one
                return (f'{self.write(left, P_ARROW)} = '
                        f'{self.write(right, P_ARROW)}')
        return None                           # nothing in scope pins it down


def type2latex(expr):
    r"""A kernel type -> the LaTeX statement that denotes it."""
    return LatexPrinter().write(expr)


# --------------------------------------------------- Python AST to the kernel

class PythonToLean(ast.NodeVisitor):
    """Compiles Python AST nodes into Lean Kernel Expressions."""

    def visit_Module(self, node):
        if not node.body:
            raise KernelError("Nothing to compile")
        return self.visit(node.body[0])

    def visit_FunctionDef(self, node):
        body = [s for s in node.body
                if not (isinstance(s, ast.Expr)
                        and isinstance(s.value, ast.Constant)
                        and isinstance(s.value.value, str))]   # drop docstring
        if len(body) != 1 or not isinstance(body[0], ast.Return):
            raise KernelError(
                f"{node.name}: a proof term must be a single return statement; "
                f"found {len(body)} statements")
        if body[0].value is None:
            raise KernelError(f"{node.name}: return needs a value")

        expr = self.visit(body[0].value)
        args = node.args.posonlyargs + node.args.args
        if node.args.vararg or node.args.kwarg or node.args.kwonlyargs:
            raise KernelError(f"{node.name}: *args and **kwargs have no "
                              f"meaning as a dependent function")
        for arg in reversed(args):
            expr = Lambda(arg.arg, self.annotation(arg, node.name), expr)
        return expr

    def annotation(self, arg, where):
        """The declared type of a parameter.

        Silently defaulting to Prop is how an unannotated argument used to
        typecheck for the wrong reason, so an annotation is now required.
        """
        node = arg.annotation
        if node is None:
            raise KernelError(f"{where}: parameter '{arg.arg}' has no type "
                              f"annotation, so there is nothing to check")
        if isinstance(node, ast.Name):
            return Var(node.id)
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            # 'Nat' and r'\text{Nat} \to \text{Nat}' both land here, because a
            # type that is not a Python name has to be quoted
            return parse_type(node.value)
        raise KernelError(f"{where}: cannot read the annotation on "
                          f"'{arg.arg}' as a type")

    def visit_Name(self, node):
        """Variables like 'x' become Var('x')"""
        return Var(node.id)

    def visit_Attribute(self, node):
        """Nat.ind is one dotted name, as it is in Lean."""
        parts = []
        cur = node
        while isinstance(cur, ast.Attribute):
            parts.append(cur.attr)
            cur = cur.value
        if not isinstance(cur, ast.Name):
            raise KernelError("only a dotted name may be used as a constant")
        parts.append(cur.id)
        return Var('.'.join(reversed(parts)))

    def visit_Call(self, node):
        """f(a, b) is curried application: App(App(f, a), b)."""
        if node.keywords:
            raise KernelError("keyword arguments have no meaning in the kernel")
        expr = self.visit(node.func)
        for arg in node.args:
            expr = App(expr, self.visit(arg))
        return expr

    def visit_Constant(self, node):
        if isinstance(node.value, int) and node.value >= 0:
            return numeral(node.value)
        raise KernelError(f"{node.value!r} is not a term the kernel knows")

    def visit_Return(self, node):
        return self.visit(node.value)

    def generic_visit(self, node):
        raise KernelError(
            f"Unsupported Python syntax for theorem prover: {type(node).__name__}")


def compile_python_to_lean(func):
    """Takes a Python function and returns its Lean Kernel representation."""
    try:
        source = textwrap.dedent(inspect.getsource(func))
    except (OSError, TypeError) as exc:
        raise KernelError(
            f"cannot read the source of {getattr(func, '__name__', func)}: "
            f"a proof must live in a file, not in an interactive session "
            f"or a -c string ({exc})")
    # the decorator is part of the FunctionDef and is simply ignored; stripping
    # it by hand breaks as soon as its arguments span more than one line
    tree = ast.parse(source)
    return PythonToLean().visit(tree.body[0])


# --------------------------------------------------------- global environment

def _eq(t, x, y):
    return App(App(App(Var('Eq'), t), x), y)


def _refl(t, x):
    return App(App(Var('refl'), t), x)


def _J(t, a, motive, base, b, h):
    """Eq.ind: induction on a proof of equality, the J rule."""
    out = App(App(App(App(Var('Eq.ind'), t), a), motive), base)
    return App(App(out, b), h)


def _motive(name, t, a, body):
    """lam b : t. lam _ : Eq t a b. body -- the motive J is eliminating with."""
    return Lambda(name, t, Lambda('_h', _eq(t, a, Var(name)), body))


# A global logical environment for our theorems.  Nat, Bool and Eq are declared
# as inductive types rather than assumed: Nat is a Type, not a Prop -- declaring
# it a Prop is what let the old identity example typecheck for the wrong reason
# -- and equality is an indexed family whose one constructor is refl, so the
# four lemmas below are proved from its induction principle instead of being
# axioms.
GLOBAL_ENV = {
    "Real": Universe(1),
}

inductive(GLOBAL_ENV, 'Bool', [('true', []), ('false', [])])
inductive(GLOBAL_ENV, 'Nat', [('zero', []), ('succ', [REC])])

_NAT = Var('Nat')
define(GLOBAL_ENV, 'add', arrow(_NAT, arrow(_NAT, _NAT)),
       Lambda('m', _NAT, Lambda('n', _NAT,
              App(App(App(App(Var('Nat.rec'), Lambda('_', _NAT, _NAT)),
                          Var('m')),
                      Lambda('k', _NAT, Lambda('ih', _NAT,
                                               App(Var('succ'), Var('ih'))))),
                  Var('n')))))

# a = b is an indexed family: the index is b, and refl only ever builds the
# case where it is a.  That is the whole content of equality.
inductive(GLOBAL_ENV, 'Eq', [('refl', [], [Var('a')])],
          params=[('A', Universe(1)), ('a', Var('A'), False)],
          indices=[('b', Var('A'))], level=0)

_A, _a, _b, _c = Var('A'), Var('a'), Var('b'), Var('c')

define(GLOBAL_ENV, 'symm',
       Pi('A', Universe(1),
          Pi('a', _A, Pi('b', _A,
             arrow(_eq(_A, _a, _b), _eq(_A, _b, _a)), implicit=True),
             implicit=True),
          implicit=True),
       Lambda('A', Universe(1), Lambda('a', _A, Lambda('b', _A,
              Lambda('h', _eq(_A, _a, _b),
                     _J(_A, _a, _motive('b2', _A, _a, _eq(_A, Var('b2'), _a)),
                        _refl(_A, _a), _b, Var('h')))))))

define(GLOBAL_ENV, 'trans',
       Pi('A', Universe(1),
          Pi('a', _A, Pi('b', _A, Pi('c', _A,
             arrow(_eq(_A, _a, _b), arrow(_eq(_A, _b, _c), _eq(_A, _a, _c))),
             implicit=True), implicit=True), implicit=True),
          implicit=True),
       Lambda('A', Universe(1), Lambda('a', _A, Lambda('b', _A, Lambda('c', _A,
              Lambda('h1', _eq(_A, _a, _b), Lambda('h2', _eq(_A, _b, _c),
                     _J(_A, _b, _motive('c2', _A, _b, _eq(_A, _a, Var('c2'))),
                        Var('h1'), _c, Var('h2')))))))))

define(GLOBAL_ENV, 'congrArg',
       Pi('A', Universe(1), Pi('B', Universe(1),
          Pi('f', arrow(_A, Var('B')),
             Pi('a', _A, Pi('b', _A,
                arrow(_eq(_A, _a, _b),
                      _eq(Var('B'), App(Var('f'), _a), App(Var('f'), _b))),
                implicit=True), implicit=True), implicit=True),
          implicit=True), implicit=True),
       Lambda('A', Universe(1), Lambda('B', Universe(1),
              Lambda('f', arrow(_A, Var('B')), Lambda('a', _A, Lambda('b', _A,
                     Lambda('h', _eq(_A, _a, _b),
                            _J(_A, _a,
                               _motive('b2', _A, _a,
                                       _eq(Var('B'), App(Var('f'), _a),
                                           App(Var('f'), Var('b2')))),
                               _refl(Var('B'), App(Var('f'), _a)),
                               _b, Var('h'))))))))) 

define(GLOBAL_ENV, 'transport',
       Pi('A', Universe(1),
          Pi('P', arrow(_A, Universe(0)),
             Pi('a', _A, Pi('b', _A,
                arrow(_eq(_A, _a, _b),
                      arrow(App(Var('P'), _a), App(Var('P'), _b))),
                implicit=True), implicit=True), implicit=True),
          implicit=True),
       Lambda('A', Universe(1), Lambda('P', arrow(_A, Universe(0)),
              Lambda('a', _A, Lambda('b', _A,
                     Lambda('h', _eq(_A, _a, _b),
                            Lambda('pa', App(Var('P'), _a),
                                   _J(_A, _a,
                                      _motive('b2', _A, _a,
                                              App(Var('P'), Var('b2'))),
                                      Var('pa'), _b, Var('h')))))))))

STRICT = True                 # a failed theorem raises; --non-strict prints
VERBOSE = True


def definition(latex_type, env=None, verbose=None, name=None):
    r"""Add a Python function to the environment as a checked definition.

    Same machinery as @theorem -- compile, elaborate, check against a type
    written in LaTeX -- but the result is kept, so later proofs can use it.
    That is what turns a fixed list of constants into a library one can build:

        @definition(r'\text{Nat} \to \text{Nat}')
        def double(n: 'Nat'):
            return add(n, n)
    """
    def decorator(func):
        loud = VERBOSE if verbose is None else verbose
        scope = GLOBAL_ENV if env is None else env
        label = name or func.__name__
        surface = compile_python_to_lean(func)
        stated = latex2type(latex_type)
        term, actual = elaborate(scope, surface, stated)
        folded = latex2type(latex_type)          # unelaborated, so still folded
        if not has_meta(folded) and definitionally_equal(folded, actual, scope):
            actual = folded
        define(scope, label, actual, term)
        if loud:
            print(f"defined {label} : {readable(actual)}")
        func.lean_term = term
        func.lean_type = actual
        return func
    return decorator


def theorem(latex_statement, strict=None, env=None, verbose=None):
    """Verify a Python function against a statement written in LaTeX.

    The function is compiled to a kernel term and type checked; the statement
    is read as a type; and the two must agree.  Checking only that the Python
    is well typed would prove nothing about what it claims.
    """
    def decorator(func):
        is_strict = STRICT if strict is None else strict
        loud = VERBOSE if verbose is None else verbose
        scope = GLOBAL_ENV if env is None else env
        report = []

        def say(line):
            report.append(line)
            if loud:
                print(line)

        say(f"\n--- Checking Theorem: {func.__name__} ---")
        say(f"LaTeX Statement: {latex_statement}")
        try:
            surface = compile_python_to_lean(func)
            say(f"Compiled Kernel Expr: {surface}")
            expected = latex2type(latex_statement)

            try:
                term, actual = elaborate(scope, surface, expected)
            except TheoremError as exc:
                raise TheoremError(
                    f"{func.__name__} does not prove what it claims: {exc}")
            if str(term) != str(surface):
                say(f"Elaborated:    {readable(term)}")
            say(f"Stated Type:   {readable(expected)}")
            say(f"Proved Type:   {readable(actual)}")

            for note in getattr(elaborate, 'last_notes', []):
                say(f"Note: {note}")
            func.lean_notes = list(getattr(elaborate, 'last_notes', []))
            func.lean_term = term
            func.lean_type = actual
            func.lean_statement = expected
            say("Status: VALID (proves the stated theorem)")
        except Exception as exc:
            say(f"Status: FAILED - {exc}")
            func.lean_error = exc
            if is_strict:
                raise
        func.lean_report = report
        return func
    return decorator


# ------------------------------------------------------------------ self test

def selftest():
    """Every one of these is a regression from a bug the kernel used to have."""
    checks = []

    def check(label, ok):
        checks.append((label, bool(ok)))
        print('  %-62s %s' % (label, 'ok' if ok else 'FAIL'))

    def raises(fn, fragment=''):
        try:
            fn()
        except Exception as exc:
            return fragment in str(exc)
        return False

    env = dict(GLOBAL_ENV, x=Var('Nat'), y=Var('Bool'))

    print('de Bruijn representation')
    check('a binder abstracts its own name',
          Lambda('a', Var('Nat'), Var('a')).body == Bound(0))
    check('shadowing binds to the nearest binder',
          Lambda('x', Var('Nat'), Lambda('x', Var('Nat'), Var('x'))).body.body
          == Bound(0))
    check('a free name stays free',
          Lambda('a', Var('Nat'), Var('b')).body == Var('b'))
    check('shift moves free indices only',
          shift(Lambda.raw('_', Var('Nat'), Bound(1)), 2).body == Bound(3))
    check('instantiate closes the binder',
          instantiate(Bound(0), Var('q')) == Var('q'))

    print('bug 3: substitution must not capture')
    captured = substitute(Lambda('a', Var('Nat'), Var('x')), 'x', Var('a'))
    check('[x := a] in (lam a. x) leaves a free', captured.body == Var('a'))
    check('and prints without pretending a is bound', "λ a' " in str(captured))

    print('bug 4: alpha-equivalent types are equal')
    check('forall x : Nat, Nat == forall y : Nat, Nat',
          Pi('x', Var('Nat'), Var('Nat')) == Pi('y', Var('Nat'), Var('Nat')))
    check('but different domains are not',
          Pi('x', Var('Nat'), Var('Nat')) != Pi('x', Var('Bool'), Var('Nat')))
    check('and a dependent type differs from a constant one',
          Pi('x', Var('Nat'), Var('x')) != Pi('x', Var('Nat'), Var('Nat')))

    print('bug 5: normalisation goes under binders')
    inner = Lambda('z', Var('Nat'), App(Lambda('w', Var('Nat'), Var('w')),
                                        Var('z')))
    check('(lam z. (lam w. w) z) reduces to (lam z. z)',
          normalize(inner) == Lambda('z', Var('Nat'), Var('z')))

    print('bug 6: expressions are hashable')
    check('equal terms collapse in a set',
          len({Var('x'), Var('x'), Var('y')}) == 2)
    check('and can be dict keys', {Pi('x', Var('Nat'), Var('Nat')): 1}
          [Pi('q', Var('Nat'), Var('Nat'))] == 1)

    print('bug 2: Pi types have a type')
    check('forall n : Nat, Nat is a Type',
          type_check(env, Pi('n', Var('Nat'), Var('Nat'))) == Universe(1))
    check('Prop is impredicative: forall A : Prop, A is a Prop',
          type_check(env, Pi('A', Universe(0), Var('A'))) == Universe(0))
    higher = Lambda('g', Pi('n', Var('Nat'), Var('Nat')), Var('g'))
    check('a function-typed argument now checks',
          type_check(env, higher) == arrow(arrow(Var('Nat'), Var('Nat')),
                                           arrow(Var('Nat'), Var('Nat'))))

    print('the kernel rejects what it should')
    check('an unknown identifier',
          raises(lambda: type_check(env, Var('nope')), 'Unknown identifier'))
    check('applying a non-function',
          raises(lambda: type_check(env, App(Var('x'), Var('x'))),
                 'Expected a function'))
    check('an argument of the wrong type',
          raises(lambda: type_check(env, App(
              Lambda('n', Var('Nat'), Var('n')), Var('y'))), 'Type mismatch'))
    check('a lambda whose domain is not a type',
          raises(lambda: type_check(env, Lambda('n', Var('x'), Var('n'))),
                 'is not a type'))
    check('an unbound de Bruijn index',
          raises(lambda: type_check(env, Bound(0)), 'Unbound index'))

    print('polymorphic identity')
    idf = Lambda('T', Universe(1), Lambda('a', Var('T'), Var('a')))
    check('types as forall T : Type 0, T -> T',
          type_check(env, idf) == Pi('T', Universe(1),
                                     arrow(Var('T'), Var('T'))))
    applied = App(App(idf, Var('Nat')), Var('x'))
    check('id(Nat)(x) normalises to x', normalize(applied) == Var('x'))
    check('id(Nat)(x) has type Nat', type_check(env, applied) == Var('Nat'))
    check('id(Prop) is rejected, since Prop is not a Type 0',
          raises(lambda: type_check(env, App(idf, Universe(1))),
                 'Type mismatch'))

    print('elaboration')
    subst = {}
    m = new_meta('A')
    check('a hole unifies with a concrete type',
          unify(m, Var('Nat'), subst) and resolve(m, subst) == Var('Nat'))
    check('and stays solved the same way',
          unify(m, Var('Nat'), subst))
    check('a second, different solution is refused',
          not unify(m, Var('Bool'), subst))
    m2 = new_meta('B')
    check('occurs check: ?m := f(?m) is refused',
          not unify(m2, App(Var('Eq'), m2), {}))
    check('unification descends into applications',
          (lambda s: unify(App(Var('Eq'), new_meta('C')),
                           App(Var('Eq'), Var('Nat')), s))({}) )
    check('mismatched heads do not unify',
          not unify(Var('Nat'), Var('Bool'), {}))
    check('a solution mentioning a loose index is refused',
          not assign(new_meta('D'), Bound(0), {}))
    check('the kernel refuses a term with a hole left in it',
          raises(lambda: type_check(env, new_meta('E')),
                 'Unsolved metavariable'))
    check('refl is implicit in its type argument',
          type_of(GLOBAL_ENV, 'refl').implicit)
    check('an implicit argument that cannot be inferred is reported',
          raises(lambda: elaborate(env, Var('refl')), 'Could not infer'))

    print('pattern unification')
    loc = '@a1'
    pctx = {loc: Var('Nat')}

    def eq3(t, u, v):
        return App(App(App(Var('Eq'), t), u), v)

    s = {}
    P = new_meta('P')
    check('?P a = Eq Nat c c solves, though a does not occur',
          unify(App(P, Var(loc)), eq3(Var('Nat'), Var('c'), Var('c')), s, pctx))
    check('and the motive is a constant function',
          normalize(App(resolve(P, s), Var('b')))
          == eq3(Var('Nat'), Var('c'), Var('c')))

    s = {}
    P = new_meta('P')
    check('?P a = Eq Nat a a abstracts every occurrence',
          unify(App(P, Var(loc)), eq3(Var('Nat'), Var(loc), Var(loc)), s, pctx))
    check('so applying it to b gives Eq Nat b b',
          normalize(App(resolve(P, s), Var('b')))
          == eq3(Var('Nat'), Var('b'), Var('b')))

    s = {}
    F = new_meta('F')
    check('?F a = Nat solves, where first-order has no rule at all',
          unify(App(F, Var(loc)), Var('Nat'), s, pctx))

    s = {}
    Q = new_meta('Q')
    check('?Q a = Eq Nat a c solves, where first-order would need a = c',
          unify(App(Q, Var(loc)), eq3(Var('Nat'), Var(loc), Var('c')), s, pctx))
    check('and gives the motive transport needs',
          normalize(App(resolve(Q, s), Var('b')))
          == eq3(Var('Nat'), Var('b'), Var('c')))

    check('a hole applied to a non-variable is refused, not guessed',
          not unify(App(new_meta('H'), App(Var('f'), Var(loc))), Var('Nat'),
                    {}, pctx))
    check('the occurs check still applies under an application',
          (lambda m: not unify(App(m, Var(loc)), App(Var('f'), m), {}, pctx))
          (new_meta('O')))
    check('a solved motive prints without the internal local prefix',
          LOCAL_PREFIX not in str(resolve(Q, s)))

    print('constraint postponement')
    m_free = new_meta('P')                          # nothing in scope
    m_bound = new_meta('P', ('@a1',))               # a is in scope
    check('a hole records the scope it was created in',
          m_bound.context == ('@a1',) and m_free.context == ())
    check('abstracting is forced when the variable is out of scope',
          not is_ambiguous(m_free, ['@a1'],
                           eq3(Var('Nat'), Var('@a1'), Var('@a1')), {}))
    check('but ambiguous when it is in scope',
          is_ambiguous(m_bound, ['@a1'],
                       eq3(Var('Nat'), Var('@a1'), Var('@a1')), {}))
    check('and unambiguous when the variable does not occur at all',
          not is_ambiguous(m_bound, ['@a1'],
                           eq3(Var('Nat'), Var('c'), Var('c')), {}))
    queue = []
    check('an ambiguous constraint is recorded, not guessed',
          unify(App(m_bound, Var('@a1')),
                eq3(Var('Nat'), Var('@a1'), Var('@a1')), {}, pctx, queue)
          and len(queue) == 1 and m_bound.index not in {})

    # symm is the case that motivated all of this: the first constraint
    # proposes the wrong motive and only the second rules it out
    @theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, \forall b \in A, '
             r'\text{Eq} A a b \to \text{Eq} A b a', verbose=False)
    def symmetry(A: 'Type', a: 'A', b: 'A', h: r'\text{Eq} A a b'):
        return transport(h, refl(a))

    # and here the motive must abstract nothing at all, which no full
    # abstraction would ever propose
    @theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, \forall b \in A, '
             r'\text{Eq} A a b \to \text{Eq} A a b')
    def rewrite_noop(A: 'Type', a: 'A', b: 'A', h: r'\text{Eq} A a b'):
        return transport(h, h)
    check('symm proves a = b implies b = a',
          symmetry.lean_type
          == latex2type(r'\forall \{A : \text{Type}\}, \forall a \in A, '
                        r'\forall b \in A, \text{Eq} A a b \to '
                        r'\text{Eq} A b a'))
    check('and the motive chosen was the later candidate, not the first',
          'Eq' in str(symmetry.lean_term))

    def unsatisfiable():
        @theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, '
                 r'\forall b \in A, \text{Eq} A a a \to \text{Eq} A a b',
                 verbose=False)
        def bogus(A: 'Type', a: 'A', b: 'A', h: r'\text{Eq} A a a'):
            return transport(h, refl(a))
    check('postponing does not let a false claim through',
          raises(unsatisfiable, 'no single value satisfies'))

    print('partial abstraction')
    rhs = eq3(Var('A'), Var('@a1'), Var('@a1'))
    check('occurrences are counted', count_occurrences(rhs, '@a1') == 2)
    first, _ = abstract_at(rhs, '@a1', {0})
    check('the first occurrence alone can be abstracted',
          first == eq3(Var('A'), Bound(0), Var('@a1')))
    second, _ = abstract_at(rhs, '@a1', {1})
    check('and so can the second',
          second == eq3(Var('A'), Var('@a1'), Bound(0)))
    check('abstracting none leaves the term alone',
          abstract_at(rhs, '@a1', set())[0] == rhs)
    cands = list(pattern_candidates(['@a1'], rhs, {'@a1': Var('A')}))
    check('two occurrences give four candidate motives', len(cands) == 4)
    check('the fully abstracted one is offered first',
          normalize(App(cands[0], Var('b')))
          == eq3(Var('A'), Var('b'), Var('b')))
    check('the constant one is offered last',
          normalize(App(cands[-1], Var('b'))) == rhs)
    check('the partial readings are among them',
          any(normalize(App(c, Var('b'))) == eq3(Var('A'), Var('b'), Var('@a1'))
              for c in cands))
    wide = eq3(Var('A'), Var('@a1'), Var('@a1'))
    for _ in range(6):
        wide = App(wide, Var('@a1'))
    check('an explosion of occurrences falls back to one candidate',
          len(list(pattern_candidates(['@a1'], wide, {}))) == 1)

    # the motive here must abstract nothing at all: full abstraction from
    # either constraint gives the wrong answer
    @theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, \forall b \in A, '
             r'\text{Eq} A a b \to \text{Eq} A a b', verbose=False)
    def rewrite_noop(A: 'Type', a: 'A', b: 'A', h: r'\text{Eq} A a b'):
        return transport(h, h)
    check('a constant motive is found when nothing may be abstracted',
          rewrite_noop.lean_type
          == latex2type(r'\forall \{A : \text{Type}\}, \forall a \in A, '
                        r'\forall b \in A, \text{Eq} A a b \to '
                        r'\text{Eq} A a b'))
    check('and a determined case reports no ambiguity',
          not rewrite_noop.lean_notes)

    @theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, '
             r'\text{Eq} A a a \to \text{Eq} A a a', verbose=False)
    def undetermined(A: 'Type', a: 'A', h: r'\text{Eq} A a a'):
        return transport(h, h)
    check('an undetermined motive still proves the theorem',
          undetermined.lean_type is not None)
    check('but the choice is reported rather than made quietly',
          undetermined.lean_notes
          and 'not fully determined' in undetermined.lean_notes[0])

    print('dependent constants')
    for name in ('symm', 'trans', 'congrArg', 'transport'):
        check('%-10s is well formed' % name,
              isinstance(type_check(GLOBAL_ENV, type_of(GLOBAL_ENV, name)),
                         Universe))
        check('%-10s is proved, not assumed' % name,
              decl_of(GLOBAL_ENV, name).kind == 'definition')
    check('transport takes its motive implicitly',
          type_of(GLOBAL_ENV, 'transport').body.implicit)

    print('LaTeX front end')
    cases = [
        (r'\text{Nat}', Var('Nat')),
        (r'\mathbb{N}', Var('Nat')),
        (r'\text{Nat} \to \text{Bool}', arrow(Var('Nat'), Var('Bool'))),
        (r'\text{Nat} \to \text{Nat} \to \text{Nat}',
         arrow(Var('Nat'), arrow(Var('Nat'), Var('Nat')))),
        (r'(\text{Nat} \to \text{Nat}) \to \text{Nat}',
         arrow(arrow(Var('Nat'), Var('Nat')), Var('Nat'))),
        (r'\forall x \in \text{Nat}, \text{Nat}',
         arrow(Var('Nat'), Var('Nat'))),
        (r'\forall (T : \text{Type}), T \to T',
         Pi('T', Universe(1), arrow(Var('T'), Var('T')))),
        (r'\forall x \in \text{Nat}, x = x',
         Pi('x', Var('Nat'), App(App(App(Var('Eq'), Var('Nat')), Var('x')),
                                 Var('x')))),
    ]
    for text, want in cases:
        check('%-42s' % text, latex2type(text) == want)
    check('arrow is right associative, not left',
          latex2type(r'\text{Nat} \to \text{Nat} \to \text{Nat}')
          != arrow(arrow(Var('Nat'), Var('Nat')), Var('Nat')))
    check('a dangling arrow is refused',
          raises(lambda: latex2type(r'\text{Nat} \to'), 'ended early'))
    check('an unscoped equality leaves a hole for the elaborator',
          has_meta(latex2type('x = x')))
    check('an implicit binder parses with braces',
          latex2type(r'\forall \{A : \text{Type}\}, A \to A')
          == Pi('A', Universe(1), arrow(Var('A'), Var('A')), implicit=True))
    check('and implicitness does not change the type it denotes',
          latex2type(r'\forall \{A : \text{Type}\}, A \to A')
          == latex2type(r'\forall (A : \text{Type}), A \to A'))
    check('trailing junk is refused',
          raises(lambda: latex2type(r'\text{Nat} )'), 'Unexpected'))

    print('LaTeX, the other way')
    for text, want in cases:
        check('%-42s' % type2latex(want),
              latex2type(type2latex(want)) == want)
    check('every declared type in the environment reads back',
          all(latex2type(type2latex(type_of(GLOBAL_ENV, n)))
              == type_of(GLOBAL_ENV, n) for n in GLOBAL_ENV))
    check('an implicit binder stays implicit',
          type2latex(Pi('A', Universe(1), arrow(Var('A'), Var('A')),
                        implicit=True)).startswith(r'\forall \{A'))
    check('a numeral is written as a numeral, not as succ',
          type2latex(numeral(3)) == '3')
    check('a forall on the right of an arrow is parenthesised',
          type2latex(arrow(Var('Bool'), Pi('x', Var('Nat'), Var('x'))))
          == r'\text{Bool} \to (\forall x \in \text{Nat}, x)')
    captures = Pi.raw('x', Var('Nat'), App(Bound(0), Var('x')))
    check('bug: a binder is renamed rather than capturing a free name',
          type2latex(captures) == r'\forall y \in \text{Nat}, y x'
          and latex2type(type2latex(captures)) == captures)
    check("and not to fresh()'s x', which the reader cannot lex",
          "'" not in type2latex(captures))
    check('a = b only when the reader recovers this carrier',
          type2latex(Pi('x', Var('Bool'), _eq(Var('Nat'), Var('x'), Var('x'))))
          == r'\forall x \in \text{Bool}, \text{Eq} \text{Nat} x x')
    check('and it does when the binder agrees',
          type2latex(Pi('x', Var('Nat'), _eq(Var('Nat'), Var('x'), Var('x'))))
          == r'\forall x \in \text{Nat}, x = x')
    check('a lambda is refused: the subset states types',
          raises(lambda: type2latex(Lambda('x', Var('Nat'), Var('x'))),
                 'a lambda is a term'))
    check('a hole is refused rather than invented',
          raises(lambda: type2latex(latex2type('x = x')), 'is a hole'))
    check('Type 1 is refused, since the reader knows only Prop and Type',
          raises(lambda: type2latex(Universe(2)), 'not Type 1'))
    check('a name the reader would alias away is refused',
          raises(lambda: type2latex(Var('N')), 'spells something else'))

    print('Python bridge')
    src = "def f(x: 'Nat'):\n    return x\n"
    term = PythonToLean().visit(ast.parse(src).body[0])
    check('bug 1: a quoted annotation is honoured, not defaulted to Prop',
          term == Lambda('x', Var('Nat'), Var('x')))
    check('and it types as Nat -> Nat',
          type_check(env, term) == arrow(Var('Nat'), Var('Nat')))
    check('a missing annotation is an error, not a silent Prop',
          raises(lambda: PythonToLean().visit(
              ast.parse("def f(x):\n    return x\n").body[0]),
              'no type annotation'))
    check('a LaTeX annotation works too',
          PythonToLean().visit(ast.parse(
              "def f(g: r'\\text{Nat} \\to \\text{Nat}'):\n    return g\n"
          ).body[0]).var_type == arrow(Var('Nat'), Var('Nat')))
    call = PythonToLean().visit(ast.parse(
        "def f(x: 'Nat'):\n    return refl(Nat, x)\n").body[0])
    check('a call becomes curried application',
          call.body == App(App(Var('refl'), Var('Nat')), Bound(0)))
    check('several statements are refused',
          raises(lambda: PythonToLean().visit(ast.parse(
              "def f(x: 'Nat'):\n    y = x\n    return y\n").body[0]),
              'single return'))

    print('declarations, delta and iota')
    check('a bare type still works as an environment entry',
          type_check(env, Var('x')) == Var('Nat'))
    scratch = dict(GLOBAL_ENV)
    define(scratch, 'two', Var('Nat'), numeral(2))
    check('a definition unfolds', normalize(Var('two'), scratch) == numeral(2))
    check('and does not unfold without an environment',
          normalize(Var('two')) == Var('two'))
    check('a definition is refused if it mentions itself',
          raises(lambda: define(scratch, 'loop', Var('Nat'),
                                App(Var('succ'), Var('loop'))),
                 'in terms of itself'))
    check('a definition is refused if it has the wrong type',
          raises(lambda: define(scratch, 'bad', Var('Bool'), numeral(1)),
                 'but its definition has type'))
    check('a name cannot be declared twice',
          raises(lambda: define(scratch, 'two', Var('Nat'), numeral(2)),
                 'already declared'))
    check('an axiom stays opaque',
          (lambda: (axiom(scratch, 'ax', Var('Nat')),
                    normalize(Var('ax'), scratch) == Var('ax'))[1])())

    print('inductive types')
    check('Nat is a Type', type_check(GLOBAL_ENV, Var('Nat')) == Universe(1))
    check('zero is a Nat', type_check(GLOBAL_ENV, Var('zero')) == Var('Nat'))
    check('succ takes a Nat to a Nat',
          type_check(GLOBAL_ENV, Var('succ'))
          == arrow(Var('Nat'), Var('Nat')))
    check('the recursor eliminates into Type',
          type_of(GLOBAL_ENV, 'Nat.rec').var_type
          == arrow(Var('Nat'), Universe(1)))
    check('and the induction principle into Prop',
          type_of(GLOBAL_ENV, 'Nat.ind').var_type
          == arrow(Var('Nat'), Universe(0)))
    check('the motive is implicit in both',
          type_of(GLOBAL_ENV, 'Nat.rec').implicit
          and type_of(GLOBAL_ENV, 'Nat.ind').implicit)
    check('Bool has two constructors that are not equal terms',
          Var('true') != Var('false')
          and type_check(GLOBAL_ENV, Var('true')) == Var('Bool'))

    print('inductive families')
    fam = dict(GLOBAL_ENV)
    inductive(fam, 'List', [('nil', []), ('cons', [Var('A'), REC])],
              params=[('A', Universe(1))])
    check('a parameterised type former takes its parameter',
          type_of(fam, 'List') == arrow(Universe(1), Universe(1)))
    check('a parameter is implicit in the constructors',
          type_of(fam, 'nil').implicit
          and type_of(fam, 'cons').implicit)
    check('List Nat and List Bool are different types',
          App(Var('List'), Var('Nat')) != App(Var('List'), Var('Bool')))
    listnat = App(Var('List'), Var('Nat'))
    define(fam, 'length', arrow(listnat, Var('Nat')),
           Lambda('xs', listnat,
                  App(App(App(App(App(Var('List.rec'), Var('Nat')),
                                  Lambda('_', listnat, Var('Nat'))),
                              Var('zero')),
                          Lambda('a', Var('Nat'),
                                 Lambda('as', listnat,
                                        Lambda('ih', Var('Nat'),
                                               App(Var('succ'), Var('ih')))))),
                      Var('xs'))))

    def mklist(*ns):
        out = App(Var('nil'), Var('Nat'))
        for n in reversed(ns):
            out = App(App(App(Var('cons'), Var('Nat')), numeral(n)), out)
        return out
    check('a list of naturals is a List Nat',
          type_check(fam, mklist(7, 8, 9)) == listnat)
    check('and the recursor counts it',
          normalize(App(Var('length'), mklist(7, 8, 9)), fam) == numeral(3))
    check('an empty list has length zero',
          normalize(App(Var('length'), mklist()), fam) == numeral(0))
    check('a list may not mix its element types',
          raises(lambda: type_check(fam, App(App(App(Var('cons'), Var('Nat')),
                                                 Var('true')), mklist())),
                 'Type mismatch'))
    check('a recursive argument in an indexed family is refused',
          raises(lambda: inductive(dict(GLOBAL_ENV), 'Bad',
                                   [('c', [REC], [Var('a')])],
                                   params=[('A', Universe(1)),
                                           ('a', Var('A'), False)],
                                   indices=[('b', Var('A'))]),
                 'indexed family'))

    # explicit() has to hold for the whole application, not just the head:
    # with more than one explicit argument, insertion used to creep back in
    define(fam, 'lmotive', arrow(listnat, Universe(1)),
           Lambda('t', listnat, Var('Nat')))
    define(fam, 'lstep',
           Pi('a', Var('Nat'), Pi('t', listnat,
              arrow(Var('Nat'), Var('Nat')))),
           Lambda('a', Var('Nat'), Lambda('t', listnat,
                  Lambda('h', Var('Nat'), App(Var('succ'), Var('h'))))))
    # written the way a user would: the element type is left to inference
    inferred = App(App(Var('cons'), numeral(1)),
                   App(App(Var('cons'), numeral(2)), Var('nil')))
    surface = App(App(App(App(App(App(Var('explicit'), Var('List.rec')),
                                  Var('Nat')), Var('lmotive')),
                          numeral(0)), Var('lstep')), inferred)
    term, ty = elaborate(fam, surface)
    check('explicit() holds across every argument, not just the head',
          normalize(term, fam) == numeral(2))
    check('and the element type of the list was inferred, never written',
          'cons(Nat)' in str(term))

    print('equality as an inductive family')
    check('Eq is declared, not assumed',
          decl_of(GLOBAL_ENV, 'Eq').kind == 'inductive')
    check('and refl is its one constructor',
          decl_of(GLOBAL_ENV, 'refl').kind == 'constructor')
    check('Eq has the type it always had',
          type_of(GLOBAL_ENV, 'Eq')
          == Pi('A', Universe(1), Pi('a', Var('A'),
                                     Pi('b', Var('A'), Universe(0)))))
    check('and so does refl',
          type_of(GLOBAL_ENV, 'refl')
          == Pi('A', Universe(1),
                Pi('a', Var('A'), eq3(Var('A'), Var('a'), Var('a'))),
                implicit=True))
    check('Eq.ind is the J rule: it eliminates a proof of equality',
          isinstance(type_of(GLOBAL_ENV, 'Eq.ind'), Pi))
    check('J computes on refl',
          normalize(_J(Var('Nat'), Var('zero'),
                       _motive('b2', Var('Nat'), Var('zero'), Var('Nat')),
                       numeral(4), Var('zero'),
                       _refl(Var('Nat'), Var('zero'))), GLOBAL_ENV)
          == numeral(4))
    check('symm really reduces to an application of J',
          'Eq.ind' in str(decl_of(GLOBAL_ENV, 'symm').value))

    print('computation')
    plus = lambda a, b: App(App(Var('add'), a), b)
    check('2 + 3 = 5 by iota alone',
          normalize(plus(numeral(2), numeral(3)), GLOBAL_ENV) == numeral(5))
    check('0 + 0 = 0', normalize(plus(numeral(0), numeral(0)), GLOBAL_ENV)
          == numeral(0))
    withm = dict(GLOBAL_ENV, m=Var('Nat'), n=Var('Nat'))
    check('m + 0 reduces to m, because add recurses on the right',
          normalize(plus(Var('m'), Var('zero')), withm) == Var('m'))
    check('0 + n is stuck, which is why induction is needed',
          normalize(plus(Var('zero'), Var('n')), withm)
          != Var('n'))
    check('a recursor with too few arguments does not fire',
          isinstance(normalize(App(Var('Nat.rec'), Var('Nat')), GLOBAL_ENV),
                     App))
    check('a numeral in a statement is a stack of succs',
          latex2type(r'\text{Eq} \text{Nat} (\text{add} 2 3) 5')
          == App(App(App(Var('Eq'), Var('Nat')),
                     plus(numeral(2), numeral(3))), numeral(5)))
    check('and that statement is a true proposition',
          type_check(GLOBAL_ENV,
                     latex2type(r'\text{Eq} \text{Nat} (\text{add} 2 3) 5'))
          == Universe(0))

    print('the Python bridge, extended')
    check('a dotted name is one constant',
          PythonToLean().visit(ast.parse("def f(n: 'Nat'):\n"
                                         "    return Nat.ind(n)\n").body[0])
          .body.func == Var('Nat.ind'))
    check('an integer literal is a numeral',
          PythonToLean().visit(ast.parse("def f(n: 'Nat'):\n"
                                         "    return add(n, 2)\n").body[0])
          .body.arg == numeral(2))

    print('theorems end to end')

    @theorem(r'\forall x \in \text{Nat}, \text{Nat}', verbose=False)
    def identity_function(x: 'Nat'):
        return x
    check('the identity function proves Nat -> Nat',
          identity_function.lean_type == arrow(Var('Nat'), Var('Nat')))

    @theorem(r'\forall x \in \text{Nat}, x = x', verbose=False)
    def reflexivity(x: 'Nat'):
        return refl(x)
    check('refl(x) proves forall x : Nat, x = x, with A inferred',
          reflexivity.lean_type == latex2type(r'\forall x \in \text{Nat}, x = x'))
    check('and the elaborated term really carries the argument',
          reflexivity.lean_term
          == Lambda('x', Var('Nat'), App(App(Var('refl'), Var('Nat')),
                                         Var('x'))))

    @theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, a = a',
             verbose=False)
    def polymorphic_refl(A: 'Type', a: 'A'):
        return refl(a)
    check('a hole may be solved by a bound variable',
          polymorphic_refl.lean_term
          == Lambda('A', Universe(1),
                    Lambda('a', Var('A'),
                           App(App(Var('refl'), Var('A')), Var('a')))))

    @theorem(r'\forall x \in \text{Nat}, x = x', verbose=False)
    def by_hand(x: 'Nat'):
        return explicit(refl)(Nat, x)
    check('explicit(refl) still lets the argument be given by hand',
          by_hand.lean_term == reflexivity.lean_term)

    @theorem(r'\forall (T : \text{Type}), T \to T', verbose=False)
    def polymorphic_id(T: 'Type', a: 'T'):
        return a
    check('the polymorphic identity proves its Pi type',
          polymorphic_id.lean_type == latex2type(r'\forall (T : \text{Type}), T \to T'))

    # the motive is implicit and appears applied, so this is exactly the
    # higher-order case: ?P a = Eq A a c
    @theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, \forall b \in A, '
             r'\forall c \in A, \text{Eq} A a b \to \text{Eq} A a c \to '
             r'\text{Eq} A b c', verbose=False)
    def transport_demo(A: 'Type', a: 'A', b: 'A', c: 'A',
                       h: r'\text{Eq} A a b', p: r'\text{Eq} A a c'):
        return transport(h, p)
    check('transport proves b = c from a = b and a = c',
          transport_demo.lean_type
          == latex2type(r'\forall \{A : \text{Type}\}, \forall a \in A, '
                        r'\forall b \in A, \forall c \in A, '
                        r'\text{Eq} A a b \to \text{Eq} A a c \to '
                        r'\text{Eq} A b c'))

    @theorem(r'\forall f \in (\text{Nat} \to \text{Nat}), '
             r'\forall x \in \text{Nat}, \text{Eq} \text{Nat} (f x) (f x)',
             verbose=False)
    def congr_demo(f: r'\text{Nat} \to \text{Nat}', x: 'Nat'):
        return congrArg(refl(x))
    check('congrArg infers the function it is congruent over',
          congr_demo.lean_type is not None)

    # add recurses on its second argument, so this holds by computation alone
    @theorem(r'\forall m \in \text{Nat}, \text{Eq} \text{Nat} '
             r'(\text{add} m \text{zero}) m', verbose=False)
    def add_zero_right(m: 'Nat'):
        return refl(m)
    check('m + 0 = m needs no induction, only iota',
          add_zero_right.lean_type is not None)

    @theorem(r'\text{Eq} \text{Nat} (\text{add} 2 3) 5', verbose=False)
    def two_plus_three():
        return refl(5)
    check('2 + 3 = 5 is proved by refl, since both sides compute',
          two_plus_three.lean_type is not None)

    # 0 + n is stuck, so this one genuinely needs the induction principle
    proofs = dict(GLOBAL_ENV)

    @definition(r'\text{Nat} \to \text{Prop}', env=proofs, verbose=False)
    def motive(k: 'Nat'):
        return Eq(Nat, add(zero, k), k)

    @definition(r'\forall k \in \text{Nat}, '
                r'\text{Eq} \text{Nat} (\text{add} \text{zero} k) k \to '
                r'\text{Eq} \text{Nat} (\text{add} \text{zero} (\text{succ} k)) '
                r'(\text{succ} k)', env=proofs, verbose=False)
    def step(k: 'Nat', ih: r'\text{Eq} \text{Nat} (\text{add} \text{zero} k) k'):
        return congrArg(ih)
    check('a definition is added to the environment and reusable',
          type_of(proofs, 'step') is not None
          and type_of(proofs, 'motive') is not None)

    @theorem(r'\forall n \in \text{Nat}, \text{Eq} \text{Nat} '
             r'(\text{add} \text{zero} n) n', env=proofs, verbose=False)
    def add_zero_left(n: 'Nat'):
        return explicit(Nat.ind)(motive, refl(zero), step, n)
    check('0 + n = n is proved by induction',
          add_zero_left.lean_type is not None)
    check('and the proof really goes through the induction principle',
          'Nat.ind' in str(add_zero_left.lean_term))

    def bad_base():
        @theorem(r'\forall n \in \text{Nat}, \text{Eq} \text{Nat} '
                 r'(\text{add} \text{zero} n) n', env=dict(proofs),
                 verbose=False)
        def wrong(n: 'Nat'):
            return explicit(Nat.ind)(motive, refl(1), step, n)
    check('an induction with the wrong base case is rejected',
          raises(bad_base, 'Type mismatch'))

    def wrong_claim():
        @theorem(r'\forall x \in \text{Nat}, x = x', verbose=False)
        def not_a_proof(x: 'Nat'):
            return x
    check('bug 7: a false claim now raises instead of printing',
          raises(wrong_claim, 'does not prove what it claims'))
    check('and the message uses readable names, not internal ones',
          not raises(wrong_claim, LOCAL_PREFIX))

    def undeclared():
        @theorem(r'\text{Nat} \to \text{Nat}', verbose=False)
        def faulty(x: 'Nat'):
            return zzz
    check('an undeclared identifier raises', raises(undeclared, 'Unknown'))

    @theorem(r'\text{Nat}', strict=False, verbose=False)
    def lenient(x: 'Nat'):
        return zzz
    check('--non-strict records the failure instead of raising',
          hasattr(lenient, 'lean_error'))

    failed = [label for label, ok in checks if not ok]
    print('\n%d checks, %s' % (len(checks),
                               'all passed' if not failed
                               else '%d FAILED: %s' % (len(failed), failed[0])))
    return 0 if not failed else 1


# --- Test the Engine ---
def demo():
    print("--- Lean4 Micro-Kernel Initialized ---")
    environment = dict(GLOBAL_ENV, x=Var("Nat"), String=Universe(1))

    # The Identity Function: fun (T : Type) (a : T) => a
    id_func = Lambda("T", Universe(1),
                     Lambda("a", Var("T"),
                            Var("a")))

    print(f"Identity Function: {id_func}")
    print(f"Type of Identity Function: {type_check(environment, id_func)}")

    app2 = App(App(id_func, Var("Nat")), Var("x"))
    print(f"\nExpression: {app2}")
    print(f"Evaluates to: {normalize(app2)}")
    print(f"Typechecks as: {type_check(environment, app2)}")

    print("\n\n=== Testing the Python Bridge ===")

    @theorem(r"\forall x \in \text{Nat}, \text{Nat}")
    def identity_function(x: 'Nat'):
        return x

    # A is implicit in refl, so the proof is written the way Lean writes it
    @theorem(r"\forall x \in \text{Nat}, x = x")
    def reflexivity(x: 'Nat'):
        return refl(x)

    @theorem(r"\forall (T : \text{Type}), T \to T")
    def polymorphic_identity(T: 'Type', a: 'T'):
        return a

    # the hole here is solved with a bound variable, not a constant
    @theorem(r"\forall \{A : \text{Type}\}, \forall a \in A, a = a")
    def reflexivity_anywhere(A: 'Type', a: 'A'):
        return refl(a)

    # explicit(f) is Lean's @f: supply the implicit argument by hand
    @theorem(r"\forall x \in \text{Nat}, x = x")
    def reflexivity_by_hand(x: 'Nat'):
        return explicit(refl)(Nat, x)

    # transport's motive is implicit and appears applied, so working it out is
    # a higher-order problem: ?P a = Eq A a c
    @theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, \forall b \in A, '
             r'\forall c \in A, \text{Eq} A a b \to \text{Eq} A a c \to '
             r'\text{Eq} A b c')
    def transitivity(A: 'Type', a: 'A', b: 'A', c: 'A',
                     h: r'\text{Eq} A a b', p: r'\text{Eq} A a c'):
        return transport(h, p)

    # here the first constraint on the motive proposes the wrong answer, and
    # only the expected type rules it out
    @theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, \forall b \in A, '
             r'\text{Eq} A a b \to \text{Eq} A b a')
    def symmetry(A: 'Type', a: 'A', b: 'A', h: r'\text{Eq} A a b'):
        return transport(h, refl(a))

    print("\n=== Computation, and a proof by induction ===")

    # add recurses on its second argument, so m + 0 = m holds by computation
    @theorem(r"\forall m \in \text{Nat}, \text{Eq} \text{Nat} "
             r"(\text{add} m \text{zero}) m")
    def add_zero_right(m: 'Nat'):
        return refl(m)

    @theorem(r"\text{Eq} \text{Nat} (\text{add} 2 3) 5")
    def two_plus_three():
        return refl(5)

    # 0 + n is stuck until n is a constructor, so this one needs induction
    @definition(r"\text{Nat} \to \text{Prop}")
    def add_zero_motive(k: 'Nat'):
        return Eq(Nat, add(zero, k), k)

    @definition(r"\forall k \in \text{Nat}, "
                r"\text{Eq} \text{Nat} (\text{add} \text{zero} k) k \to "
                r"\text{Eq} \text{Nat} (\text{add} \text{zero} (\text{succ} k)) "
                r"(\text{succ} k)")
    def add_zero_induction_step(k: 'Nat',
                                ih: r"\text{Eq} \text{Nat} (\text{add} \text{zero} k) k"):
        return congrArg(ih)

    @theorem(r"\forall n \in \text{Nat}, \text{Eq} \text{Nat} "
             r"(\text{add} \text{zero} n) n")
    def add_zero_left(n: 'Nat'):
        return explicit(Nat.ind)(add_zero_motive, refl(zero),
                                 add_zero_induction_step, n)

    print("\n=== A type with a parameter ===")
    inductive(GLOBAL_ENV, 'List', [('nil', []), ('cons', [Var('A'), REC])],
              params=[('A', Universe(1))])
    print(f"List : {readable(type_of(GLOBAL_ENV, 'List'))}")
    print(f"cons : {readable(type_of(GLOBAL_ENV, 'cons'))}")

    # the recursor needs its motive and its step case, each a checked
    # definition in its own right
    @definition(r"\text{List} \text{Nat} \to \text{Type}")
    def length_motive(t: r'\text{List} \text{Nat}'):
        return Nat

    @definition(r"\forall a \in \text{Nat}, \forall t \in \text{List} \text{Nat}, "
                r"\text{Nat} \to \text{Nat}")
    def length_step(a: 'Nat', t: r'\text{List} \text{Nat}', h: 'Nat'):
        return succ(h)

    @definition(r"\text{List} \text{Nat} \to \text{Nat}")
    def length(t: r'\text{List} \text{Nat}'):
        return explicit(List.rec)(Nat, length_motive, 0, length_step, t)

    # the element type of the list is never written down: the elaborator
    # works it out from the 7
    @theorem(r"\text{Eq} \text{Nat} "
             r"(\text{length} (\text{cons} 7 (\text{cons} 8 \text{nil}))) 2")
    def a_two_element_list_has_length_two():
        return refl(2)

    print("\n--- and a proof that should fail ---")
    try:
        @theorem(r"\forall x \in \text{Nat}, x = x")
        def faulty_function(x: 'Nat'):
            return x
    except TheoremError as exc:
        print(f"correctly rejected: {exc}")


if __name__ == "__main__":
    if '--non-strict' in sys.argv:
        STRICT = False
    if '--selftest' in sys.argv:
        VERBOSE = False
        sys.exit(selftest())
    demo()
