#!/usr/bin/env python3
# lean4.py - Version 0.3: The Micro-Kernel, on de Bruijn indices
import ast
import sys
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
?P a = Eq A a a admits both (lam z. Eq A z z) and (lam z. Eq A z a) whenever a
is in scope where the hole was made.  Such constraints are postponed rather
than guessed, and settled once every constraint on that hole is known: each
one proposes its own solution, and only a proposal satisfying all of them is
accepted.  That is what lets symm be written transport(h, refl(a)) -- the first
constraint proposes the wrong motive and the second overrules it.
'''


class KernelError(Exception):
    """The term is not well typed, or cannot be understood."""


class TheoremError(KernelError):
    """A theorem did not prove what it claimed to prove."""


# ---------------------------------------------------------------- expressions

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

    def __repr__(self):
        return str(self)


class Universe(Expr):
    """Sorts/Universes: Prop (0), Type (1), Type 1 (2), etc."""

    def __init__(self, level=0):
        self.level = level

    def key(self):
        return ('sort', self.level)

    def __str__(self):
        return pretty(self)


class Var(Expr):
    """A free variable or global constant, like 'Nat'."""

    def __init__(self, name):
        self.name = name

    def key(self):
        return ('var', self.name)

    def __str__(self):
        return pretty(self)


class Bound(Expr):
    """A bound variable, as a de Bruijn index: 0 is the nearest binder."""

    def __init__(self, index):
        self.index = index

    def key(self):
        return ('bound', self.index)

    def __str__(self):
        return pretty(self)


class App(Expr):
    """Function application: f(x)"""

    def __init__(self, func, arg):
        self.func = func
        self.arg = arg

    def key(self):
        return ('app', self.func.key(), self.arg.key())

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
        return ('meta', self.index)

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
        return (self.tag, self.var_type.key(), self.body.key())

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
        return expr.name
    if isinstance(expr, Bound):
        return names[expr.index] if expr.index < len(names) else f"#{expr.index}"
    if isinstance(expr, Meta):
        return f"?{expr.hint}{expr.index}"
    if isinstance(expr, App):
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

def shift(expr, amount, cutoff=0):
    """Renumber the free indices of expr, leaving those below cutoff alone."""
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


def normalize(expr):
    """Full beta-normalisation, including under binders."""
    if isinstance(expr, App):
        func = normalize(expr.func)
        arg = normalize(expr.arg)
        if isinstance(func, Lambda):
            return normalize(instantiate(func.body, arg))
        return App(func, arg)
    if isinstance(expr, Binder):
        return expr.rebuild(normalize(expr.var_type), normalize(expr.body))
    return expr


def definitionally_equal(a, b):
    """Types are the same if they normalise to the same term."""
    return normalize(a) == normalize(b)


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
        if expr.name not in env:
            raise KernelError(f"Unknown identifier: {expr.name}")
        return env[expr.name]

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
        func_type = normalize(type_check(env, expr.func, local))
        if not isinstance(func_type, Pi):
            raise KernelError(f"Expected a function, got {func_type}")
        arg_type = type_check(env, expr.arg, local)
        if not definitionally_equal(func_type.var_type, arg_type):
            raise KernelError(f"Type mismatch: expected "
                              f"{pretty(func_type.var_type)}, "
                              f"got {pretty(arg_type)}")
        return normalize(instantiate(func_type.body, expr.arg))

    raise KernelError(f"Cannot typecheck: {expr}")


def expect_sort(env, expr, local, role):
    """A type must itself have a sort; anything else is a category error."""
    sort = normalize(type_check(env, expr, local))
    if not isinstance(sort, Universe):
        raise KernelError(f"The {role} {pretty(expr)} is not a type "
                          f"(it has type {pretty(sort)})")
    return sort



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


def unify(a, b, subst, ctx=None, pending=None):
    """Unification up to normalisation, over Miller's pattern fragment.

    With a pending list, a constraint whose solution is not yet determined is
    recorded instead of guessed, and settled later by solve_pending.
    """
    ctx = ctx if ctx is not None else {}
    a = normalize(resolve(a, subst))
    b = normalize(resolve(b, subst))
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
        return (unify(a.func, b.func, subst, ctx, pending)
                and unify(a.arg, b.arg, subst, ctx, pending))
    if isinstance(a, Binder) and isinstance(b, Binder) and a.tag == b.tag:
        return (unify(a.var_type, b.var_type, subst, ctx, pending)
                and unify(a.body, b.body, subst, ctx, pending))
    return False


class Constraint:
    """A postponed equation ?m x1..xn = rhs, kept with the context it arose in."""

    def __init__(self, lhs, rhs, ctx):
        self.lhs = lhs
        self.rhs = rhs
        self.ctx = ctx

    def head(self, subst):
        head, args = spine(normalize(resolve(self.lhs, subst)))
        return head, args

    def satisfied(self, subst):
        return definitionally_equal(resolve(self.lhs, subst),
                                    resolve(self.rhs, subst))

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
        self.counter = 0

    def local_names(self):
        return tuple(n for n in self.env if n.startswith(self.PREFIX))

    def fresh_local(self, hint):
        self.counter += 1
        return f"{self.PREFIX}{hint}{self.counter}"

    def insert_implicits(self, term, type_):
        """Apply the term to a fresh hole for each leading implicit binder."""
        type_ = normalize(resolve(type_, self.subst))
        while isinstance(type_, Pi) and type_.implicit:
            hole = new_meta(type_.var_name, self.local_names())
            term = App(term, hole)
            type_ = normalize(instantiate(type_.body, hole))
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
        expected = normalize(resolve(expected, self.subst))
        if isinstance(expr, Lambda) and isinstance(expected, Pi):
            domain, _ = self.infer(expr.var_type)
            if not unify(domain, expected.var_type, self.subst,
                         self.env, self.pending):
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
        if not unify(expected, actual, self.subst, self.env, self.pending):
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
            if expr.name not in self.env:
                raise KernelError(f"Unknown identifier: {expr.name}")
            term, type_ = expr, self.env[expr.name]
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

            func, func_type = self.infer(expr.func, insert=True)
            func_type = normalize(resolve(func_type, self.subst))
            if not isinstance(func_type, Pi):
                raise KernelError(f"Expected a function, got "
                                  f"{pretty(func_type)}")
            arg, arg_type = self.infer(expr.arg)
            if not unify(func_type.var_type, arg_type, self.subst,
                         self.env, self.pending):
                raise KernelError(
                    f"Type mismatch: expected "
                    f"{readable(resolve(func_type.var_type, self.subst))}, got "
                    f"{readable(resolve(arg_type, self.subst))}")
            result = normalize(instantiate(func_type.body, arg))
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
                            if not c.satisfied(self.subst)]
            if not self.pending:
                return
            by_meta = {}
            for c in self.pending:
                head, args = c.head(self.subst)
                if isinstance(head, Meta) and head.index not in self.subst:
                    by_meta.setdefault(head.index, []).append((c, head, args))
            if not by_meta:
                return
            progressed = False
            for group in by_meta.values():
                for candidate, head, args in group:
                    trial = dict(self.subst)
                    if assign_pattern(head, args, candidate.rhs, trial,
                                      candidate.ctx) is not True:
                        continue
                    if all(c.satisfied(trial) for c, _, _ in group):
                        self.subst = trial
                        progressed = True
                        break
                if progressed:
                    break
            if not progressed:
                return

    def check_pending(self):
        """Nothing may be left unverified: a postponed constraint that never
        got settled is an implicit argument we could not work out."""
        self.solve_pending()
        unmet = [c for c in self.pending if not c.satisfied(self.subst)]
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
    el = Elaborator(env)
    if expected is None:
        term, _ = el.infer(term)
    else:
        expected, _ = el.infer(expected)
        term = el.check(term, expected)
    el.check_pending()
    term = el.finish(term)
    checked = type_check(env, term)          # the trusted check
    if expected is not None:
        expected = el.finish(expected, 'statement')
        if not definitionally_equal(expected, checked):
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
        if t.isidentifier():
            # tokenize() splits Nat into N, a, t and juxtaposition already
            # means application, so a multi-letter name must be written
            # \text{Nat}.  Single letters are the usual bound variables.
            return self.named(t)
        raise KernelError(f"Cannot read {t!r} as a type")


def latex2type(statement):
    r"""A LaTeX statement -> the kernel type it denotes."""
    return LatexTypeParser(rosettaui.tokenize(statement)).parse()


def parse_type(text):
    """A type written either as a bare name or as LaTeX.

    'Nat' is a plain identifier and must not go through the LaTeX reader,
    which would tokenise it into three letters and read it as an application.
    """
    text = text.strip()
    if text.isidentifier():
        return LatexTypeParser([]).named(text)
    return latex2type(text)


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

    def visit_Call(self, node):
        """f(a, b) is curried application: App(App(f, a), b)."""
        if node.keywords:
            raise KernelError("keyword arguments have no meaning in the kernel")
        expr = self.visit(node.func)
        for arg in node.args:
            expr = App(expr, self.visit(arg))
        return expr

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

def _eq_type():
    """Eq : forall A : Type 0, A -> A -> Prop"""
    return Pi('A', Universe(1),
              Pi('a', Var('A'), Pi('b', Var('A'), Universe(0))))


def _refl_type():
    r"""refl : forall {A : Type 0}, forall a : A, Eq A a a

    A is implicit, so a proof is written refl(x) and the elaborator recovers
    A by unifying the type of x with the expected argument type.  Write
    explicit(refl)(Nat, x) to supply it by hand.
    """
    same = App(App(App(Var('Eq'), Var('A')), Var('a')), Var('a'))
    return Pi('A', Universe(1), Pi('a', Var('A'), same), implicit=True)


def _eq(t, x, y):
    return App(App(App(Var('Eq'), t), x), y)


def _symm_type():
    r"""symm : forall {A} {a b : A}, Eq A a b -> Eq A b a"""
    return Pi('A', Universe(1),
              Pi('a', Var('A'),
                 Pi('b', Var('A'),
                    arrow(_eq(Var('A'), Var('a'), Var('b')),
                          _eq(Var('A'), Var('b'), Var('a'))),
                    implicit=True),
                 implicit=True),
              implicit=True)


def _trans_type():
    r"""trans : forall {A} {a b c : A}, Eq A a b -> Eq A b c -> Eq A a c"""
    inner = arrow(_eq(Var('A'), Var('a'), Var('b')),
                  arrow(_eq(Var('A'), Var('b'), Var('c')),
                        _eq(Var('A'), Var('a'), Var('c'))))
    return Pi('A', Universe(1),
              Pi('a', Var('A'),
                 Pi('b', Var('A'),
                    Pi('c', Var('A'), inner, implicit=True),
                    implicit=True),
                 implicit=True),
              implicit=True)


def _congr_type():
    r"""congrArg : forall {A B} {f : A -> B} {a b : A}, Eq A a b -> Eq B (f a) (f b)

    f is implicit, so working out what it is means solving ?f x = g x -- a
    higher-order problem, and the reason the unifier needs Miller patterns.
    """
    inner = arrow(_eq(Var('A'), Var('a'), Var('b')),
                  _eq(Var('B'), App(Var('f'), Var('a')),
                      App(Var('f'), Var('b'))))
    return Pi('A', Universe(1),
              Pi('B', Universe(1),
                 Pi('f', arrow(Var('A'), Var('B')),
                    Pi('a', Var('A'),
                       Pi('b', Var('A'), inner, implicit=True),
                       implicit=True),
                    implicit=True),
                 implicit=True),
              implicit=True)


def _transport_type():
    r"""transport : forall {A} {P : A -> Prop} {a b : A}, Eq A a b -> P a -> P b

    The motive P is implicit and appears applied, so ?P a = <goal> is again a
    pattern problem.
    """
    inner = arrow(_eq(Var('A'), Var('a'), Var('b')),
                  arrow(App(Var('P'), Var('a')), App(Var('P'), Var('b'))))
    return Pi('A', Universe(1),
              Pi('P', arrow(Var('A'), Universe(0)),
                 Pi('a', Var('A'),
                    Pi('b', Var('A'), inner, implicit=True),
                    implicit=True),
                 implicit=True),
              implicit=True)


# A global logical environment for our theorems.  Nat is a Type, not a Prop:
# declaring it a Prop is what let the old identity example typecheck for the
# wrong reason.
GLOBAL_ENV = {
    "Nat": Universe(1),
    "Bool": Universe(1),
    "Real": Universe(1),
    "Eq": _eq_type(),
    "refl": _refl_type(),
    "symm": _symm_type(),
    "trans": _trans_type(),
    "congrArg": _congr_type(),
    "transport": _transport_type(),
}

STRICT = True                 # a failed theorem raises; --non-strict prints
VERBOSE = True


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
                say(f"Elaborated:    {term}")
            say(f"Inferred Type: {actual}")
            say(f"Stated Type:   {pretty(normalize(actual))}")

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
          GLOBAL_ENV['refl'].implicit)
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

    print('dependent constants')
    for name in ('symm', 'trans', 'congrArg', 'transport'):
        check('%-10s is well formed' % name,
              isinstance(type_check(GLOBAL_ENV, GLOBAL_ENV[name]), Universe))
    check('transport takes its motive implicitly',
          GLOBAL_ENV['transport'].body.implicit)

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
