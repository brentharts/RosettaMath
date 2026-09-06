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


class Binder(Expr):
    """Shared machinery for Pi and Lambda.

    The constructor takes a *named* body and abstracts the name away, so
    callers write ordinary readable terms and the kernel still gets de Bruijn
    indices.  Inner binders are built first, so a shadowed name has already
    been abstracted by the time the outer binder looks at it.
    """

    def __init__(self, var_name, var_type, body, raw=False):
        self.var_name = var_name
        self.var_type = var_type
        self.body = body if raw else abstract(body, var_name)

    @classmethod
    def raw(cls, var_name, var_type, body):
        """Build directly from a body that already uses de Bruijn indices."""
        return cls(var_name, var_type, body, raw=True)

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
    if isinstance(expr, App):
        return f"{pretty(expr.func, names)}({pretty(expr.arg, names)})"
    if isinstance(expr, Pi):
        dom = pretty(expr.var_type, names)
        if not occurs(expr.body, 0):
            # non-dependent: print the arrow, which is what a reader expects
            return f"({dom} → {pretty(expr.body, ['_'] + names)})"
        n = fresh(expr.var_name, names, free_names(expr.body))
        return f"(∀ {n} : {dom}, {pretty(expr.body, [n] + names)})"
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
        return type(expr).raw(expr.var_name,
                              shift(expr.var_type, amount, cutoff),
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
        return type(expr).raw(expr.var_name,
                              abstract(expr.var_type, name, depth),
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
        return type(expr).raw(expr.var_name,
                              instantiate(expr.var_type, value, depth),
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
        return type(expr).raw(expr.var_name,
                              substitute(expr.var_type, var_name, replacement),
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
        return type(expr).raw(expr.var_name,
                              normalize(expr.var_type),
                              normalize(expr.body))
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
        return Pi.raw(expr.var_name, expr.var_type, body_type)

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
        parens = self.peek() == '('
        if parens:
            self.next()
        name = self.next()
        if name is None or not name.isidentifier():
            raise KernelError(f"Expected a bound variable name, found {name!r}")
        self.expect(*COLON)
        domain = self.arrow_type()
        if parens:
            self.expect(')')
        self.expect(',')
        outer = self.scope.get(name)
        self.scope[name] = domain             # so 'x = x' knows the type of x
        body = self.expression()
        if outer is None:
            self.scope.pop(name, None)
        else:
            self.scope[name] = outer
        return Pi(name, domain, body)

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
            raise KernelError(
                "Cannot tell which type this equality is over; bind the "
                "variable first, as in \\forall x \\in \\text{Nat}, x = x")
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
            if t is None or t in ARROW or t in COLON or t in (',', ')', '}', '='):
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
    if source.lstrip().startswith('@'):
        # drop the decorator lines, which are not part of the term
        lines = source.splitlines()
        while lines and lines[0].lstrip().startswith('@'):
            lines.pop(0)
        source = '\n'.join(lines)
    tree = ast.parse(source)
    return PythonToLean().visit(tree.body[0])


# --------------------------------------------------------- global environment

def _eq_type():
    """Eq : forall A : Type 0, A -> A -> Prop"""
    return Pi('A', Universe(1),
              Pi('a', Var('A'), Pi('b', Var('A'), Universe(0))))


def _refl_type():
    """refl : forall A : Type 0, forall a : A, Eq A a a"""
    same = App(App(App(Var('Eq'), Var('A')), Var('a')), Var('a'))
    return Pi('A', Universe(1), Pi('a', Var('A'), same))


# A global logical environment for our theorems.  Nat is a Type, not a Prop:
# declaring it a Prop is what let the old identity example typecheck for the
# wrong reason.
GLOBAL_ENV = {
    "Nat": Universe(1),
    "Bool": Universe(1),
    "Real": Universe(1),
    "Eq": _eq_type(),
    "refl": _refl_type(),
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
            term = compile_python_to_lean(func)
            say(f"Compiled Kernel Expr: {term}")
            actual = type_check(scope, term)
            say(f"Inferred Type: {actual}")

            expected = latex2type(latex_statement)
            say(f"Stated Type:   {expected}")
            expect_sort(scope, expected, [], "statement")
            if not definitionally_equal(expected, actual):
                raise TheoremError(
                    f"{func.__name__} does not prove what it claims: stated "
                    f"{pretty(expected)}, proved {pretty(actual)}")

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
    check('an unscoped equality is refused',
          raises(lambda: latex2type('x = x'), 'which type'))
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
        return refl(Nat, x)
    check('refl proves forall x : Nat, x = x',
          reflexivity.lean_type == latex2type(r'\forall x \in \text{Nat}, x = x'))

    @theorem(r'\forall (T : \text{Type}), T \to T', verbose=False)
    def polymorphic_id(T: 'Type', a: 'T'):
        return a
    check('the polymorphic identity proves its Pi type',
          polymorphic_id.lean_type == latex2type(r'\forall (T : \text{Type}), T \to T'))

    def wrong_claim():
        @theorem(r'\forall x \in \text{Nat}, x = x', verbose=False)
        def not_a_proof(x: 'Nat'):
            return x
    check('bug 7: a false claim now raises instead of printing',
          raises(wrong_claim, 'does not prove what it claims'))

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

    @theorem(r"\forall x \in \text{Nat}, x = x")
    def reflexivity(x: 'Nat'):
        return refl(Nat, x)

    @theorem(r"\forall (T : \text{Type}), T \to T")
    def polymorphic_identity(T: 'Type', a: 'T'):
        return a

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
