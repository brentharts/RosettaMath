#!/usr/bin/env python3
r"""rosettalean.py -- physics equations, read into the lean4.py kernel.

lean4.py already reads LaTeX, but the subset it reads is the language of types:
\forall, \lambda, \to, application, equality.  Physics is written in a different
subset -- fractions, powers, square roots, products by juxtaposition -- and
`latex2type` stops at the first `^`.  This module supplies the missing half.

The route is:

    rosettaphys.Derivation          two equations joined on a shared quantity
      -> .latex()                   one statement, braces recording provenance
      -> rosettaui.parse_latex      a shape tree
      -> term()                     a kernel term over Real
      -> conjecture()               a closed Prop, every quantity quantified
      -> lean4.type_check           the micro-kernel agrees it is a Prop
      -> leanexport                 Lean 4 source, for a second opinion

What is and is not claimed here matters, so it is worth being plain about it.

The kernel is told that Real is a type and that add, mul, div, pow and the rest
are operations on it.  It is *not* told the field axioms, so it cannot prove
m c^2 = h \nu, and nothing here pretends otherwise.  What the kernel checks is
that the statement is well formed: that every symbol is bound, that the two
sides of the equality live in the same type, and that the thing produced is a
Prop.  That is the honest claim -- the conjecture is sayable and well typed --
and it is exactly the claim a `conjecture` should make, since a conjecture that
could be proved from the notation alone would not be one.

The underbrace annotations survive the trip.  A braced subterm becomes the term
inside it, with the label recorded, so the generated Lean carries the name of
the equation each side came from as a comment.  Provenance that vanishes at the
first translation step is provenance nobody can check.

    python3 rosettalean.py             show what the library can conjecture
    python3 rosettalean.py --selftest  check the bridge end to end
    python3 rosettalean.py --lean      print Lean 4 source for each conjecture
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import lean4 as L
from lean4 import App, Lambda, Pi, Var, arrow, Universe
import rosettaphys as P
import rosettaui as U


# ------------------------------------------------------- the physics theory
#
# A signature, not a theory: the operations exist and have types, and that is
# all.  Declaring them as axioms rather than defining them is the whole reason
# the kernel's verdict on a conjecture is informative -- if mul computed, the
# kernel could decide arithmetic identities by normalising, and "well typed"
# would quietly start meaning something else.

REAL = Var('Real')
NAT = Var('Nat')

# Namespaced, because the kernel already has an `add` and it is Nat's.  Two
# different additions under one name is exactly the overloading the project
# exists to complain about, so Real's operations say whose they are.
BINARY = ('Real.add', 'Real.sub', 'Real.mul', 'Real.div')
UNARY = ('Real.neg', 'Real.sqrt', 'Real.log', 'Real.exp',
         'Real.sin', 'Real.cos', 'Real.tan', 'Real.abs')


def physics_env():
    """A fresh environment: the kernel's globals, plus arithmetic on Real."""
    env = dict(L.GLOBAL_ENV)
    for name in BINARY:
        L.axiom(env, name, arrow(REAL, arrow(REAL, REAL)))
    for name in UNARY:
        L.axiom(env, name, arrow(REAL, REAL))
    # a power with a whole-number exponent is the only kind the equations use,
    # and keeping the exponent a Nat is what stops c^2 and c^x being the same
    # shape -- the first is arithmetic, the second would need a real exponent
    L.axiom(env, 'Real.pow', arrow(REAL, arrow(NAT, REAL)))
    L.axiom(env, 'Real.rpow', arrow(REAL, arrow(REAL, REAL)))
    # a literal, so 2 and 4 can appear in a formula without being Nats
    L.axiom(env, 'Real.lit', arrow(NAT, REAL))
    # the relations physics states that are not equalities
    for name in ('Real.le', 'Real.lt', 'Real.ge', 'Real.gt'):
        L.axiom(env, name, arrow(REAL, arrow(REAL, Universe(0))))
    # conjunction, so that a page of equations can be one proposition.  An
    # axiom rather than an inductive on purpose: nothing here proves anything,
    # and a declared And is enough to *state* the claim, which is all a
    # conjecture does.
    L.axiom(env, 'And', arrow(Universe(0), arrow(Universe(0), Universe(0))))
    return env


# Names that stand for a fixed number rather than a free quantity.  Taken from
# rosettaphys.CONSTANTS, which is the same list that stops eq2py treating c as
# a function argument -- so the two translations agree on what a constant is
# instead of each having an opinion.
CONSTANT_NAMES = tuple(sorted(P.CONSTANTS))


def declare_constants(env):
    """Give every known physical constant a name of type Real.

    A constant that gets universally quantified instead is a real mistake, not
    a cosmetic one: `forall pi : Real, ...` is a strictly stronger claim than
    the equation, and one that is false for almost every pi.  Declaring them
    keeps the conjecture saying what the physics says.
    """
    for name in CONSTANT_NAMES:
        if name not in env:
            L.axiom(env, name, REAL)
    return env


PHYS_ENV = declare_constants(physics_env())


def _bin(op, left, right):
    return App(App(Var(op), left), right)


def _un(op, arg):
    return App(Var(op), arg)


# ---------------------------------------------------------------- names
#
# A LaTeX symbol has to become a Lean identifier, and the mapping must be
# injective or two different quantities silently become one.  \hbar and h are
# the case that matters: both are Planck's constant, they differ by 2*pi, and
# collapsing them would turn a false statement into a true one.

GREEK_NAMES = {
    'α': 'alpha', 'β': 'beta', 'γ': 'gamma', 'δ': 'delta', 'ε': 'varepsilon',
    'ϵ': 'epsilon', 'ζ': 'zeta', 'η': 'eta', 'θ': 'theta', 'ι': 'iota',
    'κ': 'kappa', 'λ': 'lambda', 'μ': 'mu', 'ν': 'nu', 'ξ': 'xi', 'π': 'pi',
    'ρ': 'rho', 'σ': 'sigma', 'τ': 'tau', 'υ': 'upsilon', 'φ': 'varphi',
    'ϕ': 'phi', 'χ': 'chi', 'ψ': 'psi', 'ω': 'omega',
    'Γ': 'Gamma', 'Δ': 'Delta', 'Θ': 'Theta', 'Λ': 'Lambda', 'Ξ': 'Xi',
    'Π': 'Pi', 'Σ': 'Sigma', 'Υ': 'Upsilon', 'Φ': 'Phi', 'Ψ': 'Psi',
    'Ω': 'Omega', 'ℏ': 'hbar', '∇': 'nabla', '∂': 'partial',
}

# Names Lean 4 will not accept as a local, or would read as something else.
RESERVED = {'fun', 'let', 'in', 'do', 'if', 'then', 'else', 'match', 'with',
            'have', 'show', 'from', 'by', 'at', 'end', 'this', 'Type', 'Prop',
            'Sort', 'exp', 'log', 'abs', 'max', 'min'}


def identifier(text):
    """A LaTeX glyph as a Lean-safe identifier.

    Greek is translated letter by letter rather than by looking the whole
    string up, because a subscript has usually been folded in by now and
    epsilon_0 must not come out as the glyph with an _0 stuck on the end --
    Python thinks a Greek letter is alphanumeric, so it would otherwise sail
    straight through the sanitiser and into the generated Lean.
    """
    name = GREEK_NAMES.get(text)
    if name is None:
        name = ''.join(GREEK_NAMES.get(ch, ch) for ch in text)
    out = []
    for ch in name:
        if ch.isascii() and (ch.isalnum() or ch == '_'):
            out.append(ch)
        elif ch in '\u2032\u2033':                  # primes
            out.append('p')
        else:
            out.append('_')
    name = ''.join(out).strip('_') or 'q'
    if name[0].isdigit():
        name = 'q' + name
    if name in RESERVED:
        name += '_'
    return name


# ------------------------------------------------------------ term reader
#
# rosettaphys already read the LaTeX into its algebra, so there is nothing left
# to parse here: this walks a Term and says what each node means to the kernel.
#
# That is a real simplification over what this file used to do, which was walk
# rosettaui's *shape* tree.  A shape tree records that \underbrace{x}_{label}
# is a thing with a subscript, and the reader had to know that this particular
# subscript was a caption rather than an index -- a distinction the algebra
# already makes, in one place, for every reader.

class Unreadable(Exception):
    """This corner of the notation has no reading as a kernel term.

    Every message names what was met, because the point of the message is to
    say which equation needs a case adding.
    """


BINOPS = {'add': 'Real.add', 'sub': 'Real.sub',
          'mul': 'Real.mul', 'div': 'Real.div'}

CALLS = {'log': 'Real.log', 'ln': 'Real.log', 'exp': 'Real.exp',
         'sqrt': 'Real.sqrt', 'sin': 'Real.sin', 'cos': 'Real.cos',
         'tan': 'Real.tan', 'abs': 'Real.abs'}


class TermReader:
    """A rosettaphys Term -> a kernel term over Real."""

    def __init__(self):
        self.free = {}            # identifier -> the Var standing for it
        self.labels = []          # provenance recovered from the braces
        self.spellings = {}       # identifier -> the LaTeX it came from

    # -- entry points ----------------------------------------------------

    def read(self, latex):
        """A LaTeX fragment as a kernel term."""
        return self.term(P.read_term(latex))

    def relation(self, latex):
        """A LaTeX statement as (left, relation, right) kernel terms."""
        rel = P.read_relation(latex)
        self.labels.extend(l for l in rel.labels if l)
        return self.term(rel.left), rel.op, self.term(rel.right)

    # -- the algebra -----------------------------------------------------

    def term(self, t):
        if isinstance(t, P.Sym):
            return self.symbol(t)
        if isinstance(t, P.Num):
            return self.number(t)
        if isinstance(t, P.Call):
            return self.call(t)
        if isinstance(t, P.Op):
            return self.op(t)
        if isinstance(t, P.Opaque):
            raise Unreadable('%s has no algebraic reading, so it has no '
                             'reading as a term either' % t.tex)
        raise Unreadable('no reading for %r' % (t,))

    def symbol(self, t):
        """A quantity as a free variable, remembered so it can be quantified."""
        name = identifier(t.name)
        if name not in self.free:
            self.free[name] = Var(name)
            self.spellings[name] = t.tex
        return self.free[name]

    def number(self, t):
        """A literal.  Whole numbers only: Real.lit takes a Nat."""
        try:
            value = int(t.text)
        except ValueError:
            raise Unreadable('the non-integer literal %s -- Real.lit takes a '
                             'Nat, and a decimal would need a rational'
                             % t.text)
        if value < 0:
            raise Unreadable('a negative literal')
        return _un('Real.lit', L.numeral(value))

    def call(self, t):
        name = CALLS.get(t.func)
        if name is None:
            raise Unreadable('no reading for the function %s' % t.func)
        return _un(name, self.term(t.arg))

    def op(self, t):
        if t.op == 'neg':
            return _un('Real.neg', self.term(t.args[0]))
        if t.op == 'pow':
            return self.power(t)
        name = BINOPS.get(t.op)
        if name is None:
            raise Unreadable('no reading for the operator %s' % t.op)
        return _bin(name, self.term(t.args[0]), self.term(t.args[1]))

    def power(self, t):
        r"""x^n with a whole n is Real.pow; anything else is Real.rpow.

        Keeping the two apart is not pedantry.  c^2 has a Nat exponent and
        means c times c; a^b with b real is a different operation that needs
        a positive base to be defined at all, and giving them one name would
        lose the side condition at the point where it still fits in a type.
        """
        base, exponent = t.args
        if isinstance(exponent, P.Num):
            try:
                whole = int(exponent.text)
            except ValueError:
                whole = None
            if whole is not None and whole >= 0:
                return _bin('Real.pow', self.term(base), L.numeral(whole))
        return _bin('Real.rpow', self.term(base), self.term(exponent))


# ------------------------------------------------------------ conjectures

RELATION_OPS = {'=': None, r'\leq': 'Real.le', r'\geq': 'Real.ge',
                r'\neq': None, r'\approx': None, r'\equiv': None,
                r'\propto': None, r'\simeq': None, r'\sim': None}


class Conjecture:
    """A statement from the knowledge base, as a closed kernel Prop."""

    def __init__(self, name, statement, reader, source='', notes=()):
        self.name = name
        self.statement = statement            # the kernel Pi type
        self.reader = reader
        self.source = source                  # the LaTeX it came from
        self.notes = list(notes)

    @property
    def variables(self):
        """The quantities the statement quantifies over."""
        return [n for n in sorted(self.reader.free)
                if n not in CONSTANT_NAMES]

    @property
    def constants(self):
        """The named constants it refers to, which are declared, not bound."""
        return [n for n in sorted(self.reader.free) if n in CONSTANT_NAMES]

    def check(self, env=None):
        """Ask the micro-kernel whether this is a well formed proposition."""
        env = env or PHYS_ENV
        sort = L.type_check(env, self.statement)
        return L.readable(sort)

    def latex(self):
        """Back to LaTeX, through the kernel's own printer."""
        return L.type2latex(self.statement)

    def lean(self, env=None):
        """Lean 4 source for this conjecture, as an `axiom` to be discharged."""
        return lean_source(self, env)

    def __repr__(self):
        return '<Conjecture %s : %s>' % (self.name, L.readable(self.statement))


def conjecture(derivation, name=None):
    """A Derivation as a closed proposition over Real.

    Every quantity mentioned anywhere in the statement is universally
    quantified, so the result stands on its own: there are no free names left
    for the reader to supply from context, which is the single biggest
    difference between an equation on a blackboard and one a kernel will look
    at.
    """
    reader = TermReader()
    source = derivation.latex()
    left, rel, right = reader.relation(source)
    body = _relate(rel, left, right)
    statement = _close(body, reader)
    label = name or _label(derivation)
    notes = ['%s : %s' % (step.equation.label, step.expr)
             for step in derivation.steps]
    notes.append('joined on %s' % P.pivot_tex(derivation.pivot))
    return Conjecture(label, statement, reader, source, notes)



def grand_conjecture(pivots=None, name='physics'):
    """Every family in the display, as one proposition.

    The rows of the display are conjoined and the quantities shared between
    them are bound once, over the whole thing.  That last part is what makes
    this more than a list: the m in mass-energy and the m in Newton's second
    law become the same bound variable, so the conjunction says the equations
    agree about it rather than each using a letter privately.
    """
    families = (P.grand_members() if pivots is None
                else P.grand_members(pivots))
    reader = TermReader()
    claims, notes = [], []
    for chained in families:
        pivot = reader.term(P.Sym(P._term_name(chained.pivot),
                                  P._pivot_tex(chained.pivot)))
        for step in chained.steps:
            claims.append(App(App(App(Var('Eq'), REAL), pivot),
                              reader.read(step.expr)))
            notes.append('%s : %s = %s' % (step.equation.label,
                                           P._pivot_tex(chained.pivot),
                                           step.expr))
    if not claims:
        raise Unreadable('no families to conjoin')
    body = claims[-1]
    for claim in reversed(claims[:-1]):
        body = App(App(Var('And'), claim), body)
    statement = _close(body, reader)
    return Conjecture(name, statement, reader,
                      'the whole library, conjoined', notes)


def from_equation(eq, name=None):
    """A single equation from the library as a proposition, with no joining."""
    eq = P._as_equation(eq)
    reader = TermReader()
    left, rel, right = reader.relation(eq['latex'])
    statement = _close(_relate(rel, left, right), reader)
    return Conjecture(name or _slug(eq.label), statement, reader, eq['latex'],
                      ['from %s' % eq.label])


def _relate(rel, left, right):
    """The Prop that a relation between two reals asserts."""
    if rel == '=':
        return App(App(App(Var('Eq'), REAL), left), right)
    op = RELATION_OPS.get(rel)
    if op is None:
        raise Unreadable('no reading for the relation %r as a proposition'
                         % rel)
    return App(App(Var(op), left), right)


def _close(body, reader):
    r"""Wrap a body in \forall for every quantity it mentions.

    Sorted, so the same statement always prints the same way -- which matters
    more than it sounds, because two conjectures that differ only in binder
    order would otherwise look like different theorems in a diff.
    """
    for name in sorted(reader.free, reverse=True):
        if name in CONSTANT_NAMES:
            continue                     # declared in the environment instead
        body = Pi(name, REAL, body)
    return body


def _label(derivation):
    return '_'.join(_slug(s.equation.label) for s in derivation.steps)


def _slug(text):
    out = ''.join(ch if ch.isalnum() else '_' for ch in text)
    while '__' in out:
        out = out.replace('__', '_')
    return out.strip('_')


# ------------------------------------------------------------ Lean output

def _preamble():
    """The Lean declarations matching physics_env(), generated from it.

    Written out from the same tuples the kernel environment is built from, so
    the two cannot drift apart -- a hand-maintained copy of this list had
    already gone stale once, declaring `log` while the terms said `Real.log`.
    """
    lines = ["""-- Generated by rosettalean.py from the RosettaMath knowledge base.
--
-- Real and its operations are declared, not defined: this file asks Lean
-- whether the statements below are well formed propositions, which is the
-- same question lean4.py's micro-kernel was asked.  Proving them needs the
-- field axioms and the physics, and neither is claimed here.

namespace RosettaPhys

-- Real is an axiom, so every definition over it is noncomputable and Lean's
-- code generator rejects the lot by name.  Nothing here is meant to run, so
-- the section says so once rather than annotating forty declarations.
noncomputable section

axiom Real : Type"""]
    for name in BINARY:
        lines.append('axiom %s : Real -> Real -> Real' % name)
    for name in UNARY:
        lines.append('axiom %s : Real -> Real' % name)
    lines.append('axiom Real.pow : Real -> Nat -> Real')
    lines.append('axiom Real.rpow : Real -> Real -> Real')
    lines.append('axiom Real.lit : Nat -> Real')
    for name in ('Real.le', 'Real.lt', 'Real.ge', 'Real.gt'):
        lines.append('axiom %s : Real -> Real -> Prop' % name)
    lines.append('')
    lines.append('-- The printer below emits infix * + - / ^ <= and Lean')
    lines.append('-- resolves those through type classes, so an axiomatic')
    lines.append('-- Real needs the instances spelled out or none of it')
    lines.append('-- elaborates.')
    # written with the named constructor rather than the anonymous
    # \u27e8...\u27e9 form, so the whole file stays ASCII.  Lean accepts both;
    # listings, pdflatex and half the terminals in the world accept only one
    for cls, op in (('Add', 'add'), ('Sub', 'sub'), ('Mul', 'mul'),
                    ('Div', 'div'), ('Neg', 'neg'), ('LE', 'le'),
                    ('LT', 'lt')):
        lines.append('instance : %s Real := %s.mk Real.%s' % (cls, cls, op))
    lines.append('instance : HPow Real Nat Real := HPow.mk Real.pow')
    lines.append('')
    lines.append('-- so that a numeral in an equation means a real number.')
    lines.append('-- Without it `4 * pi` does not elaborate: Real is an')
    lines.append('-- axiom here and carries no arithmetic instances of its own.')
    lines.append('instance (n : Nat) : OfNat Real n := OfNat.mk (Real.lit n)')
    lines.append('')
    lines.append('-- physical constants: named, not quantified')
    for name in CONSTANT_NAMES:
        lines.append('axiom %s : Real' % name)
    return '\n'.join(lines) + '\n'


LEAN_PREAMBLE = _preamble()

LEAN_CLOSING = '\nend\n\nend RosettaPhys\n'


def lean_source(conj, env=None):
    """One conjecture, as Lean 4 source.

    Written as `theorem ... := by sorry` rather than `axiom`: an axiom asks
    Lean only whether the statement parses and elaborates, which is worth
    knowing, but leaving a `sorry` in its place says the same thing and leaves
    the hole visible for anyone who wants to fill it.
    """
    lines = ['-- %s' % conj.source]
    for note in conj.notes:
        lines.append('--   %s' % note)
    body = _lean_expr(conj.statement, [])
    lines.append('theorem %s :\n    %s := by sorry' % (conj.name, body))
    return '\n'.join(lines)


def lean_file(conjectures, env=None):
    """A whole file: the preamble, then every conjecture."""
    parts = [LEAN_PREAMBLE]
    for conj in conjectures:
        parts.append(lean_source(conj, env))
        parts.append('')
    parts.append(LEAN_CLOSING)
    return '\n'.join(parts)


_LEAN_INFIX = {'Real.add': '+', 'Real.sub': '-',
               'Real.mul': '*', 'Real.div': '/'}


def _lean_expr(expr, names, prec=0):
    """A kernel term as Lean 4 surface syntax.

    leanexport.py does this properly for the kernel's own language; this is the
    physics dialect, where mul really should print as * if anyone is to read
    the output.
    """
    if isinstance(expr, Pi):
        binders, body = [], expr
        while isinstance(body, Pi):
            binders.append(body.var_name)
            names = names + [body.var_name]
            body = L.instantiate(body.body, Var(body.var_name))
        inner = _lean_expr(body, names)
        return 'forall %s : Real,\n      %s' % (' '.join(binders), inner)
    head, args = L.spine(expr)
    if isinstance(head, Var):
        name = head.name
        if name == 'Eq' and len(args) == 3:
            return '%s = %s' % (_lean_expr(args[1], names, 3),
                                _lean_expr(args[2], names, 3))
        if name in _LEAN_INFIX and len(args) == 2:
            op = _LEAN_INFIX[name]
            level = 5 if name in ('Real.mul', 'Real.div') else 4
            text = '%s %s %s' % (_lean_expr(args[0], names, level), op,
                                 _lean_expr(args[1], names, level + 1))
            return '(%s)' % text if level < prec else text
        if name == 'Real.pow' and len(args) == 2:
            return '%s ^ %s' % (_lean_expr(args[0], names, 7),
                                _nat_literal(args[1]))
        if name == 'Real.lit' and len(args) == 1:
            return _nat_literal(args[0])
        if name == 'And' and len(args) == 2:
            return '%s /\\ %s' % (_lean_expr(args[0], names, 2),
                                  _lean_expr(args[1], names, 1))
        if name in ('Real.le', 'Real.ge') and len(args) == 2:
            op = '<=' if name == 'Real.le' else '>='
            return '%s %s %s' % (_lean_expr(args[0], names, 3), op,
                                 _lean_expr(args[1], names, 3))
        if not args:
            return name
        return '%s %s' % (name, ' '.join(_lean_expr(a, names, 7) for a in args))
    if isinstance(expr, L.Bound):
        index = len(names) - 1 - expr.index
        return names[index] if 0 <= index < len(names) else '?%d' % expr.index
    return L.readable(expr)


def _nat_literal(expr):
    value = L.as_numeral(expr)
    return str(value) if value is not None else _lean_expr(expr, [])


# --------------------------------------------------------------- library

def conjectures(graph=None):
    """Every join the knowledge base offers, as a checked conjecture."""
    out = []
    for derivation in P.all_joins(graph):
        try:
            conj = conjecture(derivation)
            conj.check()
        except (Unreadable, L.KernelError) as exc:
            conj = None
            out.append((derivation, None, exc))
            continue
        out.append((derivation, conj, None))
    return out


def report():
    print(__doc__.strip().split('\n')[0])
    print()
    for derivation, conj, error in conjectures():
        title = ' = '.join(s.equation.label for s in derivation.steps)
        print('%s' % title)
        print('    latex  %s' % derivation.statement())
        if error is not None:
            print('    lean   -- not yet readable: %s' % error)
            print()
            continue
        print('    vars   %s' % (', '.join(conj.variables) or '-'))
        if conj.constants:
            print('    const  %s' % ', '.join(conj.constants))
        print('    sort   %s' % conj.check())
        print('    lean   %s' % _one_line(conj))
        print()


def _one_line(conj):
    return ' '.join(_lean_expr(conj.statement, []).split())


def selftest():
    """Check the bridge end to end."""
    failures = []

    def check(label, ok):
        print('  %-58s %s' % (label, 'ok' if ok else 'FAIL'))
        if not ok:
            failures.append(label)

    print('reading terms')
    r = TermReader()
    check('a product is a product, not an application',
          L.readable(r.read('m c')) == 'Real.mul(m)(c)')
    r = TermReader()
    check('a superscript is a power with a Nat exponent',
          L.readable(r.read('c^2')) == 'Real.pow(c)(2)')
    r = TermReader()
    check('a subscript makes a distinct quantity',
          sorted(TermReader().free) == [] and
          'm_1' in (lambda t: t.free)(_read_into('m_1 m_2')))
    r = TermReader()
    check('a fraction is a division', L.readable(r.read(r'\frac{a}{b}'))
          == 'Real.div(a)(b)')
    r = TermReader()
    check('a leading minus negates',
          L.readable(r.read('-a')).startswith('Real.neg('))
    r = TermReader()
    check('a sum splits at the right place',
          L.readable(r.read('a b + c')) == 'Real.add(Real.mul(a)(b))(c)')
    r = TermReader()
    check('log applies rather than multiplying',
          L.readable(r.read(r'k \log W')) == 'Real.mul(k)(Real.log(W))')
    r = TermReader()
    check('hbar and h stay different quantities',
          sorted(_read_into(r'\hbar h').free) == ['h', 'hbar'])

    print('braces')
    r = TermReader()
    left, rel, right = r.relation(r'\overbrace{a = b}^{\text{x}}')
    check('an overbrace round the whole statement is stripped',
          rel == '=' and L.readable(left) == 'a')
    r = TermReader()
    check('an underbrace reads as the term inside it',
          L.readable(r.read(r'\underbrace{m c}_{\text{label}}'))
          == 'Real.mul(m)(c)')
    r = TermReader()
    r.relation(P.join('Mass-energy equivalence', 'Planck relation').latex())
    check('and its label is kept as provenance',
          r.labels == ['Mass-energy equivalence', 'Planck relation'])
    check('an operator refuses to be read as a term',
          _refuses(r'\nabla^2 \psi'))
    check('and so does a tensor component', _refuses(r'G_{\mu\nu}'))

    print('conjectures')
    d = P.join('Mass-energy equivalence', 'Planck relation')
    conj = conjecture(d)
    check('the join becomes a Prop', conj.check() == 'Prop')
    known = {'Eq', 'Real', 'Real.mul', 'Real.pow', 'succ', 'zero'}
    check('every quantity is bound or declared',
          not (L.free_names(conj.statement) - known - set(CONSTANT_NAMES)))
    check('and the constants really are declared',
          all(n in PHYS_ENV for n in conj.constants))
    check('the binders are the quantities that appeared',
          conj.variables == ['m', 'nu'] and conj.constants == ['c', 'h'])
    check('mass-energy and Planck both named in the notes',
          any('Mass-energy' in n for n in conj.notes) and
          any('Planck' in n for n in conj.notes))

    single = from_equation('Ideal gas law')
    check('a lone equation is a Prop too', single.check() == 'Prop')

    print('lean output')
    text = conj.lean()
    check('the Lean text states a theorem', text.count('theorem') == 1)
    check('it quantifies over Real', 'forall' in text and 'Real' in text)
    check('multiplication prints infix', '*' in text)
    check('the power prints as ^', '^ 2' in text)
    check('the source equation is kept as a comment',
          'Mass-energy equivalence' in text)

    whole = lean_file([conj])
    check('a file carries the preamble', 'namespace RosettaPhys' in whole)
    check('the whole file is ASCII', whole.isascii())
    check('and closes it', 'end RosettaPhys' in whole)

    print('the whole library at once')
    grand = grand_conjecture()
    check('it is a single proposition', grand.check() == 'Prop')
    check('conjoining many equations', grand.notes and len(grand.notes) > 20)
    check('sharing its variables across them',
          'm' in grand.variables and grand.statement is not None)
    check('and printing as a conjunction', '/\\' in grand.lean())

    print('the library')
    results = conjectures()
    readable = [c for _, c, e in results if c is not None]
    check('every join in the library reads',
          len(readable) == len(results))
    check('and every one is a Prop',
          all(c.check() == 'Prop' for c in readable))

    print()
    if failures:
        print('%d failure(s): %s' % (len(failures), ', '.join(failures)))
    else:
        print('rosettalean: %d conjectures, all well typed.' % len(readable))
    return len(failures)


def _refuses(latex):
    """Did the reader decline this, as it should?"""
    try:
        TermReader().read(latex)
    except (Unreadable, P.Unreadable):
        return True
    return False


def _read_into(latex):
    reader = TermReader()
    reader.read(latex)
    return reader


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    if '--lean' in sys.argv:
        print(lean_file([c for _, c, e in conjectures() if c is not None]))
    else:
        report()
