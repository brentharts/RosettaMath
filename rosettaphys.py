#!/usr/bin/env python3
r"""RosettaPhys -- the offline maths and physics knowledge base for RosettaMath.

This is data, not machinery.  rosettaui.py imports it and does the drawing;
rosettaphys.py knows only what the symbols mean.  Keeping them apart means the
knowledge base can grow -- new fields, new equations, longer articles -- without
anyone having to read the parser or the Qt layer.

Four kinds of entry live here.

SYMBOLS -- one entry per glyph, keyed by its LaTeX spelling.  Built through
add_symbol(), or in bulk from the GREEK_LOWER / GREEK_UPPER / OPERATORS / LATIN
tables.  Each carries a blurb that says what the symbol *is* and what it
conventionally *denotes*, since that is the part a newcomer to physics notation
cannot look up in a syntax reference.

    add_symbol(latex, unicode, name, category, blurb, wikipedia_slug, aka='')

CONCEPTS -- longer articles for the browsable offline encyclopedia, cross
linked to the symbols and equations they talk about.

    add_concept(title, category, body, wikipedia_slug, symbols=(), equations=())

EQUATIONS -- a signature library for the classifier.  'must' lists the features
that have to be present for the equation to be a candidate; 'nice' lists the
ones that raise confidence.  The feature vocabulary comes from rosettaui's
extract_features(): bare symbol names ('psi', 'hbar', 'E') and structural tags
prefixed with 'S:' ('S:frac', 'S:nabla2', 'S:sup2').

    equation(name=, field=, latex=, slug=, must=[], nice=[], blurb=)

EQUATION_FAMILIES -- the fallback when no single equation matches: a feature
set paired with a description of the genre it belongs to.

CONSTANTS maps symbol names to scipy.constants attributes, which is what stops
c and hbar being inferred as function arguments during translation.

    python3 rosettaphys.py             a census of the knowledge base
    python3 rosettaphys.py --selftest  check every entry is well formed
"""

import math
import re

WIKI = 'https://en.wikipedia.org/wiki/'


# ------------------------------------------------------------------- nodes
#
# Everything the knowledge base knows about is a node, and nodes are joined by
# typed edges.  The three kinds -- Symbol, Concept, Equation -- differ in the
# fields they carry, not in how they connect, so the graph code below never has
# to ask what sort of thing it is looking at.
#
# Each class subclasses dict.  That is deliberate: the entries were plain dicts
# before, every reader in rosettaui.py says entry['blurb'], and none of those
# readers should have to change for the graph to exist.  Attribute access is
# added on top because entry.blurb reads better in new code.

class Node(dict):
    """One thing the knowledge base knows about."""

    kind = 'node'
    key_field = 'name'

    def __init__(self, **fields):
        dict.__init__(self, fields)
        self.out = []                 # edges leaving this node
        self.inn = []                 # edges arriving at it

    # entry.blurb as a synonym for entry['blurb'], without losing the dict
    def __getattr__(self, attr):
        try:
            return self[attr]
        except KeyError:
            raise AttributeError('%s has no %r' % (type(self).__name__, attr))

    @property
    def key(self):
        """What this node is called in the graph.  Unique across all kinds."""
        return '%s:%s' % (self.kind, self[self.key_field])

    @property
    def label(self):
        """A human readable one-liner."""
        return self[self.key_field]

    def links(self, kind=None, outgoing=True, incoming=False):
        """Edges touching this node, optionally of one relation only."""
        edges = (list(self.out) if outgoing else []) + \
                (list(self.inn) if incoming else [])
        return [e for e in edges if kind is None or e.kind == kind]

    def related(self, kind=None, outgoing=True, incoming=False):
        """The nodes on the other end of those edges."""
        out = []
        for e in self.links(kind, outgoing, incoming):
            other = e.dst if e.src is self else e.src
            if other not in out:
                out.append(other)
        return out

    def __repr__(self):
        return '<%s %s>' % (type(self).__name__, self.label)

    # dicts are unhashable by default; nodes are identities, so hash on one
    __hash__ = object.__hash__

    def __eq__(self, other):
        return self is other

    def __ne__(self, other):
        return self is not other


class Symbol(Node):
    """One glyph, its readings, and where it comes from."""

    kind = 'symbol'
    key_field = 'latex'

    @property
    def label(self):
        return self['name']


class Concept(Node):
    """A prose article about a convention, joined to what it talks about."""

    kind = 'concept'
    key_field = 'title'


class Equation(Node):
    """A named equation, its signature, and the symbols it is built from."""

    kind = 'equation'
    key_field = 'name'

    def features(self):
        """Every feature in the signature, must and nice together."""
        return list(self.get('must', ())) + list(self.get('nice', ()))

    def sides(self):
        """(left, right) of the top level =, or None if there is no top =.

        Only a depth-zero equals counts, so the = inside a \\frac or a
        subscript is not mistaken for the one that splits the statement.
        """
        return split_relation(self['latex'])


class Edge:
    """A typed, directed link between two nodes.

    The direction is the one the relation is named for -- an equation USES a
    symbol, not the other way round -- but every edge is filed on both nodes,
    so either end can be walked from.
    """

    __slots__ = ('kind', 'src', 'dst', 'note')

    def __init__(self, kind, src, dst, note=''):
        self.kind = kind
        self.src = src
        self.dst = dst
        self.note = note

    def __repr__(self):
        return '<%s %s -> %s%s>' % (self.kind, self.src.label, self.dst.label,
                                    ' (%s)' % self.note if self.note else '')


# The relation vocabulary.  Kept as names rather than bare strings so that a
# typo is an AttributeError here instead of an edge that silently never matches.
USES = 'uses'                 # equation -> symbol it is built from
MENTIONS = 'mentions'         # concept  -> symbol it discusses
CITES = 'cites'               # concept  -> equation it discusses
SHARES = 'shares'             # equation -> equation, via a common quantity
FIELD = 'field'               # equation -> equation, same field of physics
SPECIALISES = 'specialises'   # equation -> the more general one it comes from
LIMIT_OF = 'limit-of'         # equation -> what it becomes in some limit
DEFINES = 'defines'           # equation -> the quantity it introduces
DENOTES = 'denotes'           # equation -> what one of its letters means


def split_relation(latex):
    r"""Split a LaTeX statement on its top level relation symbol.

    Returns (left, relation, right), or None when there is no relation at
    depth zero.  Brace depth is tracked so that the = in \frac{a=b}{c} is not
    mistaken for the one that splits the statement, and \leq and friends count
    as well as = because plenty of physics is stated as an inequality.
    """
    depth = 0
    i = 0
    while i < len(latex):
        ch = latex[i]
        if ch == '\\':                      # a command; skip its name whole
            j = i + 1
            while j < len(latex) and (latex[j].isalpha()):
                j += 1
            word = latex[i:j] or latex[i:i + 2]
            if depth == 0 and word in RELATIONS:
                return latex[:i].strip(), word, latex[j:].strip()
            i = max(j, i + 2)
            continue
        if ch in '{[':
            depth += 1
        elif ch in '}]':
            depth -= 1
        elif ch == '=' and depth == 0:
            # not part of \neq, and not the = of a \sum_{n=0} (that is braced)
            return latex[:i].strip(), '=', latex[i + 1:].strip()
        i += 1
    return None


RELATIONS = (r'\leq', r'\geq', r'\neq', r'\equiv', r'\approx', r'\simeq',
             r'\propto', r'\sim', r'\to')



# ---------------------------------------------------------------- symbols
#
# Every entry:  unicode, display name, category, blurb, wikipedia slug.
# The blurb is the offline description -- it should say what the symbol *is*
# and what it conventionally *denotes*, since that is the part a newcomer to
# physics notation cannot look up in a syntax reference.

SYMBOLS = {}


def add_symbol(latex, uni, name, category, blurb, slug, aka=''):
    SYMBOLS[latex] = Symbol(
        latex=latex, unicode=uni, name=name, category=category,
        blurb=blurb, wiki=WIKI + slug, aka=aka)
    return SYMBOLS[latex]


GREEK_LOWER = [
    (r'\alpha', 'α', 'Alpha',
     'First letter of the Greek alphabet. In physics: the fine-structure '
     'constant (~1/137), angular acceleration, the alpha particle (a helium '
     'nucleus), thermal expansion or absorption coefficients, and in '
     'statistics the significance level of a test.', 'Alpha'),
    (r'\beta', 'β', 'Beta',
     'In relativity, beta is the velocity as a fraction of light speed, v/c, '
     'the quantity that appears inside the Lorentz factor. In plasma physics '
     'it is the ratio of plasma pressure to magnetic pressure. Also beta '
     'decay, and regression coefficients in statistics.', 'Beta'),
    (r'\gamma', 'γ', 'Gamma',
     'The Lorentz factor of special relativity, 1/sqrt(1-v^2/c^2), which grows '
     'without bound as v approaches c. Also the photon (gamma ray), the '
     'adiabatic index (ratio of specific heats) in thermodynamics, and the '
     'Euler-Mascheroni constant.', 'Gamma'),
    (r'\delta', 'δ', 'Delta (small)',
     'A small or infinitesimal change, an inexact differential, the Dirac '
     'delta function (an idealised unit spike), and the Kronecker delta, which '
     'is 1 when its two indices agree and 0 otherwise.', 'Delta_(letter)'),
    (r'\epsilon', 'ϵ', 'Epsilon',
     'A vanishingly small positive quantity -- the epsilon of "for every '
     'epsilon there exists a delta" in analysis. In physics: permittivity, '
     'strain, emissivity, and orbital eccentricity.', 'Epsilon'),
    (r'\varepsilon', 'ε', 'Epsilon (variant)',
     'The variant shape of epsilon, used identically. Often reserved for '
     'permittivity or for the Levi-Civita symbol when the plain epsilon is '
     'already taken by a small quantity.', 'Epsilon'),
    (r'\zeta', 'ζ', 'Zeta',
     'The Riemann zeta function, whose nontrivial zeros are the subject of the '
     'Riemann hypothesis. In mechanics it is the damping ratio of an '
     'oscillator.', 'Zeta'),
    (r'\eta', 'η', 'Eta',
     'Efficiency (of an engine or process), dynamic viscosity in fluid '
     'mechanics, and the Minkowski metric tensor of flat spacetime when '
     'written with indices.', 'Eta'),
    (r'\theta', 'θ', 'Theta',
     'The archetypal angle. Also a polar or scattering angle, the Heaviside '
     'step function, and in statistics a generic parameter to be estimated.',
     'Theta'),
    (r'\vartheta', 'ϑ', 'Theta (variant)',
     'A cursive variant of theta, used for a second angle or for the Jacobi '
     'theta functions.', 'Theta'),
    (r'\iota', 'ι', 'Iota',
     'Rarely used because it is easily confused with the letter i; it survives '
     'in the phrase "not one iota" and as an inclusion map in mathematics.',
     'Iota'),
    (r'\kappa', 'κ', 'Kappa',
     'Curvature of a curve, thermal conductivity, the Einstein gravitational '
     'constant 8*pi*G/c^4 in the field equations, and the wavenumber in some '
     'conventions.', 'Kappa'),
    (r'\lambda', 'λ', 'Lambda (small)',
     'Wavelength -- the distance between successive crests of a wave. Also an '
     'eigenvalue in linear algebra, the rate parameter of a Poisson process, '
     'and a Lagrange multiplier in constrained optimisation.', 'Lambda'),
    (r'\mu', 'μ', 'Mu',
     'The SI prefix micro (10^-6), the magnetic permeability of a medium, the '
     'mean of a distribution, the coefficient of friction, the reduced mass of '
     'a two-body system, and the muon.', 'Mu_(letter)'),
    (r'\nu', 'ν', 'Nu',
     'Frequency in cycles per second -- the nu of Planck\'s E = h*nu. Also the '
     'neutrino, and kinematic viscosity in fluid dynamics. Easily confused '
     'with an italic v.', 'Nu_(letter)'),
    (r'\xi', 'ξ', 'Xi',
     'A generic dummy variable or random perturbation; in stochastic equations '
     'it is the noise term. Also a coherence length, and the correlation '
     'function in cosmology.', 'Xi_(letter)'),
    (r'\pi', 'π', 'Pi (small)',
     'The ratio of a circle\'s circumference to its diameter, 3.14159..., an '
     'irrational and transcendental number. Also, in different contexts, the '
     'prime-counting function and the pion.', 'Pi'),
    (r'\rho', 'ρ', 'Rho',
     'Density -- mass per unit volume, charge per unit volume, or probability '
     'per unit volume, depending on context. In quantum mechanics rho is the '
     'density matrix describing a mixed state; in electromagnetism it is '
     'charge density; in circuits it is resistivity.', 'Rho'),
    (r'\sigma', 'σ', 'Sigma (small)',
     'Standard deviation -- the spread of a distribution about its mean. Also '
     'a cross-section in scattering, electrical conductivity, mechanical '
     'stress, surface charge density, and the Stefan-Boltzmann constant.',
     'Sigma'),
    (r'\tau', 'τ', 'Tau',
     'A time constant or characteristic decay time, proper time in relativity '
     '(the time measured by a clock carried along a worldline), torque in '
     'mechanics, and the tau lepton.', 'Tau'),
    (r'\upsilon', 'υ', 'Upsilon', 'Rarely used; appears as the Upsilon meson '
     'in particle physics.', 'Upsilon_(letter)'),
    (r'\phi', 'ϕ', 'Phi',
     'A scalar field or potential -- the gravitational potential, the electric '
     'potential, or in quantum field theory the Klein-Gordon field itself. '
     'Also an azimuthal angle and the golden ratio.', 'Phi'),
    (r'\varphi', 'φ', 'Phi (variant)',
     'The variant shape of phi, used interchangeably; often the phase of a '
     'wave or an azimuthal angle when the plain phi is a potential.', 'Phi'),
    (r'\chi', 'χ', 'Chi',
     'Susceptibility (electric or magnetic response to an applied field), the '
     'chi-squared statistic, and the Euler characteristic in topology.',
     'Chi_(letter)'),
    (r'\psi', 'ψ', 'Psi',
     'The wavefunction of quantum mechanics: a complex-valued amplitude whose '
     'squared modulus gives a probability density. Also a stream function in '
     'fluid dynamics.', 'Psi_(Greek)'),
    (r'\omega', 'ω', 'Omega (small)',
     'Angular frequency in radians per second, equal to 2*pi times the '
     'ordinary frequency. Also angular velocity, and a root of unity in '
     'algebra.', 'Omega'),
]

GREEK_UPPER = [
    (r'\Gamma', 'Γ', 'Gamma (capital)',
     'The gamma function, which extends the factorial to real and complex '
     'numbers. In general relativity the Christoffel symbols, written with '
     'three indices, encode how coordinates curve.', 'Gamma_function'),
    (r'\Delta', 'Δ', 'Delta (capital)',
     'A finite change or difference: Delta x means "the change in x". Also the '
     'Laplace operator in some traditions, and the discriminant of a '
     'polynomial.', 'Delta_(letter)'),
    (r'\Theta', 'Θ', 'Theta (capital)',
     'A characteristic temperature (Debye or Einstein temperature) and, in '
     'computer science, the asymptotic tight bound notation.', 'Theta'),
    (r'\Lambda', 'Λ', 'Lambda (capital)',
     'The cosmological constant -- the energy density of empty space driving '
     'the accelerating expansion of the universe, and the "Lambda" in the '
     'Lambda-CDM standard model of cosmology.', 'Cosmological_constant'),
    (r'\Xi', 'Ξ', 'Xi (capital)',
     'The grand canonical partition function in statistical mechanics, and the '
     'Xi baryons.', 'Xi_(letter)'),
    (r'\Pi', 'Π', 'Pi (capital)',
     'The product operator: multiply a sequence of terms together, exactly as '
     'capital Sigma sums them.', 'Multiplication'),
    (r'\Sigma', 'Σ', 'Sigma (capital)',
     'The summation operator: add up a sequence of terms. Also a covariance '
     'matrix in statistics and the self-energy in field theory.', 'Summation'),
    (r'\Upsilon', 'Υ', 'Upsilon (capital)', 'Rare; the Upsilon meson.',
     'Upsilon_meson'),
    (r'\Phi', 'Φ', 'Phi (capital)',
     'A flux -- the amount of a field passing through a surface. Magnetic flux '
     'in Faraday\'s law, electric flux in Gauss\'s law. Also the cumulative '
     'distribution function of the normal distribution.', 'Flux'),
    (r'\Psi', 'Ψ', 'Psi (capital)',
     'A wavefunction, usually the full many-body or time-dependent one, with '
     'the lowercase psi reserved for a single-particle or spatial part.',
     'Wave_function'),
    (r'\Omega', 'Ω', 'Omega (capital)',
     'The ohm, unit of electrical resistance; the number of accessible '
     'microstates in Boltzmann\'s entropy formula; a solid angle; and the '
     'density parameter in cosmology.', 'Omega'),
]

for _l, _u, _n, _b, _s in GREEK_LOWER:
    add_symbol(_l, _u, _n, 'Greek letters', _b, _s)
for _l, _u, _n, _b, _s in GREEK_UPPER:
    add_symbol(_l, _u, _n, 'Greek letters', _b, _s)


OPERATORS = [
    (r'=', '=', 'Equals', 'Relations',
     'Asserts that two expressions denote the same value. Note the clash with '
     'programming: in Python "=" means assignment and "==" means comparison, '
     'which is why RosettaMath maps the LaTeX "=" to "==" and "\\gets" to "=".',
     'Equality_(mathematics)'),
    (r'\neq', '≠', 'Not equal', 'Relations', 'Asserts two values differ.',
     'Inequality_(mathematics)'),
    (r'\approx', '≈', 'Approximately equal', 'Relations',
     'Equal to within an accepted tolerance or to leading order.',
     'Approximation'),
    (r'\equiv', '≡', 'Identically equal', 'Relations',
     'Stronger than equality: true for all values, or a definition, or '
     'congruence in modular arithmetic.', 'Identity_(mathematics)'),
    (r'\propto', '∝', 'Proportional to', 'Relations',
     'Equal up to a constant factor. Physicists use it to state a scaling law '
     'while deliberately discarding the constant.', 'Proportionality_(mathematics)'),
    (r'\sim', '∼', 'Similar / of order', 'Relations',
     'Of the same order of magnitude, or asymptotically equal, or "is '
     'distributed as" in probability.', 'Asymptotic_analysis'),
    (r'\leq', '≤', 'Less than or equal', 'Relations',
     'Ordering: the left side is smaller than or equal to the right. Common as '
     'a constraint boundary, where the equality case is exactly the '
     'interesting one.', 'Inequality_(mathematics)'),
    (r'\geq', '≥', 'Greater than or equal', 'Relations',
     'Ordering in the other direction. Physical bounds are usually stated this '
     'way -- the uncertainty principle, for instance, sets a floor rather than '
     'an exact value.', 'Inequality_(mathematics)'),
    (r'\ll', '≪', 'Much less than', 'Relations',
     'Signals that a term is negligible and about to be dropped from an '
     'approximation.', 'Inequality_(mathematics)'),
    (r'\gg', '≫', 'Much greater than', 'Relations',
     'The dominant term in an approximation.', 'Inequality_(mathematics)'),
    (r'\pm', '±', 'Plus-minus', 'Operators',
     'Both signs are valid, as in the quadratic formula, or an experimental '
     'uncertainty.', 'Plus%E2%80%93minus_sign'),
    (r'\mp', '∓', 'Minus-plus', 'Operators',
     'The opposite sign to a paired plus-minus in the same expression.',
     'Plus%E2%80%93minus_sign'),
    (r'\times', '×', 'Times / cross product', 'Operators',
     'Ordinary multiplication, or the cross product of two vectors, which '
     'yields a third vector perpendicular to both.', 'Cross_product'),
    (r'\cdot', '⋅', 'Dot / scalar product', 'Operators',
     'Multiplication, or the dot product of two vectors, which yields a '
     'scalar measuring how much they point the same way.', 'Dot_product'),
    (r'\div', '÷', 'Division', 'Operators',
     'Division. Rare in published mathematics, which prefers a stacked '
     'fraction or a slash; it survives mainly in elementary teaching.',
     'Division_(mathematics)'),
    (r'\ast', '∗', 'Convolution / conjugate', 'Operators',
     'Convolution of two functions, or complex conjugation when written as a '
     'superscript.', 'Convolution'),
    (r'\otimes', '⊗', 'Tensor product', 'Operators',
     'Combines two vector spaces into a larger one -- how the state space of a '
     'composite quantum system is built from its parts.', 'Tensor_product'),
    (r'\oplus', '⊕', 'Direct sum', 'Operators',
     'Combines spaces side by side rather than multiplicatively; also XOR.',
     'Direct_sum'),
    (r'\infty', '∞', 'Infinity', 'Operators',
     'Unbounded growth. Not a number: it appears as a limit of integration or '
     'inside a limit, never as a value to compute with.', 'Infinity'),
    (r'\partial', '∂', 'Partial derivative', 'Calculus',
     'Rate of change with respect to one variable while all others are held '
     'fixed. The curly d distinguishes it from the total derivative d, which '
     'accounts for indirect dependence too.', 'Partial_derivative'),
    (r'\nabla', '∇', 'Nabla / del', 'Calculus',
     'The vector of partial derivatives. Applied to a scalar it gives the '
     'gradient (direction of steepest increase); dotted with a vector it gives '
     'the divergence (how much a field spreads out); crossed with a vector it '
     'gives the curl (how much it circulates).', 'Del'),
    (r'\Box', '□', "d'Alembert operator", 'Calculus',
     'The d\'Alembertian, or wave operator, or box operator -- the Laplace '
     'operator of Minkowski spacetime. It is the second time derivative '
     'divided by c squared, minus the spatial Laplacian, so it treats time '
     'and space almost alike, differing only by the minus sign that '
     'separates a spacetime interval from a Euclidean distance. Setting it '
     'to zero gives the wave equation in a form that is manifestly the same '
     'in every reference frame, which is why it is the natural operator of '
     'special relativity and electromagnetism. Named for Jean le Rond '
     "d'Alembert; the box notation is due to Poincare, and by analogy with "
     'nabla it is sometimes called the quabla.', "D'Alembert_operator"),
    (r'\int', '∫', 'Integral', 'Calculus',
     'Accumulates a quantity over an interval -- the area under a curve, or '
     'the total of an infinitesimal contribution. The elongated S stands for '
     '"summa".', 'Integral'),
    (r'\oint', '∮', 'Contour integral', 'Calculus',
     'An integral around a closed loop or over a closed surface. Central to '
     'Maxwell\'s equations in integral form and to complex analysis.',
     'Contour_integration'),
    (r'\iint', '∬', 'Double integral', 'Calculus',
     'Integration over a two-dimensional region.', 'Multiple_integral'),
    (r'\sum', '∑', 'Summation', 'Calculus',
     'Add the term to its right once for each value of the index, which runs '
     'from the value below the sigma to the value above. Translates directly '
     'to a Python for loop with an accumulator.', 'Summation'),
    (r'\prod', '∏', 'Product', 'Calculus',
     'Multiply a sequence of terms, the multiplicative twin of summation.',
     'Multiplication'),
    (r'\lim', 'lim', 'Limit', 'Calculus',
     'The value an expression approaches as its variable approaches some '
     'target, without necessarily ever reaching it. The foundation of both '
     'derivatives and integrals.', 'Limit_(mathematics)'),
    (r'\sqrt', '√', 'Square root', 'Operators',
     'The non-negative number whose square is the argument. In LaTeX the '
     'optional bracket argument gives an n-th root.', 'Square_root'),
    (r'\frac', '/', 'Fraction', 'Structures',
     'A ratio, written with the numerator stacked above the denominator. '
     'RosettaMath translates \\frac{a}{b} to (a)/(b) -- the parentheses matter, '
     'because the visual grouping of the stacked form is invisible once it is '
     'flattened onto one line.', 'Fraction'),
    (r'\in', '∈', 'Element of', 'Set theory',
     'Membership: the thing on the left belongs to the set on the right. Maps '
     'straight onto Python\'s "in".', 'Element_(mathematics)'),
    (r'\notin', '∉', 'Not an element of', 'Set theory',
     'The negation of membership: the thing on the left is not in the set on '
     'the right. Maps onto Python\'s "not in".', 'Element_(mathematics)'),
    (r'\subset', '⊂', 'Subset', 'Set theory',
     'Every element of the left set is also in the right set.', 'Subset'),
    (r'\cup', '∪', 'Union', 'Set theory', 'All elements in either set.',
     'Union_(set_theory)'),
    (r'\cap', '∩', 'Intersection', 'Set theory',
     'Only the elements in both sets.', 'Intersection_(set_theory)'),
    (r'\emptyset', '∅', 'Empty set', 'Set theory', 'The set with no elements.',
     'Empty_set'),
    (r'\forall', '∀', 'For all', 'Logic',
     'Universal quantifier: the statement holds for every member of the '
     'domain.', 'Universal_quantification'),
    (r'\exists', '∃', 'There exists', 'Logic',
     'Existential quantifier: at least one member satisfies the statement.',
     'Existential_quantification'),
    (r'\land', '∧', 'Logical and', 'Logic', 'True only if both sides are true.',
     'Logical_conjunction'),
    (r'\lor', '∨', 'Logical or', 'Logic', 'True if either side is true.',
     'Logical_disjunction'),
    (r'\lnot', '¬', 'Logical not', 'Logic',
     'Negation: flips true to false. Note that negating a quantifier also '
     'swaps it -- the negation of "for all x, P" is "there exists an x with '
     'not P", a rewriting rule worth internalising.', 'Negation'),
    (r'\to', '→', 'Maps to / tends to', 'Logic',
     'Either a function\'s domain-to-codomain arrow or a limiting process.',
     'Function_(mathematics)'),
    (r'\mapsto', '↦', 'Maps to', 'Logic',
     'Names what a function does to a particular input, as opposed to the '
     'bare arrow which names the sets involved.', 'Function_(mathematics)'),
    (r'\implies', '⟹', 'Implies', 'Logic',
     'Material implication: if the left side holds, so does the right.',
     'Material_conditional'),
    (r'\iff', '⟺', 'If and only if', 'Logic',
     'Implication in both directions; logical equivalence.', 'If_and_only_if'),
    (r'\langle', '⟨', 'Bra / left angle', 'Quantum',
     'Opens a Dirac bra-ket. A bra is the conjugate transpose of a ket, and '
     'the two together form an inner product. Also denotes an expectation '
     'value or time average.', 'Bra%E2%80%93ket_notation'),
    (r'\rangle', '⟩', 'Ket / right angle', 'Quantum',
     'Closes a Dirac bra-ket. A ket is a state vector in Hilbert space.',
     'Bra%E2%80%93ket_notation'),
    (r'\dagger', '†', 'Dagger / adjoint', 'Quantum',
     'Conjugate transpose. An operator equal to its own dagger is Hermitian '
     'and has real eigenvalues, which is why observables are Hermitian.',
     'Hermitian_adjoint'),
    (r'\hbar', 'ℏ', 'h-bar', 'Constants',
     'The reduced Planck constant, h/2*pi, about 1.055e-34 J*s. The quantum of '
     'action: it sets the scale at which quantum effects matter and appears in '
     'every quantum equation. RosettaMath maps it to scipy.constants.hbar.',
     'Planck_constant'),
    (r'\ell', 'ℓ', 'Script l', 'Structures',
     'A length or an angular momentum quantum number; the script form avoids '
     'confusion with the digit 1.', 'L'),
    (r'\vec', '→', 'Vector accent', 'Structures',
     'Marks a quantity with both magnitude and direction. Bold type is the '
     'common alternative.', 'Euclidean_vector'),
    (r'\hat', '^', 'Hat accent', 'Structures',
     'A unit vector (length one), or in quantum mechanics an operator rather '
     'than a plain number, or in statistics an estimated quantity.',
     'Unit_vector'),
    (r'\dot', '˙', 'Dot accent', 'Structures',
     'Newton\'s notation for a time derivative: one dot is d/dt, two dots is '
     'the second derivative. Ubiquitous in mechanics.', 'Notation_for_differentiation'),
    (r'\bar', '¯', 'Bar accent', 'Structures',
     'An average, or a complex conjugate, or an antiparticle.', 'Mean'),
    (r'\tilde', '~', 'Tilde accent', 'Structures',
     'A transformed or approximate version of a quantity, often its Fourier '
     'transform.', 'Tilde'),
    (r'\mathbb', 'ℝ', 'Blackboard bold', 'Structures',
     'Denotes a standard number system: N naturals, Z integers, Q rationals, '
     'R reals, C complex.', 'Blackboard_bold'),
    (r'\Re', 'ℜ', 'Real part', 'Operators', 'The real component of a complex number.',
     'Complex_number'),
    (r'\Im', 'ℑ', 'Imaginary part', 'Operators',
     'The imaginary component of a complex number.', 'Complex_number'),
    (r'\log', 'log', 'Logarithm', 'Functions',
     'The inverse of exponentiation. Turns products into sums, which is why it '
     'appears throughout entropy and information theory.', 'Logarithm'),
    (r'\ln', 'ln', 'Natural logarithm', 'Functions',
     'Logarithm to base e. It is the "natural" one because its derivative is '
     'simply 1/x, with no stray constant factor, which is why it is the '
     'logarithm that appears in solutions of differential equations.',
     'Natural_logarithm'),
    (r'\exp', 'exp', 'Exponential', 'Functions',
     'e raised to a power; the function equal to its own derivative, which is '
     'why it describes every unconstrained growth and decay process.',
     'Exponential_function'),
    (r'\sin', 'sin', 'Sine', 'Functions',
     'The vertical coordinate on the unit circle; with cosine it generates all '
     'oscillation and, via Fourier analysis, all periodic behaviour.',
     'Sine_and_cosine'),
    (r'\cos', 'cos', 'Cosine', 'Functions',
     'The horizontal coordinate on the unit circle, a quarter cycle out of '
     'phase with sine.', 'Sine_and_cosine'),
    (r'\tan', 'tan', 'Tangent', 'Functions', 'Sine over cosine; the slope of a line '
     'at a given angle.', 'Trigonometric_functions'),
    (r'\det', 'det', 'Determinant', 'Linear algebra',
     'A scalar summarising a square matrix: it is the volume scaling factor of '
     'the transformation, and zero exactly when the matrix is singular.',
     'Determinant'),
    (r'\cdots', '⋯', 'Ellipsis', 'Structures',
     'Omitted terms following an obvious pattern.', 'Ellipsis'),
]

for _l, _u, _n, _c, _b, _s in OPERATORS:
    add_symbol(_l, _u, _n, _c, _b, _s)

# The horizontal braces are annotations rather than operators: they change
# nothing about the value of the expression, they group part of it and give
# that part a name.  That makes them worth a glossary entry of their own,
# because a reader meeting one needs to be told it is a label and not an
# operation they have failed to recognise.
add_symbol(r'\underbrace', '\u23df', 'Underbrace', 'Structures',
           'A brace drawn beneath part of an expression, with a label under '
           'it. Purely annotation: it groups a span and names it, and removing '
           'it would not change the value of anything. Common in physics for '
           'pointing out that one term is the kinetic energy or that another '
           'is a correction that vanishes in some limit.',
           'Underbrace')
add_symbol(r'\overbrace', '\u23de', 'Overbrace', 'Structures',
           'The same annotation as an underbrace, drawn above the expression '
           'with its label on top. Which one an author picks is usually a '
           'matter of what else is crowding the line rather than of meaning.',
           'Underbrace')


# Single Latin letters are the worst offenders for overloading -- the same
# glyph means a dozen different things.  We list the readings rather than
# pretend there is one.
LATIN = [
    ('c', 'Speed of light', 'Constants',
     'In relativity, the speed of light in vacuum, exactly 299792458 m/s -- a '
     'conversion factor between space and time, and the universal speed limit. '
     'Elsewhere: a generic constant, the speed of sound, or heat capacity. '
     'RosettaMath can resolve it to scipy.constants.c.', 'Speed_of_light'),
    ('G', 'Gravitational constant', 'Constants',
     'Newton\'s constant, 6.674e-11 m^3/(kg*s^2), the weakest and least '
     'precisely measured of the fundamental constants. Also the Gibbs free '
     'energy in thermodynamics and the Einstein tensor in relativity.',
     'Gravitational_constant'),
    ('h', 'Planck constant', 'Constants',
     'The quantum of action, 6.626e-34 J*s, relating a photon\'s energy to its '
     'frequency. Also a height, or a step size in numerical methods.',
     'Planck_constant'),
    ('k', 'Boltzmann constant / wavenumber', 'Constants',
     'The Boltzmann constant, 1.381e-23 J/K, converting temperature into '
     'energy per degree of freedom -- often written with a B subscript. Also '
     'the wavenumber 2*pi/lambda, a spring constant, or a summation index.',
     'Boltzmann_constant'),
    ('e', 'Euler\'s number / elementary charge', 'Constants',
     'Either 2.71828..., the base of the natural logarithm, or the elementary '
     'charge 1.602e-19 C. Which one is meant is pure context: an exponent '
     'means the former, a charge means the latter.', 'E_(mathematical_constant)'),
    ('i', 'Imaginary unit', 'Constants',
     'The square root of -1. In quantum mechanics its appearance in the '
     'Schrodinger equation is what makes the wavefunction complex and '
     'interference possible. Engineers write j instead, to free i for current.',
     'Imaginary_unit'),
    ('E', 'Energy / electric field', 'Physics variables',
     'Energy, the conserved quantity associated with time-translation '
     'symmetry. As a vector or with a subscript it is the electric field '
     'instead.', 'Energy'),
    ('m', 'Mass', 'Physics variables',
     'Mass -- both resistance to acceleration (inertial) and the source of '
     'gravity (gravitational); their exact equality is the equivalence '
     'principle underpinning general relativity.', 'Mass'),
    ('v', 'Velocity', 'Physics variables',
     'Velocity, the time derivative of position. A vector: speed plus '
     'direction.', 'Velocity'),
    ('a', 'Acceleration', 'Physics variables',
     'Acceleration, the time derivative of velocity. In cosmology, the scale '
     'factor of the expanding universe.', 'Acceleration'),
    ('F', 'Force', 'Physics variables',
     'Force, the rate of change of momentum. In thermodynamics, Helmholtz free '
     'energy; in relativity, the electromagnetic field tensor.', 'Force'),
    ('p', 'Momentum / pressure', 'Physics variables',
     'Momentum, mass times velocity, conserved because space is homogeneous. '
     'Also pressure, and in quantum mechanics the momentum operator.',
     'Momentum'),
    ('T', 'Temperature / period', 'Physics variables',
     'Absolute temperature in kelvin, a measure of energy per degree of '
     'freedom. Also the period of an oscillation, kinetic energy in Lagrangian '
     'mechanics, and the stress-energy tensor.', 'Temperature'),
    ('S', 'Entropy / action', 'Physics variables',
     'Entropy, the logarithm of the number of microstates -- a measure of how '
     'many ways a system can be arranged, and the reason time has a direction. '
     'In mechanics, the action, whose stationary points are the physical '
     'paths.', 'Entropy'),
    ('Q', 'Heat / charge', 'Physics variables',
     'Heat transferred, or electric charge, or a quality factor.', 'Heat'),
    ('W', 'Work / microstates', 'Physics variables',
     'Work done by a force, or the number of microstates in Boltzmann\'s '
     'entropy formula.', 'Work_(physics)'),
    ('L', 'Lagrangian / angular momentum', 'Physics variables',
     'The Lagrangian, kinetic minus potential energy, whose integral is the '
     'action. Also angular momentum, inductance, or a length.', 'Lagrangian_mechanics'),
    ('H', 'Hamiltonian', 'Physics variables',
     'The Hamiltonian: total energy expressed in position and momentum, and in '
     'quantum mechanics the operator generating time evolution. Also the '
     'Hubble parameter and magnetic field strength.', 'Hamiltonian_mechanics'),
    ('t', 'Time', 'Physics variables',
     'Time. In relativity it is a coordinate on equal footing with space, not '
     'a universal parameter.', 'Time'),
    ('x', 'Position / unknown', 'Physics variables',
     'A position coordinate, or the generic unknown of algebra.',
     'Variable_(mathematics)'),
    ('r', 'Radius / position vector', 'Physics variables',
     'A radial distance from an origin, or the full position vector.',
     'Polar_coordinate_system'),
    ('n', 'Count / index / refractive index', 'Physics variables',
     'A counting integer or loop index; a number density; a quantum number; or '
     'the refractive index of a medium.', 'Refractive_index'),
    ('B', 'Magnetic field', 'Physics variables',
     'The magnetic flux density. Its divergence is zero -- there are no '
     'magnetic monopoles.', 'Magnetic_field'),
    ('J', 'Current density', 'Physics variables',
     'Electric current per unit area, the source term of Ampere\'s law. Also '
     'the Jacobian matrix.', 'Current_density'),
    ('V', 'Potential / volume', 'Physics variables',
     'Electric potential in volts, or potential energy, or a volume.',
     'Electric_potential'),
    ('U', 'Internal energy / potential', 'Physics variables',
     'Internal energy in thermodynamics, or potential energy in mechanics.',
     'Internal_energy'),
    ('R', 'Resistance / Ricci scalar', 'Physics variables',
     'Electrical resistance, the gas constant, a radius, or the Ricci scalar '
     'curvature in general relativity.', 'Electrical_resistance_and_conductance'),
    ('N', 'Number', 'Physics variables',
     'A count of particles or samples; with an A subscript, Avogadro\'s '
     'number.', 'Avogadro_constant'),
    ('P', 'Probability / power / pressure', 'Physics variables',
     'A probability, a power in watts, or a pressure.', 'Probability'),
    ('A', 'Area / amplitude / vector potential', 'Physics variables',
     'An area, an oscillation amplitude, or the magnetic vector potential.',
     'Magnetic_vector_potential'),
    ('f', 'Function / frequency', 'Physics variables',
     'The default name for a function, or an ordinary frequency in hertz.',
     'Function_(mathematics)'),
]

for _l, _n, _c, _b, _s in LATIN:
    add_symbol(_l, _l, _n, _c, _b, _s)


# ---------------------------------------------------------------- concepts
#
# Longer articles for the browsable offline encyclopedia in the menu bar.

CONCEPTS = {}


def add_concept(title, category, body, slug, symbols=(), equations=()):
    CONCEPTS[title] = Concept(
        title=title, category=category, body=body.strip(),
        wiki=WIKI + slug, symbols=list(symbols), equations=list(equations))
    return CONCEPTS[title]


add_concept('Overloaded notation', 'Conventions', """
The single hardest thing about reading physics is that the alphabet ran out
long ago. One glyph carries many meanings and the reader is expected to infer
which from context alone.

The letter e is either 2.71828... or the elementary charge. Rho is mass
density, or charge density, or resistivity, or a quantum density matrix. T is
temperature, or a period, or kinetic energy, or the stress-energy tensor. None
of this is written down in the equation itself; it lives in the surrounding
prose and in the reader's training.

Code cannot work this way. A program must commit: rho_density and
rho_resistivity are different names holding different numbers. This is exactly
the gap RosettaMath is trying to close -- translating notation into
self-documenting identifiers forces the implicit context to become explicit,
which is both what makes the code runnable and what makes it teachable.
""", 'Mathematical_notation', ['\\rho', 'e', 'T', 'S'])

add_concept('Derivatives: d, partial, and dot', 'Calculus', """
Three notations for rates of change, distinguished by what is being held fixed.

The straight d is the total derivative: how a quantity changes overall,
including changes that arrive indirectly through other variables.

The curly partial is the partial derivative: how a quantity changes with
respect to one variable while every other is frozen. Fields that depend on
both space and time are almost always differentiated this way, which is why
partial symbols dominate the equations of physics.

The overdot is Newton's shorthand for a derivative with respect to time
specifically. One dot is a velocity, two dots an acceleration. It survives
because mechanics differentiates by time so constantly that a dedicated mark
pays for itself.

A prime mark is a third shorthand, usually a derivative with respect to the
function's single argument, or sometimes just "a different version of".
""", 'Derivative', ['\\partial', '\\dot'])

add_concept('The nabla operator', 'Calculus', """
Nabla is a vector whose components are partial derivative operators. It has
three uses, distinguished by what follows it.

Nabla applied to a scalar field gives the gradient: a vector pointing in the
direction of steepest increase, with length equal to that rate of increase.
Water flows down the negative gradient of the terrain.

Nabla dotted with a vector field gives the divergence: a scalar measuring how
much the field spreads out from a point. A positive divergence means a source,
a negative one a sink. Gauss's law says the divergence of the electric field is
proportional to the charge density -- charge is literally where the field comes
from.

Nabla crossed with a vector field gives the curl: a vector measuring
circulation. A paddle wheel dropped into the field spins about the curl.

Nabla dotted with itself is the Laplacian, written as nabla squared. It
compares the value of a field at a point to the average of its neighbours, and
it appears in almost every important partial differential equation.
""", 'Del', ['\\nabla', '\\partial'])

add_concept('The Laplacian', 'Calculus', """
The Laplacian, nabla squared, measures how much a field at a point differs
from the average of the surrounding points. Where it is zero the field is
perfectly smooth and equals its local average -- these are harmonic functions,
the solutions of Laplace's equation.

This one operator sorts the great partial differential equations by what it is
paired with. Set the Laplacian equal to zero and you have Laplace's equation
(static fields in empty space). Equal to a source term, Poisson's equation
(static fields with charge or mass present). Equal to a first time derivative,
the heat or diffusion equation (irreversible smoothing out). Equal to a second
time derivative, the wave equation (oscillation and propagation). Equal to a
first time derivative with an i in front, the Schrodinger equation -- which is
why quantum mechanics behaves like diffusion with a complex phase, and
produces interference instead of smoothing.
""", 'Laplace_operator', ['\\nabla', '\\partial'])

add_concept("The d'Alembert operator", 'Calculus', """
The d'Alembertian, written as a box, is what the Laplacian becomes when time
is admitted as a fourth coordinate. It is the second derivative with respect
to time, divided by the speed of light squared, minus the ordinary spatial
Laplacian.

That minus sign is the entire point. In Euclidean space every coordinate
contributes with the same sign and the Laplacian measures how a field differs
from its local average. In Minkowski spacetime the time coordinate enters with
the opposite sign, and the operator instead measures propagation. Setting it
to zero gives the wave equation; the speed of that propagation is the c
already sitting inside the operator.

Its value is that it is Lorentz invariant. An equation written with a box has
the same form for every observer, however fast they are moving, whereas an
equation written with a bare Laplacian and a separate time derivative
privileges one frame. This is why the box is the natural operator of special
relativity, electromagnetism and relativistic field theory -- the Klein-Gordon
equation is little more than the box plus a mass term.

The operator is named after Jean le Rond d'Alembert, who studied the vibrating
string. The box notation was introduced by Henri Poincare in his lectures on
electromagnetism, and by analogy with nabla the operator is sometimes called
the quabla.
""", "D'Alembert_operator", ['\\Box', '\\nabla', '\\partial', 'c'],
    ['Wave equation (box form)', 'Klein-Gordon equation'])

add_concept('Bra-ket notation', 'Quantum mechanics', """
Dirac's notation for quantum states. A ket is a column vector in Hilbert space
representing a state. A bra is its conjugate transpose, a row vector. Writing
a bra next to a ket closes the angle brackets and forms an inner product, a
complex number whose squared modulus is the probability of measuring one state
and finding the other.

The order matters and is not symmetric: swapping bra and ket conjugates the
result. An operator sandwiched between a bra and a ket gives a matrix element,
and when both are the same state, the expectation value -- the average result
of many measurements.

The notation is a piece of deliberate engineering: it makes the linear algebra
of quantum mechanics readable without ever writing out a basis.
""", 'Bra%E2%80%93ket_notation', ['\\langle', '\\rangle', '\\psi', '\\dagger'])

add_concept('Operators and observables', 'Quantum mechanics', """
In quantum mechanics every measurable quantity is represented by an operator,
usually marked with a hat, rather than by a number. Position, momentum and
energy all become operators acting on the wavefunction.

Observables must be Hermitian -- equal to their own conjugate transpose --
because Hermitian operators have real eigenvalues, and measurements yield real
numbers. The possible outcomes of a measurement are exactly the eigenvalues of
the corresponding operator, and the state collapses to the matching
eigenvector.

Operators need not commute. The order in which you apply position and momentum
matters, and the size of the discrepancy is exactly Planck's constant. That
non-commutation is the whole content of the uncertainty principle: it is a
statement about algebra, not about clumsy instruments.
""", 'Operator_(physics)', ['\\hat', '\\dagger', '\\hbar', '\\psi'])

add_concept('Tensor index notation', 'Relativity', """
A tensor is an object that transforms in a definite way under a change of
coordinates, which is what lets a physical law be written once and hold in
every reference frame.

Indices come in two flavours. Upper indices are contravariant, lower are
covariant, and the metric tensor converts between them. A repeated index, once
up and once down, is implicitly summed over -- the Einstein summation
convention, invented precisely because writing the sigma every time was
unbearable.

Greek indices usually run over all four spacetime coordinates while Latin
indices run over the three spatial ones. An expression with no free indices
left is a scalar and the same in every frame.
""", 'Tensor', ['\\Gamma', '\\mu', '\\nu', '\\eta'])

add_concept('Conservation laws and symmetry', 'Classical mechanics', """
Noether's theorem states that every continuous symmetry of a physical system
corresponds to a conserved quantity. This is arguably the deepest structural
fact in physics.

If the laws do not change over time, energy is conserved. If they do not change
from place to place, momentum is conserved. If they do not change with
orientation, angular momentum is conserved. Conservation of electric charge
comes from a symmetry of the quantum phase.

In the equations this appears as a continuity equation: the rate of change of a
density plus the divergence of its flux equals zero. Whatever leaves a region
must cross its boundary; nothing simply vanishes.
""", 'Noether%27s_theorem', ['\\partial', '\\nabla', '\\rho'])

add_concept('The action principle', 'Classical mechanics', """
Rather than pushing a system forward step by step with forces, Lagrangian
mechanics considers every conceivable path between two points and asks which
one makes the action -- the integral of the Lagrangian over time -- stationary.
That path is the one nature takes.

The Lagrangian is kinetic minus potential energy, an odd-looking combination
with no direct intuitive meaning, yet the machinery works and generalises to
fields, relativity and quantum theory. Requiring the action to be stationary
yields the Euler-Lagrange equations, which for a simple particle reproduce
Newton's second law exactly.

Feynman's path integral takes the idea literally: a quantum particle explores
every path, each contributing a phase, and the classical path is where those
phases reinforce.
""", 'Principle_of_least_action', ['L', 'S', '\\int', '\\partial'])

add_concept('Entropy', 'Thermodynamics', """
Entropy counts. Boltzmann's formula sets it to the logarithm of the number of
microscopic arrangements consistent with what you can observe macroscopically.
There are overwhelmingly more disordered arrangements than ordered ones, so
systems left alone drift toward disorder -- not by any force, but by counting.

The logarithm is there so entropy adds when systems are combined, since the
number of joint arrangements multiplies.

Shannon later derived the same expression for information, defining the entropy
of a probability distribution as the average surprise of its outcomes. The
coincidence is not superficial: both quantities measure how much you do not
know, and the connection runs through Landauer's principle to the thermodynamic
cost of erasing a bit and on to black hole thermodynamics.
""", 'Entropy', ['S', 'k', '\\log', '\\sum'])

add_concept('Fourier analysis', 'Mathematics', """
Any reasonable function can be written as a sum of sines and cosines. The
Fourier transform performs that decomposition, converting a function of time
into a function of frequency, or a function of position into one of wavenumber.

Its power is that differentiation becomes multiplication. A differential
equation in ordinary space turns into an algebraic equation in Fourier space,
gets solved trivially, and is transformed back. Most analytical solutions of
wave and diffusion equations are obtained this way.

The transform also enforces a trade-off: a signal sharply localised in time
must be spread out in frequency. In quantum mechanics, where momentum is the
Fourier conjugate of position, that mathematical fact is the uncertainty
principle.
""", 'Fourier_transform', ['\\int', '\\exp', 'i', '\\omega'])

add_concept('Dimensional analysis', 'Conventions', """
Every term in a valid equation must carry the same physical dimensions. You may
add metres to metres but never metres to seconds, and the argument of an
exponential, logarithm or sine must be dimensionless.

This is the cheapest and most effective check on an equation or a piece of
code. It catches missing factors, wrong constants and misremembered formulas
instantly, and it often lets you reconstruct the form of an unknown law up to a
dimensionless constant just by asking what combination of the available
quantities gives the right units.

It is also why the natural-unit conventions exist: setting c and hbar to one
removes conversion factors, at the cost of having to restore them by dimensional
analysis before comparing with an experiment.
""", 'Dimensional_analysis', ['c', '\\hbar', 'G'])

add_concept('Natural units', 'Conventions', """
Theorists frequently set the speed of light, the reduced Planck constant and
sometimes Boltzmann's and Newton's constants equal to one. The equations get
much shorter -- mass, energy and inverse length all become the same kind of
quantity -- and the structure becomes easier to see.

The cost is that a formula in natural units cannot be evaluated numerically
until the constants are put back. This is a recurring source of confusion when
moving from a paper to a program, because the published equation is often not
the one you can actually run.

RosettaMath's approach is the opposite: resolve the symbols to real values from
scipy.constants so that the equation as written is the equation that executes.
""", 'Natural_units', ['c', '\\hbar', 'G', 'k'])

add_concept('Piecewise definitions', 'Mathematics', """
A cases environment defines a function by branches: each row gives a value and
the condition under which it applies. Read top to bottom, first match wins,
with "otherwise" as the catch-all.

This maps almost perfectly onto an if/elif/else chain, which is why RosettaMath
handles it. The one mathematical convention worth noting is that the branches
are expected to be exhaustive and mutually exclusive -- a function undefined
somewhere is a bug in the maths, just as a missing else can be a bug in code.
""", 'Piecewise', [])

add_concept('Summation as a loop', 'Mathematics', """
A capital sigma is a for loop with an accumulator. The index and its starting
value sit below the sigma, the final value above, and the expression to the
right is the loop body.

The only real trap is the bounds. Mathematical sums are inclusive of both
limits, whereas Python's range excludes the upper one -- so a sum from 1 to n
becomes range(1, n + 1). Off-by-one errors introduced at exactly this point are
one of the most common bugs when transcribing a paper into code, and it is why
RosettaMath's for2py deliberately adds the +1 when translating a "for i = a to
b" loop.
""", 'Summation', ['\\sum', '\\prod'])

add_concept('Complex numbers in physics', 'Mathematics', """
Complex numbers package an amplitude and a phase into one object, and Euler's
formula makes rotation and oscillation the same operation. That is why they
appear wherever waves do, even in classical problems where the physical answer
is purely real and the imaginary part is discarded at the end.

Quantum mechanics is different. There the wavefunction is genuinely complex,
the i in the Schrodinger equation cannot be removed, and the relative phase
between components is physically meaningful -- it is what produces
interference. The measurable prediction is the squared modulus, which is real,
but the phase that got you there is not decoration.
""", 'Complex_number', ['i', '\\exp', '\\Re', '\\Im'])

add_concept('Aperiodic tilings and the domino problem', 'Tilings', """
A set of tiles is aperiodic when it tiles the plane and every tiling it admits
lacks a translational period. That such a set exists at all was not obvious.
Wang conjectured in 1961 that any set of tiles able to cover the plane could
cover it periodically, and observed that if he were right, the question of
whether a given set tiles at all would be decidable: search outward from a
patch, and either you close up a period or you jam.

Berger disproved the conjecture in 1966 by constructing an aperiodic set, and
in doing so proved the domino problem undecidable -- a set of Wang tiles can
encode the tape of a Turing machine, so asking whether it tiles the plane is
asking whether the machine runs forever. Berger's set had over twenty thousand
tiles; Jeandel and Rao brought the minimum to eleven in 2015, and proved that
eleven cannot be beaten.

This is worth stating in a library of equations precisely because it cannot be
one. Everything else here is a relation between quantities that some procedure
could in principle evaluate. The domino problem is a statement about tiles that
is perfectly precise, entirely finite to write down, and provably beyond any
procedure at all. It marks the edge of what a knowledge base of this kind can
promise: the Lean conjectures this module generates ask whether a statement is
well formed, which is decidable, and never whether it is true, which in general
is not.

The Penrose tilings are the famous aperiodic set, and their obstruction is
arithmetic rather than computational: fat and thin rhombs occur in the ratio of
the golden ratio, and a periodic tiling would force that ratio to be rational.

How few tiles can an aperiodic set have? Penrose got it to two in the 1970s and
there it stayed for fifty years. In 2023 Smith, Myers, Kaplan and
Goodman-Strauss found a single tile that tiles the plane and never
periodically, settling a question that had been open since Wang asked it: the
hat, and then the spectre, which needs no reflections.

The arithmetic came out different from Penrose's, and then came out the same
again, which is worth following. The hat is generated by a substitution on four
metatiles whose matrix has characteristic polynomial
(lambda-1)(lambda+1)(lambda^2-7lambda+1), so its inflation factor is the larger
root of that quadratic -- which is phi^4, the golden ratio again, four powers
up. Unreflected hats outnumber reflected ones by exactly that factor.

The spectre is a different substitution: nine species, characteristic
polynomial lambda^5 (lambda-1) (lambda+1) (lambda^2-8lambda+1), inflation
factor 4 + sqrt15. The two polynomials differ in a single coefficient, seven
against eight, and that one coefficient is the difference between sqrt5 and
sqrt15.

It is easy to write these two down as though they contradicted each other, and
this article did in its first draft. They do not: they are two tilings and two
substitutions, and the entries in the library now say which matrix each number
was computed from. That is what the `source` field is for.
""", 'Wang_tile', [], ['Golden ratio', 'Penrose tile ratio',
                       'Inflation quadratic', 'Spectre inflation quadratic',
                       'Spectre inflation factor', 'Hat inflation quadratic',
                       'Hat constant as a golden power'])

add_concept('Area as an action', 'Extremal geometry', """
A soap film spanning a wire loop has no memory, no dynamics and nothing to
compute with, and it finds a minimal surface anyway. The reason is that surface
tension makes energy proportional to area, so the film's equilibrium is
whatever shape makes area stationary. Setting the first variation of the area
integral to zero gives the minimal surface equation, and the condition it
encodes is that mean curvature vanishes everywhere.

The same sentence, with two words changed, is the founding statement of string
theory. A relativistic point particle extremises the length of its worldline. A
relativistic string extremises the area of the sheet it sweeps out, and the
Nambu-Goto action is that area multiplied by a tension. Nothing has been added:
the variational problem is the one Plateau posed about films, transplanted from
Euclidean space to Minkowski spacetime, where the signature puts a minus sign
under the square root.

What this group of entries is really about is the price of a constraint. Hold a
boundary fixed and area cannot go below some value. Demand a segment in every
direction and measure can be pushed to zero but dimension cannot. Close a
surface up and total curvature is pinned to a whole number by Gauss-Bonnet, no
matter how the surface is bent. In each case a geometric demand is made and the
answer comes back as a number that will not move.
""", 'Plateau%27s_problem', [], ['Area functional', 'Minimal surface equation',
                                 'Minimal surface condition',
                                 'Nambu-Goto action', 'Gauss-Bonnet theorem'])


# ---------------------------------------------------------------- equations
#
# A signature library.  Each entry lists the features that MUST be present for
# the equation to be a candidate, plus features that raise confidence.  The
# feature vocabulary is produced by extract_features() below: bare symbol names
# ('psi', 'hbar', 'E'), and structural tags prefixed with 'S:' ('S:frac',
# 'S:nabla2', 'S:sup2').
#
# An entry may also carry a `source`, and the reason it exists is worth
# recording.  Two of this project's own repositories give different inflation
# factors for the aperiodic monotile -- phi^4 from a four-metatile substitution
# and 4 + sqrt15 from a nine-species one -- and both are right, because they
# are different substitutions.  Written without saying which matrix each came
# from, the two entries read as a contradiction, and the first draft of the
# tilings group below did exactly that.
#
# So `source` names the thing a number was checked against when that thing is
# not the Wikipedia article in `slug`: a repository and the function inside it.
# The rule is narrow on purpose. `slug` is where a reader goes to learn what
# the equation means; `source` is where the specific value in this entry was
# computed, which is a different question and, for anything derived rather than
# quoted, the more important one.

def equation(**fields):
    """One entry in the signature library, as a graph node."""
    return Equation(**fields)


EQUATIONS = [
    equation(name='Mass-energy equivalence', field='Relativity',
         latex=r'E = m c^2', slug='Mass%E2%80%93energy_equivalence',
         must=['E', 'm', 'c', 'S:sup2'], nice=[],
         blurb='Mass and energy are the same thing in different units, and the '
               'conversion factor is enormous. The equation does not say mass '
               'turns into energy; it says a system with energy has inertia, '
               'and a body at rest already carries energy m*c^2.'),
    equation(name='Newton\'s second law', field='Classical mechanics',
         latex=r'F = m a', slug='Newton%27s_laws_of_motion',
         must=['F', 'm', 'a'], nice=[],
         blurb='Force equals mass times acceleration -- more precisely, force '
               'is the rate of change of momentum. It is the definition that '
               'makes mass measurable and turns mechanics into a solvable '
               'differential equation.'),
    equation(name='Newton\'s law of gravitation', field='Classical mechanics',
         latex=r'F = G \frac{m_1 m_2}{r^2}', slug='Newton%27s_law_of_universal_gravitation',
         must=['F', 'G', 'm', 'r', 'S:frac'], nice=['S:sup2', 'S:sub'],
         blurb='An inverse-square attraction between any two masses. The '
               'inverse square is not arbitrary: it is what a flux spreading '
               'over the surface of a sphere must do in three dimensions.'),
    equation(name='Coulomb\'s law', field='Electromagnetism',
         latex=r'F = \frac{1}{4 \pi \epsilon_0} \frac{q_1 q_2}{r^2}',
         slug='Coulomb%27s_law',
         must=['F', 'epsilon', 'r', 'S:frac', 'pi'], nice=['q', 'S:sup2'],
         blurb='The electrostatic force between two charges. Structurally '
               'identical to Newtonian gravity, but roughly 10^36 times '
               'stronger and able to take either sign -- which is why bulk '
               'matter is electrically neutral and gravity wins at large '
               'scales.'),
    equation(name='Schrodinger equation (time-dependent)', field='Quantum mechanics',
         latex=r'i \hbar \frac{\partial \Psi}{\partial t} = \hat{H} \Psi',
         slug='Schr%C3%B6dinger_equation',
         must=['i', 'hbar', 'partial', 'Psi'], nice=['H', 'S:frac', 't', 'S:hat'],
         blurb='The equation of motion for a quantum state. The i on the left '
               'makes it a wave equation rather than a diffusion equation: '
               'instead of smoothing out, solutions rotate in phase and '
               'interfere. It is first order in time, so the present state '
               'determines the entire future.'),
    equation(name='Schrodinger equation (time-independent)', field='Quantum mechanics',
         latex=r'-\frac{\hbar^2}{2m} \nabla^2 \psi + V \psi = E \psi',
         slug='Schr%C3%B6dinger_equation',
         must=['hbar', 'psi', 'E', 'S:nabla2'], nice=['m', 'V', 'S:frac', 'S:sup2'],
         blurb='An eigenvalue problem: only certain energies admit '
               'well-behaved solutions, and that discreteness is where '
               'quantisation comes from. Atomic energy levels are the '
               'eigenvalues of this equation for a Coulomb potential.'),
    equation(name='Klein-Gordon equation', field='Quantum field theory',
         latex=r'\left( \Box + \frac{m^2 c^2}{\hbar^2} \right) \phi = 0',
         slug='Klein%E2%80%93Gordon_equation',
         must=['phi', 'm', 'hbar'],
         nice=['c', 'Box', 'S:nabla2', 'partial', 'S:sup2', 'S:frac'],
         blurb='The relativistic wave equation for a spinless field. It is '
               'second order in time, unlike the Schrodinger equation, which '
               'is what makes it Lorentz invariant -- and also what forced the '
               'reinterpretation of its negative-energy solutions as '
               'antiparticles.'),
    equation(name='Dirac equation', field='Quantum field theory',
         latex=r'( i \gamma^\mu \partial_\mu - m ) \psi = 0',
         slug='Dirac_equation',
         must=['i', 'gamma', 'partial', 'psi', 'm'], nice=['mu', 'S:sup', 'S:sub'],
         blurb='The relativistic equation for spin-1/2 particles. Dirac '
               'insisted on first order in time, which required the '
               'coefficients to be matrices; spin and antimatter both fell out '
               'of the algebra rather than being put in by hand.'),
    equation(name="d'Alembert operator", field='Relativity',
         latex=r'\Box = \frac{1}{c^2} \frac{\partial^2}{\partial t^2} - \nabla^2',
         slug="D'Alembert_operator",
         must=['Box', 'S:nabla2', 'partial'], nice=['c', 'S:frac', 'S:sup2', 't'],
         blurb='The definition of the box operator: a second time derivative '
               'against a spatial Laplacian, with the relative minus sign that '
               'is the whole difference between Minkowski spacetime and '
               'Euclidean space. Written out this way it is clear why the '
               'operator is Lorentz invariant and the Laplacian alone is not.'),
    equation(name='Wave equation (box form)', field='Waves',
         latex=r'\Box \psi = 0', slug='Wave_equation',
         must=['Box'], nice=['psi', 'phi', 'A', 'u', 'F'],
         blurb='The wave equation written with the d\'Alembertian. Compressing '
               'the time and space derivatives into one symbol makes the '
               'relativistic content visible at a glance: the equation has the '
               'same form in every inertial frame, and its solutions propagate '
               'at exactly the speed c buried inside the operator.'),
    equation(name='Wave equation', field='Waves',
         latex=r'\frac{\partial^2 u}{\partial t^2} = c^2 \nabla^2 u',
         slug='Wave_equation',
         must=['partial', 'c', 'S:nabla2'], nice=['S:frac', 't', 'S:sup2', 'u'],
         blurb='A second time derivative equal to a Laplacian: disturbances '
               'propagate at fixed speed c without changing shape. Sound, '
               'light, and a plucked string all obey it, and the constant c is '
               'set by the medium.'),
    equation(name='Heat / diffusion equation', field='Thermodynamics',
         latex=r'\frac{\partial u}{\partial t} = \alpha \nabla^2 u',
         slug='Heat_equation',
         must=['partial', 'S:nabla2'], nice=['alpha', 'S:frac', 't', 'u', 'D'],
         blurb='A first time derivative equal to a Laplacian: gradients smooth '
               'out irreversibly. Unlike the wave equation it has a preferred '
               'direction of time -- you cannot run it backwards stably, which '
               'is the arrow of time appearing in a differential equation.'),
    equation(name='Laplace\'s equation', field='Fields',
         latex=r'\nabla^2 \phi = 0', slug='Laplace%27s_equation',
         must=['S:nabla2'], nice=['phi', 'Phi', 'u'],
         blurb='The Laplacian vanishes: the field everywhere equals the '
               'average of its neighbours. Such harmonic functions describe '
               'static fields in empty space, and they have no local maxima or '
               'minima in the interior -- extremes live on the boundary.'),
    equation(name='Poisson\'s equation', field='Fields',
         latex=r'\nabla^2 \phi = \rho', slug='Poisson%27s_equation',
         must=['S:nabla2', 'rho'], nice=['phi', 'Phi', 'epsilon', 'S:frac'],
         blurb='Laplace\'s equation with a source. The density on the right '
               'tells the potential how to curve; solving it recovers the '
               'gravitational or electrostatic potential produced by a given '
               'distribution of mass or charge.'),
    equation(name='Helmholtz equation', field='Waves',
         latex=r'\nabla^2 A + k^2 A = 0', slug='Helmholtz_equation',
         must=['S:nabla2', 'k'], nice=['A', 'S:sup2'],
         blurb='What the wave equation becomes after separating out a single '
               'frequency. k is the wavenumber; the equation governs standing '
               'waves, waveguides and optical modes.'),
    equation(name='Gauss\'s law', field='Electromagnetism',
         latex=r'\nabla \cdot E = \frac{\rho}{\epsilon_0}', slug='Gauss%27s_law',
         must=['nabla', 'rho', 'E'], nice=['epsilon', 'S:frac', 'S:cdot'],
         blurb='The divergence of the electric field is the charge density: '
               'field lines begin and end on charge. Integrated over a closed '
               'surface it says the flux out equals the charge enclosed, '
               'regardless of how that charge is arranged.'),
    equation(name='Gauss\'s law for magnetism', field='Electromagnetism',
         latex=r'\nabla \cdot B = 0', slug='Gauss%27s_law_for_magnetism',
         must=['nabla', 'B'], nice=['S:cdot'],
         blurb='The magnetic field has zero divergence: there are no magnetic '
               'monopoles. Every field line closes on itself, which is why '
               'cutting a magnet in half gives two magnets rather than a north '
               'and a south pole.'),
    equation(name='Faraday\'s law of induction', field='Electromagnetism',
         latex=r'\nabla \times E = -\frac{\partial B}{\partial t}',
         slug='Faraday%27s_law_of_induction',
         must=['nabla', 'E', 'B', 'partial'], nice=['S:times', 'S:frac', 't'],
         blurb='A changing magnetic field creates a circulating electric '
               'field. This is the principle behind every generator and '
               'transformer, and the minus sign (Lenz\'s law) is what keeps '
               'the induced effect opposing the change that caused it.'),
    equation(name='Ampere-Maxwell law', field='Electromagnetism',
         latex=r'\nabla \times B = \mu_0 J + \mu_0 \epsilon_0 \frac{\partial E}{\partial t}',
         slug='Amp%C3%A8re%27s_circuital_law',
         must=['nabla', 'B', 'mu'], nice=['J', 'epsilon', 'partial', 'E', 'S:times'],
         blurb='Currents and changing electric fields both create circulating '
               'magnetic fields. Maxwell\'s addition of the second term is '
               'what made the equations self-consistent and predicted '
               'electromagnetic waves travelling at the speed of light.'),
    equation(name='Continuity equation', field='Conservation laws',
         latex=r'\frac{\partial \rho}{\partial t} + \nabla \cdot J = 0',
         slug='Continuity_equation',
         must=['partial', 'rho', 'nabla'], nice=['J', 't', 'S:frac', 'S:cdot'],
         blurb='The local statement of a conservation law: whatever the '
               'density loses, the flux must carry across the boundary. The '
               'same form governs mass, charge, energy and probability.'),
    equation(name='Navier-Stokes equation', field='Fluid dynamics',
         latex=r'\rho \left( \frac{\partial v}{\partial t} + v \cdot \nabla v \right) = -\nabla p + \eta \nabla^2 v',
         slug='Navier%E2%80%93Stokes_equations',
         must=['rho', 'partial', 'nabla', 'v'], nice=['eta', 'p', 'mu', 'S:nabla2'],
         blurb='Newton\'s second law for a fluid. The nonlinear term in which '
               'the velocity advects itself is what produces turbulence, and '
               'why proving that smooth solutions always exist is an open '
               'Millennium Prize problem.'),
    equation(name='Euler-Lagrange equation', field='Classical mechanics',
         latex=r'\frac{d}{dt} \frac{\partial L}{\partial \dot{q}} - \frac{\partial L}{\partial q} = 0',
         slug='Euler%E2%80%93Lagrange_equation',
         must=['partial', 'L'], nice=['q', 'S:dot', 'S:frac', 't'],
         blurb='The condition for the action to be stationary. Feed it a '
               'Lagrangian and it hands back the equations of motion; for a '
               'particle in a potential it reduces to F = ma, but it works '
               'just as well in awkward coordinates where forces are painful.'),
    equation(name='Boltzmann entropy', field='Thermodynamics',
         latex=r'S = k_B \log W', slug='Boltzmann%27s_entropy_formula',
         must=['S', 'k'], nice=['log', 'W', 'ln', 'S:sub'],
         blurb='Entropy is the logarithm of the number of microstates. This '
               'formula, carved on Boltzmann\'s gravestone, is the bridge '
               'between the microscopic world of atoms and the macroscopic '
               'laws of thermodynamics.'),
    equation(name='Shannon entropy', field='Information theory',
         latex=r'H = -\sum p_i \log p_i', slug='Entropy_(information_theory)',
         must=['S:sum', 'p'], nice=['H', 'log', 'S:sub', 'i'],
         blurb='The average information content of a distribution, measured in '
               'bits when the logarithm is base two. It is Boltzmann\'s formula '
               'again in a different guise, and it sets the hard limit on how '
               'far data can be compressed.'),
    equation(name='Planck relation', field='Quantum mechanics',
         latex=r'E = h \nu', slug='Planck_relation',
         must=['E', 'h'], nice=['nu', 'omega', 'hbar', 'f'],
         blurb='A photon\'s energy is proportional to its frequency, with '
               'Planck\'s constant as the conversion. This is the quantum '
               'hypothesis in its smallest form: light comes in discrete '
               'packets, which is why the photoelectric effect depends on '
               'colour rather than brightness.'),
    equation(name='de Broglie relation', field='Quantum mechanics',
         latex=r'\lambda = \frac{h}{p}', slug='Matter_wave',
         must=['lambda', 'h', 'p'], nice=['S:frac'],
         blurb='Every particle has a wavelength inversely proportional to its '
               'momentum. For everyday objects it is unmeasurably small; for '
               'electrons it is atom-sized, which is why they diffract and why '
               'electron microscopes work.'),
    equation(name='Heisenberg uncertainty principle', field='Quantum mechanics',
         latex=r'\Delta x \Delta p \geq \frac{\hbar}{2}',
         slug='Uncertainty_principle',
         must=['Delta', 'hbar'], nice=['x', 'p', 'geq', 'S:frac'],
         blurb='Position and momentum cannot both be sharply defined. This is '
               'not a limit on instruments but a property of Fourier conjugate '
               'pairs: a narrow wave packet in space is necessarily broad in '
               'wavenumber.'),
    equation(name='Einstein field equations', field='General relativity',
         latex=r'G_{\mu\nu} + \Lambda g_{\mu\nu} = \frac{8 \pi G}{c^4} T_{\mu\nu}',
         slug='Einstein_field_equations',
         must=['mu', 'nu', 'G', 'T'], nice=['Lambda', 'pi', 'c', 'g', 'S:frac', 'S:sub'],
         blurb='Curvature on the left, matter and energy on the right: '
               'spacetime tells matter how to move, matter tells spacetime how '
               'to curve. Ten coupled nonlinear equations, which is why exact '
               'solutions are rare and precious.'),
    equation(name='Schwarzschild radius', field='General relativity',
         latex=r'r_s = \frac{2 G M}{c^2}', slug='Schwarzschild_radius',
         must=['G', 'c', 'r'], nice=['M', 'm', 'S:frac', 'S:sup2', 'S:sub'],
         blurb='The radius at which the escape velocity reaches the speed of '
               'light -- the event horizon of a non-rotating black hole. For '
               'the Sun it is about three kilometres, for the Earth about nine '
               'millimetres.'),
    equation(name='Bekenstein-Hawking entropy', field='General relativity',
         latex=r'S = \frac{k_B c^3 A}{4 G \hbar}', slug='Black_hole_thermodynamics',
         must=['S', 'G', 'hbar', 'c'], nice=['k', 'A', 'S:frac', 'S:sup'],
         blurb='A black hole\'s entropy is proportional to the area of its '
               'horizon, not its volume. That every fundamental constant '
               'appears at once -- quantum, relativistic, gravitational and '
               'thermodynamic -- is why this formula is treated as a clue to '
               'quantum gravity, and it is the origin of the holographic '
               'principle.'),
    equation(name='Lorentz factor', field='Relativity',
         latex=r'\gamma = \frac{1}{\sqrt{1 - \frac{v^2}{c^2}}}',
         slug='Lorentz_factor',
         must=['gamma', 'v', 'c', 'S:sqrt'], nice=['S:frac', 'S:sup2'],
         blurb='The factor by which time dilates and length contracts. It is '
               'essentially one at everyday speeds and diverges as v '
               'approaches c, which is why massive objects cannot reach the '
               'speed of light.'),
    equation(name='Ideal gas law', field='Thermodynamics',
         latex=r'P V = n R T', slug='Ideal_gas_law',
         must=['V', 'T', 'R'], nice=['P', 'n', 'p', 'N', 'k'],
         blurb='Pressure times volume equals amount times temperature. An '
               'excellent approximation whenever the molecules are far enough '
               'apart to ignore their size and mutual attraction.'),
    equation(name='Stefan-Boltzmann law', field='Thermodynamics',
         latex=r'j = \sigma T^4', slug='Stefan%E2%80%93Boltzmann_law',
         must=['sigma', 'T'], nice=['S:sup', 'j', 'P', 'A'],
         blurb='Radiated power scales as the fourth power of temperature. The '
               'steepness is why a modest rise in a star\'s surface '
               'temperature makes it dramatically brighter.'),
    equation(name='Plasma frequency', field='Plasma physics',
         latex=r'\omega_p = \sqrt{\frac{n e^2}{\epsilon_0 m_e}}',
         slug='Plasma_oscillation',
         must=['omega', 'n', 'e', 'epsilon', 'S:sqrt'], nice=['m', 'S:frac', 'S:sub'],
         blurb='The natural oscillation frequency of electrons in a plasma. '
               'Waves below it cannot propagate and are reflected -- which is '
               'how the ionosphere bounces radio signals around the curve of '
               'the Earth.'),
    equation(name='Debye length', field='Plasma physics',
         latex=r'\lambda_D = \sqrt{\frac{\epsilon_0 k_B T}{n e^2}}',
         slug='Debye_length',
         must=['lambda', 'epsilon', 'T', 'n', 'e'], nice=['k', 'S:sqrt', 'S:frac'],
         blurb='The distance over which a charge is screened out by the '
               'surrounding plasma. Beyond it the plasma looks neutral, and a '
               'system is only genuinely a plasma if it is much larger than '
               'this length.'),
    equation(name='Vlasov equation', field='Plasma physics',
         latex=r'\frac{\partial f}{\partial t} + v \cdot \nabla f + \frac{F}{m} \cdot \nabla_v f = 0',
         slug='Vlasov_equation',
         must=['partial', 'f', 'nabla', 'v'], nice=['F', 'm', 't', 'S:frac', 'S:cdot'],
         blurb='Tracks the distribution of particles in position-velocity '
               'space for a collisionless plasma. It is a continuity equation '
               'in six dimensions, with the electromagnetic force supplied '
               'self-consistently by the particles themselves.'),
    equation(name='Friedmann equation', field='Cosmology',
         latex=r'H^2 = \frac{8 \pi G}{3} \rho - \frac{k c^2}{a^2} + \frac{\Lambda c^2}{3}',
         slug='Friedmann_equations',
         must=['H', 'G', 'rho'], nice=['pi', 'Lambda', 'a', 'c', 'k', 'S:frac', 'S:sup2'],
         blurb='Governs the expansion of a homogeneous universe. The competing '
               'terms are matter, spatial curvature and the cosmological '
               'constant, and which one dominates decides whether the universe '
               'expands forever.'),
    equation(name='Euler\'s identity', field='Mathematics',
         latex=r'e^{i \pi} + 1 = 0', slug='Euler%27s_identity',
         must=['e', 'i', 'pi', 'S:sup'], nice=[],
         blurb='Rotating by half a turn in the complex plane lands you at -1. '
               'It links the additive identity, the multiplicative identity, '
               'and the three constants e, i and pi in one line.'),
    equation(name='Pythagorean theorem', field='Mathematics',
         latex=r'a^2 + b^2 = c^2', slug='Pythagorean_theorem',
         must=['a', 'b', 'c', 'S:sup2'], nice=[],
         blurb='In a right triangle the squares on the legs sum to the square '
               'on the hypotenuse. Generalised, it is the definition of '
               'distance in Euclidean space -- and changing the signs gives '
               'the spacetime interval of relativity.'),
    equation(name='Quadratic formula', field='Mathematics',
         latex=r'x = \frac{-b \pm \sqrt{b^2 - 4ac}}{2a}',
         slug='Quadratic_formula',
         must=['x', 'S:sqrt', 'S:frac', 'pm'], nice=['a', 'b', 'c', 'S:sup2'],
         blurb='The roots of a quadratic. The discriminant under the root '
               'decides everything: positive gives two real roots, zero a '
               'repeated one, negative a complex conjugate pair.'),
    equation(name='Bayes\' theorem', field='Probability',
         latex=r'P(A \mid B) = \frac{P(B \mid A) P(A)}{P(B)}',
         slug='Bayes%27_theorem',
         must=['P', 'S:frac'], nice=['A', 'B', 'mid'],
         blurb='How to update a belief when evidence arrives. The prior is '
               'multiplied by how well the hypothesis predicted the data and '
               'renormalised -- the whole of Bayesian inference is repeated '
               'application of this one line.'),
    equation(name='Normal distribution', field='Probability',
         latex=r'f(x) = \frac{1}{\sigma \sqrt{2\pi}} e^{-\frac{(x-\mu)^2}{2\sigma^2}}',
         slug='Normal_distribution',
         must=['sigma', 'mu', 'pi', 'S:exp_or_e'], nice=['x', 'S:frac', 'S:sqrt', 'S:sup2'],
         blurb='The bell curve. The central limit theorem explains its '
               'ubiquity: add up enough independent small effects and the '
               'total is normally distributed almost regardless of what you '
               'started with.'),
    equation(name='Kullback-Leibler divergence', field='Information theory',
         latex=r'D(P \parallel Q) = \sum P(x) \log \frac{P(x)}{Q(x)}',
         slug='Kullback%E2%80%93Leibler_divergence',
         must=['S:sum', 'log', 'P'], nice=['Q', 'D', 'S:frac', 'x'],
         blurb='The relative entropy between two distributions: the extra '
               'information cost of using the wrong model. It is never '
               'negative, zero only when the distributions agree, and is not '
               'symmetric -- so it is a divergence, not a distance.'),
    equation(name='Geometric series', field='Mathematics',
         latex=r'\sum_{n=0}^{\infty} r^n = \frac{1}{1-r}',
         slug='Geometric_series',
         must=['S:sum', 'r', 'infty'], nice=['n', 'S:frac', 'S:sup', 'S:sub'],
         blurb='A sum with a constant ratio between terms converges whenever '
               'that ratio is less than one in magnitude. It is the workhorse '
               'behind perturbation expansions and the resolvent of an '
               'operator.'),
    equation(name='Kinetic energy', field='Classical mechanics',
             latex=r'E_k = \frac{1}{2} m v^2', slug='Kinetic_energy',
             must=['E', 'm', 'v', 'S:frac'], nice=['S:sup2'],
             blurb='The energy a body has by moving. The half and the square '
                   'are not decoration: the square is what makes kinetic '
                   'energy add as work does, and the half is what falls out of '
                   'integrating momentum with respect to velocity.'),
    equation(name='Momentum', field='Classical mechanics',
             latex=r'p = m v', slug='Momentum',
             must=['p', 'm', 'v'], nice=[],
             blurb='Mass times velocity -- the quantity that is conserved when '
                   'nothing external pushes, which is why it, rather than '
                   'velocity, is what appears in the laws.'),
    equation(name='Work done by a force', field='Classical mechanics',
             latex=r'W = F d', slug='Work_(physics)',
             must=['W', 'F', 'd'], nice=[],
             blurb='Force times the distance moved along it. This is the '
                   'bridge between the force laws and the energy laws: it is '
                   'how a push becomes a change in energy.'),
    equation(name='Gravitational potential energy', field='Classical mechanics',
             latex=r'U = m g h', slug='Gravitational_energy',
             must=['U', 'm', 'g', 'h'], nice=[],
             blurb='The energy stored by lifting something in a uniform field. '
                   'The uniform g is an approximation to the inverse-square '
                   'law that is excellent near a surface and useless far from '
                   'one.'),
    equation(name='Surface gravity', field='Classical mechanics',
             latex=r'g = \frac{G M}{r^2}', slug='Surface_gravity',
             must=['g', 'G', 'M', 'r', 'S:frac'], nice=['S:sup2'],
             blurb='What the inverse-square law becomes when one of the two '
                   'masses is a planet: the acceleration it imposes, '
                   'independent of what is falling. That independence is the '
                   'equivalence principle in its oldest form.'),
    equation(name='Hooke\'s law', field='Classical mechanics',
             latex=r'F = -k x', slug='Hooke%27s_law',
             must=['F', 'k', 'x'], nice=[],
             blurb='A restoring force proportional to displacement. Almost '
                   'nothing obeys it exactly, and almost everything obeys it '
                   'near equilibrium, because it is the first term of any '
                   'potential expanded about a minimum.'),
    equation(name='Angular frequency', field='Waves',
             latex=r'\omega = 2 \pi f', slug='Angular_frequency',
             must=['omega', 'pi', 'f'], nice=[],
             blurb='Frequency in radians per second rather than cycles per '
                   'second. The factor of two pi is the single commonest '
                   'source of a lost constant when moving between a formula '
                   'and its implementation.'),
    equation(name='Wave speed', field='Waves',
             latex=r'v = f \lambda', slug='Wavelength',
             must=['v', 'f', 'lambda'], nice=[],
             blurb='Frequency times wavelength. It holds for any wave at all, '
                   'which is why it links the optical, acoustic and quantum '
                   'descriptions of the same travelling disturbance.'),
    equation(name='Ohm\'s law', field='Electromagnetism',
             latex=r'V = I R', slug='Ohm%27s_law',
             must=['V', 'I', 'R'], nice=[],
             blurb='Voltage equals current times resistance. It is a property '
                   'of certain materials rather than a law of nature, which is '
                   'why semiconductors ignore it.'),
    equation(name='Electrical power', field='Electromagnetism',
             latex=r'P = V I', slug='Electric_power',
             must=['P', 'V', 'I'], nice=[],
             blurb='Voltage times current. Combined with Ohm\'s law it gives '
                   'the two forms every electronics text uses next, P = I^2 R '
                   'and P = V^2 / R.'),
    equation(name='Capacitor charge', field='Electromagnetism',
             latex=r'Q = C V', slug='Capacitance',
             must=['Q', 'C', 'V'], nice=[],
             blurb='Charge stored is capacitance times voltage. The definition '
                   'of capacitance, really, dressed as a result.'),
    equation(name='Density', field='Fluid dynamics',
             latex=r'\rho = \frac{m}{V}', slug='Density',
             must=['rho', 'm', 'V', 'S:frac'], nice=[],
             blurb='Mass per unit volume. Worth stating explicitly because rho '
                   'is among the most overloaded letters in physics, and this '
                   'is the reading the others are named after.'),
    equation(name='Hydrostatic pressure', field='Fluid dynamics',
             latex=r'P = \rho g h', slug='Hydrostatic_equilibrium',
             must=['P', 'rho', 'g', 'h'], nice=[],
             blurb='The pressure at a depth is the weight of the column above '
                   'it. It does not depend on the shape of the container, '
                   'which surprised people for a long time.'),
    equation(name='Thermal energy', field='Thermodynamics',
             latex=r'E = k_B T', slug='Thermal_energy',
             must=['E', 'k', 'T'], nice=['B', 'S:sub'],
             blurb='The energy scale a temperature corresponds to, per degree '
                   'of freedom. This is what the Boltzmann constant is for: it '
                   'is a unit conversion between kelvin and joules, and in '
                   'natural units it is simply one.'),
    equation(name='Heat capacity', field='Thermodynamics',
             latex=r'Q = m c_p \Delta T', slug='Heat_capacity',
             must=['Q', 'm', 'T'], nice=['Delta', 'S:sub'],
             blurb='How much heat a temperature change costs. The specific '
                   'heat c_p is where the material comes in, and it is one '
                   'more meaning for an already overloaded c.'),
    equation(name='Compton wavelength', field='Quantum mechanics',
             latex=r'\lambda_C = \frac{h}{m c}', slug='Compton_wavelength',
             must=['lambda', 'h', 'm', 'c', 'S:frac'], nice=['S:sub'],
             blurb='The wavelength of a photon whose energy equals a '
                   'particle\'s rest energy -- the scale at which quantum '
                   'mechanics and relativity have to be used together, and '
                   'below which the idea of a single particle stops working.'),
    equation(name='Planck length', field='Cosmology',
             latex=r'\ell_P = \sqrt{\frac{\hbar G}{c^3}}',
             slug='Planck_length',
             must=['hbar', 'G', 'c', 'S:sqrt', 'S:frac'], nice=['S:sup'],
             blurb='The only length that can be built from hbar, G and c '
                   'alone. That it exists at all is the argument that quantum '
                   'gravity has a scale; what happens there is not something '
                   'the formula knows.'),
    equation(name='Escape velocity', field='Classical mechanics',
             latex=r'v_e = \sqrt{\frac{2 G M}{r}}', slug='Escape_velocity',
             must=['v', 'G', 'M', 'r', 'S:sqrt', 'S:frac'], nice=['S:sub'],
             blurb='The speed at which kinetic energy exactly cancels '
                   'gravitational binding. Set it equal to c and the '
                   'Schwarzschild radius drops out, which is a coincidence of '
                   'the Newtonian derivation rather than a proof of it.'),
    equation(name='Hubble\'s law', field='Cosmology',
             latex=r'v = H_0 D', slug='Hubble%27s_law',
             must=['v', 'H', 'D'], nice=['S:sub'],
             blurb='Recession speed grows with distance. The constant of '
                   'proportionality is an inverse time, and that time is '
                   'roughly the age of the universe -- which is the whole '
                   'reason the law mattered.'),
    equation(name='Coulomb potential energy', field='Electromagnetism',
             latex=r'U = \frac{1}{4 \pi \epsilon_0} \frac{q_1 q_2}{r}',
             slug='Electric_potential_energy',
             must=['U', 'epsilon', 'r', 'S:frac', 'pi'], nice=['q'],
             blurb='The work needed to bring two charges together from far '
                   'apart. One power of r rather than two: the force is the '
                   'derivative of this, and differentiating is where the '
                   'second power comes from.'),

    # -- tilings ---------------------------------------------------------
    #
    # These sit here because the library is about notation, and the notation
    # of an aperiodic tiling is arithmetic: the whole obstruction to a tiling
    # repeating is that a ratio of counts comes out irrational.

    equation(name='Golden ratio', field='Tilings',
             latex=r'\phi = \frac{1 + \sqrt{5}}{2}', slug='Golden_ratio',
             must=['phi', 'S:frac', 'S:sqrt'], nice=[],
             blurb='The positive root of x^2 = x + 1, and the inflation factor '
                   'of the Penrose tilings. Its irrationality is not a '
                   'curiosity here: a tiling with a translational period has '
                   'only finitely many tiles per cell, so its tile ratios are '
                   'rational, and a tiling whose ratio is this number '
                   'therefore cannot have one.'),
    equation(name='Inflation quadratic', field='Tilings',
             latex=r'\lambda^2 = \lambda + 1', slug='Substitution_tiling',
             must=['lambda', 'S:sup2'], nice=[],
             blurb='The characteristic equation of the Fibonacci substitution '
                   'matrix, and the defining property of the golden ratio: a '
                   'length that reproduces itself plus a copy of what came '
                   'before. The eigenvalue is what a substitution rule '
                   'multiplies lengths by, and whether it is rational decides '
                   'whether the tiling can repeat. Note the collision: lambda '
                   'is a wavelength three entries above this one.'),
    equation(name='Penrose tile ratio', field='Tilings',
             latex=r'N_f = \phi N_t', slug='Penrose_tiling',
             must=['N', 'phi'], nice=['S:sub'],
             blurb='In any Penrose tiling of the plane, fat rhombs outnumber '
                   'thin ones by the golden ratio in the limit of a large '
                   'patch. The counts themselves are unbounded and mean '
                   'nothing; the ratio is the invariant, and it is the same '
                   'for every one of the uncountably many distinct tilings.'),
    equation(name='Inflation of area', field='Tilings',
             latex=r"A' = \phi^2 A", slug='Penrose_tiling',
             must=['A', 'phi', 'S:sup2'], nice=[],
             blurb='One step of inflation scales lengths by the golden ratio '
                   'and so scales areas by its square. This is where the '
                   'tilings meet the rest of this group: an inflation rule is '
                   'a statement about how area is budgeted, which is also what '
                   'a minimal surface and a string worldsheet are about.'),

    # -- the spectre monotile --------------------------------------------
    #
    # The Penrose entries above are a two-tile system and the constant that
    # governs them is the golden ratio.  These are the one-tile system found in
    # 2023, and the constant is different: the substitution matrix of the nine
    # metatile species has characteristic polynomial
    #
    #     lambda^5 (lambda - 1) (lambda + 1) (lambda^2 - 8 lambda + 1)
    #
    # so the Perron root is a root of the quadratic rather than anything to do
    # with sqrt5.  Every number below was checked against the substitution
    # matrix in github.com/brentharts/spectre rather than taken from a paper:
    # the eigenvalue exactly, the nine frequencies exactly in Q(sqrt15), and
    # the area formula against the tile geometry.

    equation(name='Spectre inflation quadratic', field='Tilings',
             latex=r'\mu^2 = 8 \mu - 1', slug='Einstein_problem',
             source='brentharts/spectre: chirality_e8.substitution_matrix(), nine species',
             must=['mu', 'S:sup2'], nice=[],
             blurb='The defining relation of the spectre inflation factor, and '
                   'the exact analogue of x^2 = x + 1 for the Penrose tilings '
                   'four entries above. It is the non-trivial factor of the '
                   'substitution matrix\'s characteristic polynomial; the rest '
                   'of that polynomial is a power of lambda and the two roots '
                   'of unity. Same shape of argument as the golden ratio, '
                   'different quadratic field.'),
    equation(name='Spectre inflation factor', field='Tilings',
             latex=r'\mu = 4 + \sqrt{15}', slug='Einstein_problem',
             source='brentharts/spectre: chirality_e8.substitution_matrix(), nine species',
             must=['mu', 'S:sqrt'], nice=[],
             blurb='The larger root, about 7.873, and the factor by which one '
                   'round of substitution multiplies the number of tiles. It '
                   'is irrational, which is the whole obstruction: a periodic '
                   'tiling has a rational ratio of tile counts and this number '
                   'is not one.'),
    equation(name='Spectre reciprocal pair', field='Tilings',
             latex=r'g \mu = 1', slug='Einstein_problem',
             source='brentharts/spectre: chirality_e8.substitution_matrix(), nine species',
             must=['g', 'mu'], nice=[],
             blurb='The two roots of the inflation quadratic multiply to one, '
                   'because the constant term is one. So the smaller root is '
                   'exactly the reciprocal of the larger, and the frequency of '
                   'the commonest metatile species is exactly one over the '
                   'inflation factor. That coincidence is not a coincidence: '
                   'it is the constant term of the quadratic, read twice.'),
    equation(name='Spectre triplet frequency', field='Tilings',
             latex=r'g = 4 - \sqrt{15}', slug='Aperiodic_tiling',
             source='brentharts/spectre: chirality_e8.substitution_matrix(), nine species',
             must=['g', 'S:sqrt'], nice=[],
             blurb='The limiting fraction of the tiling occupied by each of '
                   'the three metatile species that every supertile contains '
                   'exactly one of. Three species share this value, and they '
                   'share it for a reason: the corresponding rows of the '
                   'substitution matrix are all ones, which is a conservation '
                   'law rather than an accident.'),
    equation(name='Spectre frequency ratio', field='Tilings',
             latex=r'v_\Theta = \frac{v_\Gamma}{\mu}',
             slug='Substitution_tiling', source='brentharts/spectre: chirality_e8.substitution_matrix(), nine species',
             must=['v', 'mu', 'S:frac'], nice=['S:sub'],
             blurb='One species appears exactly one inflation step behind '
                   'another, so its frequency is the other\'s divided by the '
                   'inflation factor. The counts bear this out literally: the '
                   'sequence for the rarer species is the sequence for the '
                   'commoner one shifted by a generation.'),
    equation(name='Spectre count recurrence', field='Tilings',
             latex=r"N'' = 8 N' - N", slug='Substitution_tiling',
             source='brentharts/spectre: spectre_tile_counter.py',
             must=['N'], nice=[],
             blurb='Tile counts obey a second-order linear recurrence whose '
                   'characteristic polynomial is the inflation quadratic -- '
                   'the numbers run 1, 8, 63, 496, 3905, 30744. Two generations '
                   'of history are enough to determine the next, which is what '
                   'makes the count an integer sequence rather than a rounded '
                   'power, and the ratio of consecutive terms tends to the '
                   'inflation factor.'),
    equation(name='Spectre tile area', field='Tilings',
             latex=r'A = 2 \sqrt{3} a^2 + 3 a b + \sqrt{3} b^2',
             slug='Einstein_problem', source='brentharts/spectre: spectre.get_spectre_points()',
             must=['A', 'a', 'b', 'S:sqrt', 'S:sup2'], nice=[],
             blurb='The area of the fourteen-sided tile in terms of its two '
                   'edge lengths. The expression is not symmetric in a and b, '
                   'and that asymmetry is the whole reason the reflected tile '
                   'is a different shape rather than the same one turned over.'),
    equation(name='Hat tile area', field='Tilings',
             latex=r'A_H = 8 \sqrt{3}', slug='Einstein_problem',
             source='brentharts/spectre: spectre.get_spectre_points()',
             must=['A', 'S:sqrt'], nice=['S:sub'],
             blurb='The hat is the tile with a = 1 and b = root three. Its '
                   'sibling the turtle, with the lengths swapped, has area ten '
                   'root three, and the spectre with both edges equal has '
                   'three plus three root three -- three different areas from '
                   'one formula, which is what makes the family a family.'),

    # -- the hat, which is a different substitution ------------------------
    #
    # These look like they contradict the four entries above and do not.  The
    # spectre substitution acts on nine tile species and inflates by 4 + sqrt15;
    # the hat substitution acts on four metatiles H, T, P and F and inflates by
    # phi^4.  Two tilings, two substitutions, two Perron roots.  The two
    # characteristic polynomials even share a factor:
    #
    #     hat      (lambda - 1) (lambda + 1) (lambda^2 - 7 lambda + 1)
    #     spectre  lambda^5 (lambda - 1) (lambda + 1) (lambda^2 - 8 lambda + 1)
    #
    # so they differ in exactly one coefficient, and that coefficient is the
    # difference between sqrt5 and sqrt15.  Both were computed here rather than
    # quoted, from the matrices named in each `source`.

    equation(name='Hat inflation quadratic', field='Tilings',
             latex=r'\kappa^2 = 7 \kappa - 1', slug='Einstein_problem',
             source='brentharts/CICY: pyCICY.monotile.SUBSTITUTION, four '
                    'metatiles',
             must=['kappa', 'S:sup2'], nice=[],
             blurb='The defining relation of the hat inflation factor. One '
                   'coefficient away from the spectre\'s quadratic above, and '
                   'that one coefficient is the whole difference between the '
                   'two tilings\' arithmetic. The rest of the characteristic '
                   'polynomial is the same pair of roots of unity in both.'),
    equation(name='Hat inflation factor', field='Tilings',
             latex=r'\kappa = \frac{7 + 3 \sqrt{5}}{2}', slug='Einstein_problem',
             source='brentharts/CICY: pyCICY.monotile.inflation_factor()',
             must=['kappa', 'S:frac', 'S:sqrt'], nice=[],
             blurb='The larger root, about 6.854, which is the fourth power of '
                   'the golden ratio. So the hat tiling is governed by the '
                   'same constant as the Penrose tilings after all, four '
                   'powers up -- while the spectre, which is the same shape '
                   'family, is governed by root fifteen instead.'),
    equation(name='Hat constant as a golden power', field='Tilings',
             latex=r'\kappa = \phi^4', slug='Golden_ratio',
             source='brentharts/CICY: pyCICY.monotile.hat_chirality(), '
                    'is_phi4',
             must=['kappa', 'phi', 'S:sup'], nice=[],
             blurb='The hat inflation factor is the fourth power of the golden '
                   'ratio, so the constant governing the one-tile system is '
                   'the same one that governs the two-tile system Penrose '
                   'found fifty years earlier. This is the entry that ties the '
                   'two halves of this group together, and being written down '
                   'is what lets the library check it: both sides are pinned '
                   'to numbers elsewhere, so it is one of the few statements '
                   'here that can simply be evaluated.'),
    equation(name='Hat chirality ratio', field='Tilings',
             latex=r'\frac{N_u}{N_r} = \kappa', slug='Einstein_problem',
             source='brentharts/CICY: pyCICY.monotile.hat_chirality()',
             must=['N', 'kappa', 'S:frac'], nice=['S:sub'],
             blurb='Unreflected hats outnumber reflected ones by exactly the '
                   'inflation factor: about one anti-hat per 6.854 hats. The '
                   'tiling is therefore almost, but not quite, chiral, and the '
                   'imbalance is irrational -- which is the same argument as '
                   'the Penrose rhombs, since a periodic tiling would force '
                   'the ratio to be rational.'),

    # -- extremal geometry -----------------------------------------------

    equation(name='Euler characteristic of a closed surface', field='Extremal geometry',
             latex=r'\chi = 2 - 2 g', slug='Euler_characteristic',
             must=['chi', 'g'], nice=[],
             blurb='Two for a sphere, nought for a torus, and down by two for '
                   'every handle added. Nothing short of cutting the surface '
                   'changes it, which is what makes it worth computing -- and '
                   'in string perturbation theory the genus counting handles '
                   'is also the genus counting loops.'),
    equation(name='Riemann-Hurwitz (unbranched)', field='Extremal geometry',
             latex=r'\chi_C = n \chi_B', slug='Riemann%E2%80%93Hurwitz_formula',
             must=['chi', 'n'], nice=['S:sub'],
             blurb='An n-sheeted cover of a surface has n times its Euler '
                   'characteristic, provided nothing is branched. The full '
                   'formula subtracts a term for each ramification point; this '
                   'is the case where that term is absent, which is the case '
                   'that says a torus can cover a torus and nothing can cover '
                   'a sphere except a sphere.'),
    equation(name='Gauss-Bonnet theorem', field='Extremal geometry',
             latex=r'\int_M K \, dA + \oint_{\partial M} k_g \, ds = 2 \pi \chi',
             slug='Gauss%E2%80%93Bonnet_theorem',
             must=['K', 'chi', 'pi', 'S:int'], nice=['S:sub'],
             blurb='Total curvature is topology. The left side is measured '
                   'with a ruler and depends on the shape; the right side is a '
                   'whole number that does not. Bend the surface however you '
                   'like and the curvature moves around without the integral '
                   'changing, which is the sharpest statement in this group of '
                   'what a constraint on geometry costs.'),
    equation(name='Mean curvature', field='Extremal geometry',
             latex=r'H = \frac{\kappa_1 + \kappa_2}{2}',
             slug='Mean_curvature',
             must=['H', 'kappa', 'S:frac'], nice=['S:sub'],
             blurb='The average of the two principal curvatures at a point. '
                   'Note the collision: H is a Hamiltonian everywhere else in '
                   'this library.'),
    equation(name='Minimal surface condition', field='Extremal geometry',
             latex=r'H = 0', slug='Minimal_surface',
             must=['H'], nice=[],
             blurb='A surface is minimal exactly when its mean curvature '
                   'vanishes everywhere. It does not say the surface has least '
                   'area outright -- only that area is stationary under small '
                   'deformations, which is the same distinction as between a '
                   'minimum and a turning point. A soap film finds one of '
                   'these because surface tension makes area the energy.'),
    equation(name='Minimal surface equation', field='Extremal geometry',
             latex=r'(1 + u_y^2) u_{xx} - 2 u_x u_y u_{xy} + (1 + u_x^2) u_{yy} = 0',
             slug='Minimal_surface',
             must=['u', 'S:sub', 'S:sup2'], nice=[],
             blurb='The mean-curvature condition written out for a surface '
                   'given as a height above the plane. It is the Euler-Lagrange '
                   'equation of the area functional, and it is quasilinear '
                   'rather than linear -- the coefficients contain the slopes '
                   'of the very solution being sought, which is why soap films '
                   'are hard and Laplace\'s equation is easy.'),
    equation(name='Catenoid', field='Extremal geometry',
             latex=r'r = c \cosh \left( \frac{z}{c} \right)', slug='Catenoid',
             must=['r', 'c', 'z'], nice=['S:frac'],
             blurb='The surface swept by rotating a catenary, and after the '
                   'plane the first minimal surface anyone found. Stretch the '
                   'two rings holding the soap film too far apart and no '
                   'catenoid joins them: the solution stops existing and the '
                   'film snaps to two discs.'),
    equation(name='Area functional', field='Extremal geometry',
             latex=r'A = \int \int \sqrt{1 + |\nabla u|^2} \, dx \, dy',
             slug='Plateau%27s_problem',
             must=['A', 'nabla', 'S:int', 'S:sqrt'], nice=[],
             blurb='The area of a surface given as a height above the plane. '
                   'Plateau\'s problem is to minimise this with the boundary '
                   'held fixed, and the minimal surface equation is what comes '
                   'out of setting its first variation to zero. The square '
                   'root is the whole difficulty.'),
    equation(name='Kakeya conjecture', field='Extremal geometry',
             latex=r'\dim_H K = n', slug='Kakeya_set',
             must=['K', 'n'], nice=['S:sub'],
             blurb='A Kakeya set contains a unit segment in every direction '
                   'and can have measure zero, which is Besicovitch\'s '
                   'construction. The conjecture is that it cannot be small in '
                   'the dimensional sense as well: its Hausdorff dimension '
                   'must be the full n. Settled in the plane long ago, and in '
                   'three dimensions by Wang and Zahl in 2025.'),
    equation(name='Perron tree bound', field='Extremal geometry',
             latex=r'A \leq \frac{C}{\log n}', slug='Kakeya_set',
             must=['A', 'C', 'S:frac'], nice=[],
             blurb='Bisect a triangle, slide the halves together so they '
                   'overlap, and repeat: after n steps the figure still points '
                   'in all the original directions but its area has fallen '
                   'like one over log n. The decay is slow, and unbounded, '
                   'which is how a needle turns around in arbitrarily little '
                   'area.'),

    # -- string theory ----------------------------------------------------
    #
    # A note on the signatures below.  The classifier in rosettaui reads a
    # drawn formula and emits 'alpha' for \alpha', because the prime is a
    # separate glyph to it; the algebra here reads the same thing as one
    # quantity called alpha_prime, because a prime belongs to the name.  Both
    # are right for what they do, and the two vocabularies have to meet
    # somewhere.
    #
    # They meet in the signature.  'alpha' goes in must, so the classifier can
    # still identify these from a drawing; 'alpha_prime' goes in nice, where
    # the graph can pivot on it and where never matching costs nothing, since
    # a nice feature is optional by definition.  Teaching extract_features to
    # emit both would let the two agree properly, and is the better fix.

    equation(name='Nambu-Goto action', field='String theory',
             latex=r'S = -T \int d^2\sigma \sqrt{-\det(h_{ab})}',
             slug='Nambu%E2%80%93Goto_action',
             must=['S', 'T', 'sigma', 'S:int', 'S:sqrt'], nice=['S:sup2'],
             blurb='The action of a string is the area of the sheet it sweeps '
                   'through spacetime, times its tension. That is the whole '
                   'content: a point particle extremises its worldline length, '
                   'a string extremises its worldsheet area, and everything '
                   'else in the subject is consequence. It is also why minimal '
                   'surfaces belong in the same group as this.'),
    equation(name='String tension', field='String theory',
             latex=r"T = \frac{1}{2 \pi \alpha'}", slug='String_(physics)',
             must=['T', 'alpha', 'pi', 'S:frac'], nice=['alpha_prime'],
             blurb='Tension and the Regge slope are the same parameter '
                   'inverted. Note the collision: T is a temperature and a '
                   'period elsewhere in this library, and alpha prime is not '
                   'alpha -- the prime is part of the name, not an operation.'),
    equation(name='Regge trajectory', field='String theory',
             latex=r"J = \alpha' M^2 + \alpha_0", slug='Regge_theory',
             must=['J', 'alpha', 'M', 'S:sup2'], nice=['S:sub', 'alpha_prime'],
             blurb='Spin against mass squared, and the points lie on a line. '
                   'This was measured in hadron spectra before anyone proposed '
                   'a string, and explaining the straightness is what strings '
                   'were invented to do: a spinning relativistic string has '
                   'exactly this relation between its angular momentum and its '
                   'energy.'),
    equation(name='String length', field='String theory',
             latex=r"\ell_s = \sqrt{\alpha'}", slug='String_(physics)',
             must=['ell', 'alpha', 'S:sqrt'], nice=['S:sub', 'alpha_prime'],
             blurb='The one length the theory has, in natural units. Every '
                   'statement about strings being small is a statement about '
                   'this number, and nothing in the theory predicts it.'),
    equation(name='Genus expansion', field='String theory',
             latex=r'Z = \sum_g g_s^{-\chi} Z_g', slug='String_theory',
             must=['Z', 'chi', 'S:sum'], nice=['S:sub', 'S:sup'],
             blurb='The perturbation series of string theory is a sum over '
                   'surfaces, ordered by how many handles they have. The '
                   'exponent is minus the Euler characteristic, so by chi = 2 '
                   '- 2g each extra handle costs two powers of the coupling. '
                   'A loop expansion and a classification of surfaces turn out '
                   'to be the same list.'),
    equation(name='Critical dimension', field='String theory',
             latex=r'D = 26', slug='Critical_dimension',
             must=['D'], nice=[],
             blurb='The bosonic string is only consistent in twenty-six '
                   'spacetime dimensions; the superstring, in ten. The number '
                   'is not chosen. It is what makes a quantum anomaly cancel, '
                   'and getting a specific integer out of a consistency '
                   'condition rather than out of observation is the most '
                   'unusual thing about the subject.'),
    equation(name='Hagedorn temperature', field='String theory',
             latex=r"T_H = \frac{1}{4 \pi \sqrt{\alpha'} k_B}",
             slug='Hagedorn_temperature',
             must=['T', 'alpha', 'k', 'S:frac', 'S:sqrt'],
             nice=['pi', 'S:sub', 'alpha_prime'],
             blurb='Heat a gas of strings and the number of available states '
                   'grows exponentially with energy, so above this temperature '
                   'the partition function diverges and temperature stops '
                   'meaning anything. It is where this group rejoins ordinary '
                   'physics: the Boltzmann constant appears, and the quantity '
                   'on the left is the same temperature as in the gas laws.'),
]

EQUATION_FAMILIES = [
    (['S:nabla2', 'partial'], 'a second-order partial differential equation of '
     'the kind that governs fields -- compare the wave, heat and Laplace '
     'equations, which differ only in what the Laplacian is set equal to'),
    (['S:sum'], 'a summation, which translates directly to a for loop with an '
     'accumulator'),
    (['S:int'], 'an integral -- an accumulated quantity, which numerically '
     'becomes a quadrature or a Monte Carlo estimate'),
    (['hbar'], 'a quantum-mechanical relation: the presence of hbar is the '
     'giveaway'),
    (['c', 'G'], 'a relativistic gravitational relation, judging from the '
     'appearance of both c and G'),
    (['S:cases'], 'a piecewise definition, which maps onto an if/elif chain'),
]

# ------------------------------------------------------- physical constants

# Symbols that are physical constants rather than free variables, mapped to
# their scipy.constants names.  Passing these to eq2py as "already known" is
# what stops c and hbar being treated as arguments -- and it is the semantic
# mapping the RosettaMath paper is about, made concrete.
CONSTANTS = {
    'c': 'c', 'hbar': 'hbar', 'h': 'h', 'G': 'G', 'k_B': 'k',
    'epsilon_0': 'epsilon_0', 'mu_0': 'mu_0', 'N_A': 'N_A', 'pi': 'pi',
    'm_e': 'm_e', 'm_p': 'm_p', 'm_n': 'm_n',
}



# ---------------------------------------------------------------- algebra
#
# A small expression type, and a reader that builds it from the algebraic
# subset of LaTeX.
#
# This is the project's third LaTeX reader, which deserves a word.  rosettaui
# parses for *shape*, because it has to draw a fraction stacked and an exponent
# raised; lean4 parses the language of *types*, where juxtaposition is
# application; and this parses for *algebra*, where juxtaposition is
# multiplication and the only thing that matters is which operation is applied
# to what.  The three subsets disagree about what a space between two letters
# means, so one parser with a mode flag would have to be told which dialect it
# was reading anyway.  Keeping them apart also keeps rosettaphys importing
# nothing -- rosettaui imports this module, so this module cannot import it.


class Term:
    """One node of an expression.  Immutable; rearranging builds new ones."""

    __slots__ = ()

    def symbols(self):
        """Every symbol name occurring anywhere, in order of first appearance."""
        out = []
        _collect(self, out)
        return out

    def count(self, name):
        """How many times a symbol occurs.  Isolating needs this to be one."""
        return sum(1 for s in _walk(self) if isinstance(s, Sym)
                   and s.name == name)

    def contains(self, name):
        return self.count(name) > 0

    def latex(self):
        return render(self)

    def __str__(self):
        return render(self)


class Sym(Term):
    """A quantity: a letter, possibly with a subscript folded into the name."""

    __slots__ = ('name', 'tex')

    def __init__(self, name, tex=None):
        object.__setattr__(self, 'name', name)
        object.__setattr__(self, 'tex', tex if tex is not None else name)

    def __repr__(self):
        return 'Sym(%r)' % self.name

    def __eq__(self, other):
        return isinstance(other, Sym) and other.name == self.name

    def __hash__(self):
        return hash(('sym', self.name))


class Num(Term):
    """A numeric literal, kept as written rather than evaluated."""

    __slots__ = ('text',)

    def __init__(self, text):
        object.__setattr__(self, 'text', str(text))

    @property
    def value(self):
        try:
            return int(self.text)
        except ValueError:
            return float(self.text)

    def __repr__(self):
        return 'Num(%s)' % self.text

    def __eq__(self, other):
        return isinstance(other, Num) and other.text == self.text

    def __hash__(self):
        return hash(('num', self.text))


class Op(Term):
    """An operator applied to its operands: add, sub, mul, div, pow, neg."""

    __slots__ = ('op', 'args')

    def __init__(self, op, *args):
        object.__setattr__(self, 'op', op)
        object.__setattr__(self, 'args', tuple(args))

    def __repr__(self):
        return 'Op(%s, %s)' % (self.op, ', '.join(map(repr, self.args)))

    def __eq__(self, other):
        return (isinstance(other, Op) and other.op == self.op
                and other.args == self.args)

    def __hash__(self):
        return hash(('op', self.op, self.args))


class Call(Term):
    """A named function applied to one argument: log, sqrt, exp, sin."""

    __slots__ = ('func', 'arg')

    def __init__(self, func, arg):
        object.__setattr__(self, 'func', func)
        object.__setattr__(self, 'arg', arg)

    def __repr__(self):
        return 'Call(%s, %r)' % (self.func, self.arg)

    def __eq__(self, other):
        return (isinstance(other, Call) and other.func == self.func
                and other.arg == self.arg)

    def __hash__(self):
        return hash(('call', self.func, self.arg))


class Opaque(Term):
    r"""A fragment with no algebraic reading, carried along verbatim.

    \nabla \cdot E has no meaning in an algebra of products and sums, but an
    equation containing it still has two sides and still belongs in the graph.
    Refusing to read it at all would throw away the equation; pretending it is
    a product of nabla and E would be worse, because then something downstream
    would try to divide by nabla.  So it is kept as a lump: printable,
    comparable, and explicitly not rearrangeable.
    """

    __slots__ = ('tex',)

    def __init__(self, tex):
        object.__setattr__(self, 'tex', tex.strip())

    def __repr__(self):
        return 'Opaque(%r)' % self.tex

    def __eq__(self, other):
        return isinstance(other, Opaque) and other.tex == self.tex

    def __hash__(self):
        return hash(('opaque', self.tex))


def _walk(term):
    yield term
    if isinstance(term, Op):
        for arg in term.args:
            for sub in _walk(arg):
                yield sub
    elif isinstance(term, Call):
        for sub in _walk(term.arg):
            yield sub


def _collect(term, out):
    for node in _walk(term):
        if isinstance(node, Sym) and node.name not in out:
            out.append(node.name)


# shorthands, so the rearranger reads like the algebra it is doing
def add(a, b):
    return Op('add', a, b)


def sub(a, b):
    return Op('sub', a, b)


def mul(a, b):
    return Op('mul', a, b)


def div(a, b):
    return Op('div', a, b)


def power(a, b):
    return Op('pow', a, b)


def neg(a):
    return Op('neg', a)


# ----------------------------------------------------------------- reading

_COMMAND_SYMBOLS = {
    r'\hbar': 'hbar', r'\ell': 'ell', r'\infty': 'infty', r'\partial': 'partial',
    r'\nabla': 'nabla', r'\Box': 'Box',
}

BRACE_COMMANDS = (r'\underbrace', r'\overbrace')

FUNCTIONS = {r'\log': 'log', r'\ln': 'ln', r'\exp': 'exp', r'\sin': 'sin',
             r'\cos': 'cos', r'\tan': 'tan', r'\sinh': 'sinh',
             r'\cosh': 'cosh', r'\tanh': 'tanh', r'\det': 'det'}

PRODUCT_MARKS = (r'\cdot', r'\times', r'\ast', '*')

# Commands that carry no algebraic content and can be dropped on sight.
_NOISE = (r'\left', r'\right', r'\!', r'\,', r'\;', r'\:', r'\quad',
          r'\qquad', r'\displaystyle', r'\limits', '&')

# Notation that is not scalar algebra, and what it is instead.
#
# This table is the most important thing in the module, because without it the
# reader is far too willing.  Nothing stops it reading \nabla^2 \psi as nabla
# squared times psi, and once it has, solving for psi means dividing by it --
# which produces a confident, well formed, meaningless rearrangement.  The
# first version of this reader did exactly that, and the results typechecked.
#
# So an equation containing any of these is refused for rearrangement.  It
# still belongs in the graph, still has a signature, still gets drawn: it is
# only the algebra that declines to touch it.
NON_ALGEBRAIC = {
    r'\Delta': 'a change in a quantity, not a factor',
    r'\delta': 'a small change in a quantity, not a factor',
    r'\nabla': 'a gradient, divergence or curl',
    r'\partial': 'a partial derivative',
    r'\Box': "the d'Alembert operator",
    r'\sum': 'a summation',
    r'\prod': 'a product over an index',
    r'\dim': 'a dimension, not a factor',
    r'\int': 'an integral',
    r'\oint': 'a contour integral',
    r'\pm': 'an ambiguous sign',
    r'\mp': 'an ambiguous sign',
    r'\mid': 'a conditional bar',
    r'\parallel': 'a divergence bar',
    r'\hat': 'an operator hat',
    r'\vec': 'a vector arrow',
    r'\dot': 'a derivative dot',
    r'\ddot': 'a second derivative dot',
    r'\bar': 'an overbar',
    r'\times': 'a cross product',
    r'\otimes': 'a tensor product',
    r'\langle': 'a bra-ket',
    r'\rangle': 'a bra-ket',
}


class Unreadable(Exception):
    """This fragment has no algebraic reading.

    Raised rather than guessed at, because every downstream user of a Term --
    the rearranger, the Lean bridge -- is entitled to assume that what it was
    handed means what it says.
    """


def lex(latex):
    r"""LaTeX into tokens: commands whole, everything else one character."""
    out = []
    i = 0
    while i < len(latex):
        ch = latex[i]
        if ch.isspace():
            i += 1
            continue
        if ch == '\\':
            j = i + 1
            while j < len(latex) and latex[j].isalpha():
                j += 1
            out.append(latex[i:j] if j > i + 1 else latex[i:i + 2])
            i = max(j, i + 2)
            continue
        if ch.isdigit():
            j = i
            while j < len(latex) and (latex[j].isdigit() or
                                      (latex[j] == '.' and j + 1 < len(latex)
                                       and latex[j + 1].isdigit())):
                j += 1
            out.append(latex[i:j])
            i = j
            continue
        out.append(ch)
        i += 1
    return [t for t in out if t not in _NOISE]


class TermParser:
    """Tokens -> Term, for the algebraic subset."""

    def __init__(self, tokens, strict=True):
        self.toks = list(tokens)
        self.i = 0
        self.strict = strict
        self.labels = []              # (command, text) from every brace met

    # -- plumbing --------------------------------------------------------

    def peek(self, k=0):
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else None

    def next(self):
        t = self.peek()
        if t is not None:
            self.i += 1
        return t

    def expect(self, what):
        t = self.next()
        if t != what:
            raise Unreadable('expected %r, found %r' % (what, t))
        return t

    def group(self):
        """A {...} group, or the single token standing in for one."""
        if self.peek() == '{':
            self.next()
            inner = self.sum(stop=('}',))
            self.expect('}')
            return inner
        return self.atom()

    def raw_group(self):
        """A {...} group as text -- for a subscript, which is part of a name."""
        if self.peek() != '{':
            t = self.next()
            return t if t is not None else ''
        self.next()
        depth, out = 1, []
        while True:
            t = self.next()
            if t is None:
                raise Unreadable('unclosed {')
            if t == '{':
                depth += 1
            elif t == '}':
                depth -= 1
                if depth == 0:
                    return ''.join(out)
            out.append(t)

    # -- grammar ---------------------------------------------------------

    def parse(self):
        term = self.sum()
        if self.peek() is not None:
            raise Unreadable('trailing %r' % self.peek())
        return term

    def sum(self, stop=()):
        out = self.product(stop)
        while self.peek() in ('+', '-') and self.peek() not in stop:
            op = self.next()
            right = self.product(stop)
            out = Op('add' if op == '+' else 'sub', out, right)
        return out

    def product(self, stop=()):
        """A run of factors.  Juxtaposition multiplies; that is the dialect."""
        if self.peek() == '-':
            self.next()
            return Op('neg', self.product(stop))
        if self.peek() == '+':
            self.next()
        factors = []
        while True:
            t = self.peek()
            if t is None or t in stop or t in ('+', '-', '}', ')', ']'):
                break
            if t in PRODUCT_MARKS:
                # \nabla \cdot E is a divergence, not a product of two things,
                # and the dot is the only warning the notation gives
                if factors and _is_operator_symbol(factors[-1]):
                    raise Unreadable('%s applied with \\cdot is an operator, '
                                     'not a factor' % factors[-1])
                self.next()
                continue
            if t in RELATIONS or t == '=':
                break
            factors.append(self.power(stop))
        if not factors:
            raise Unreadable('an empty product')
        out = factors[0]
        for factor in factors[1:]:
            out = Op('mul', out, factor)
        return out

    def power(self, stop=()):
        base = self.atom()
        while self.peek() == '^':
            if self._prime_ahead():
                # \alpha^\prime and \alpha^{\prime} are the same quantity as
                # \alpha', and none of the three is alpha raised to anything.
                # Left alone, this reads as a power whose exponent is a symbol
                # called 'prime', which then joins to every other equation
                # mentioning it.
                base = self._primed(base)
                continue
            self.next()
            base = Op('pow', base, self.group())
        if self.peek() == '_':                    # a trailing index on a group
            raise Unreadable('a subscript in a position that is not a name')
        return base

    def _prime_ahead(self):
        """Is the ^ at the cursor followed by nothing but a prime mark?"""
        if self.peek(1) == r'\prime':
            return True
        return (self.peek(1) == '{' and self.peek(2) == r'\prime'
                and self.peek(3) == '}')

    def _primed(self, base):
        """Consume a ^\\prime or ^{\\prime} and mark the name it belongs to."""
        self.next()                                       # the ^
        self.next()                                       # \prime or {
        if self.peek() == r'\prime':
            self.next()
            self.expect('}')
        if not isinstance(base, Sym):
            raise Unreadable('a prime on something that is not a name')
        return Sym(base.name + '_prime', base.tex + "'")

    def atom(self):
        t = self.next()
        if t is None:
            raise Unreadable('the expression ended early')
        if t == '(':
            inner = self.sum(stop=(')',))
            self.expect(')')
            return inner
        if t == '{':
            inner = self.sum(stop=('}',))
            self.expect('}')
            return inner
        if t in BRACE_COMMANDS:
            # \underbrace{x}_{label}: the body is the expression and the label
            # is provenance.  Both are kept -- the label is what tells the Lean
            # bridge which equation a side of a composed statement came from,
            # and dropping it here would mean parsing the LaTeX twice to get
            # it back.
            body = self.group()
            if self.peek() in ('_', '^'):
                self.next()
                self.labels.append((t, self.raw_group()))
            return body
        if t in (r'\text', r'\mathrm', r'\mathbf', r'\mathit',
                 r'\mathcal', r'\operatorname'):
            return Sym(_clean_index(self.raw_group()) or 'x', t)
        if t == r'\frac' or t == r'\dfrac' or t == r'\tfrac':
            return Op('div', self.group(), self.group())
        if t == r'\sqrt':
            if self.peek() == '[':
                raise Unreadable('an nth root')
            return Call('sqrt', self.group())
        if t in FUNCTIONS:
            return Call(FUNCTIONS[t], self.power())
        if t[0].isdigit():
            return Num(t)
        return self.name(t)

    def name(self, token):
        """A letter or command, plus any subscript, as one quantity."""
        if token in _COMMAND_SYMBOLS:
            base, tex = _COMMAND_SYMBOLS[token], token
        elif token.startswith('\\') and len(token) > 1:
            # the name loses the backslash so that it matches the feature
            # vocabulary the signatures are written in -- 'pi', not '\\pi' --
            # while tex keeps it, because that is how it has to print
            base, tex = token[1:], token
        elif token.isalpha():
            base = tex = token
        else:
            raise Unreadable('no reading for %r' % token)
        # a prime is part of the name, not an operation on it.  alpha' is the
        # Regge slope and alpha is a different number entirely; x' is the
        # coordinate in the other frame.  Reading the mark as anything else
        # would let the rearranger cancel a quantity against its own primed
        # version, which is the same class of error as joining two equations on
        # a letter they disagree about.
        primes = 0
        while self.peek() in ("'", r'\prime'):
            self.next()
            primes += 1
        if self.peek() == '_':
            self.next()
            index = self.raw_group()
            # m_1 and m_2 are two masses, not m indexed by a number: the
            # subscript belongs to the name, which is the only reading that
            # keeps them apart when it comes time to solve for one
            base = '%s_%s' % (base, _clean_index(index))
            tex = '%s_{%s}' % (tex, index)
        while self.peek() in ("'", r'\prime'):     # x'_i and x_i' both occur
            self.next()
            primes += 1
        if primes:
            # spelt out, because the name has to survive becoming a Python
            # identifier, and Python does not accept an apostrophe.  Lean would
            # have taken alpha' happily; the printer keeps the mark in tex, so
            # only the internal name is spelt.
            base = base + '_prime' * primes
            tex = tex + "'" * primes
        return Sym(base, tex)


def _clean_index(text):
    out = ''.join(ch for ch in text if ch.isalnum() or ch == '_')
    return out or 'i'


def _is_operator_symbol(term):
    return isinstance(term, Sym) and term.name in ('nabla', 'partial', 'Box')


def algebraic(latex):
    """Why this fragment is not scalar algebra, or None if it is.

    Checked on the token stream rather than during parsing, so the answer is
    the same whether or not the rest of the fragment happens to parse.
    """
    for token in lex(latex):
        if token in BRACE_COMMANDS:
            continue
        if token in NON_ALGEBRAIC:
            return NON_ALGEBRAIC[token]
    if _TENSOR_INDEX.search(latex):
        return 'an indexed tensor component'
    return None


# An index made of Greek letters -- G_{\mu\nu} -- is a tensor component, and
# nothing in this algebra can divide by one.  The test is deliberately narrow:
# a \text{...} label under a brace is also a command inside a subscript, and
# refusing those would refuse every composed statement this module builds.
#
# Narrow, but the first version was not narrow enough: it refused a brace that
# merely *contained* a Greek command anywhere, which is true of an index and
# equally true of an exponent.  So e^{i \pi} was read as a tensor component and
# Euler's identity was refused for a reason that was not about it, and
# g_s^{-\chi} -- the string genus expansion, where chi is a number and not an
# index -- would have been refused the same way.
#
# An index is the whole of what sits in the brace: one or more Greek letters
# and nothing else.  The moment a digit, a sign, an operator or a Latin letter
# appears alongside, the brace is an expression, and an expression is the
# algebra's business.  A lone braced Greek is still read as an index, because
# T^{\mu} is a component and the exponent that wanted to be a power should have
# been written without the brace.
_GREEK_INDEX = ('alpha', 'beta', 'gamma', 'delta', 'epsilon', 'zeta', 'eta',
                'theta', 'iota', 'kappa', 'lambda', 'mu', 'nu', 'xi', 'pi',
                'rho', 'sigma', 'tau', 'upsilon', 'phi', 'chi', 'psi', 'omega')
_TENSOR_INDEX = re.compile(
    r'[_^]\s*\{\s*(?:\\(?:%s)\b\s*)+\}' % '|'.join(_GREEK_INDEX))


def read_term(latex, strict=True):
    """A LaTeX fragment as a Term, or Opaque when it has no algebraic reading.

    With strict off, an unreadable fragment becomes Opaque rather than raising,
    which is what the graph wants: an equation full of divergences still has
    two sides worth relating, even though neither can be rearranged.
    """
    why = algebraic(latex)
    if why is None:
        parser = TermParser(lex(latex))
        try:
            term = parser.parse()
        except Unreadable as exc:
            why = str(exc)
        else:
            read_term.labels = parser.labels
            return term
    read_term.labels = []
    if strict:
        raise Unreadable(why)
    return Opaque(latex)



def strip_brace(latex):
    r"""Peel an \overbrace or \underbrace wrapping a whole fragment.

    Returns (inner, label).  A brace around an entire statement is a caption
    on the statement rather than part of it, and leaving it in place hides the
    top level relation one group deep where split_relation cannot see it.
    """
    text = latex.strip()
    for command in BRACE_COMMANDS:
        if not text.startswith(command + '{'):
            continue
        depth, i = 0, len(command)
        start = i + 1
        while i < len(text):
            if text[i] == '{':
                depth += 1
            elif text[i] == '}':
                depth -= 1
                if depth == 0:
                    break
            i += 1
        else:
            return text, ''
        inner, rest = text[start:i], text[i + 1:].strip()
        label = ''
        if rest[:1] in ('_', '^'):
            label = rest[1:].strip()
            if label.startswith('{') and label.endswith('}'):
                label = label[1:-1]
        return inner, label
    return text, ''


class Relation:
    """Two Terms and the relation between them, with any brace labels kept."""

    __slots__ = ('left', 'op', 'right', 'caption', 'labels')

    def __init__(self, left, op, right, caption='', labels=()):
        self.left = left
        self.op = op
        self.right = right
        self.caption = caption            # the overbrace over the whole thing
        self.labels = list(labels)        # one per side, in order

    def symbols(self):
        out = list(self.left.symbols())
        for name in self.right.symbols():
            if name not in out:
                out.append(name)
        return out

    def latex(self):
        return '%s %s %s' % (render(self.left), self.op, render(self.right))

    def __repr__(self):
        return '<Relation %s>' % self.latex()


def read_relation(latex, strict=True):
    """A LaTeX statement as a Relation.

    Handles the composed form this module produces -- an overbrace round the
    whole claim, an underbrace under each side -- as well as a plain equation
    straight out of the library.
    """
    body, caption = strip_brace(latex)
    parts = split_relation(body)
    if parts is None:
        raise Unreadable('%r states no relation' % latex)
    left_tex, op, right_tex = parts
    labels = []
    terms = []
    for side in (left_tex, right_tex):
        inner, label = strip_brace(side)
        labels.append(_label_text(label))
        terms.append(read_term(inner, strict))
    return Relation(terms[0], op, terms[1], _label_text(caption), labels)


def _label_text(label):
    r"""The words inside a \text{...} label, without the command."""
    text = label.strip()
    for command in (r'\text', r'\mathrm', r'\mathbf'):
        if text.startswith(command + '{') and text.endswith('}'):
            text = text[len(command) + 1:-1]
    return text.replace(r'\_', '_').strip()


# ---------------------------------------------------------------- printing

_PREC = {'add': 1, 'sub': 1, 'mul': 2, 'div': 2, 'neg': 3, 'pow': 4}


def render(term, prec=0):
    """A Term back as LaTeX, bracketed exactly where it has to be."""
    if isinstance(term, Sym):
        return term.tex
    if isinstance(term, Num):
        return term.text
    if isinstance(term, Opaque):
        return term.tex
    if isinstance(term, Call):
        if term.func == 'sqrt':
            return r'\sqrt{%s}' % render(term.arg)
        return r'\%s %s' % (term.func, render(term.arg, 3))
    if not isinstance(term, Op):
        raise Unreadable('cannot render %r' % (term,))
    op, args = term.op, term.args
    if op == 'div':
        # a fraction brackets itself against a neighbouring factor, but not
        # against a superscript: \frac{a}{b}^{2} reads as if the exponent
        # belonged to b alone, which is a different number
        text = r'\frac{%s}{%s}' % (render(args[0]), render(args[1]))
        return _bracket(text, _PREC['div'], prec)
    if op == 'neg':
        return _bracket('-%s' % render(args[0], 3), 3, prec)
    if op == 'pow':
        return _bracket('%s^{%s}' % (render(args[0], 5), render(args[1])),
                        4, prec)
    mine = _PREC[op]
    joiner = {'add': ' + ', 'sub': ' - ', 'mul': ' '}[op]
    left = render(args[0], mine)
    # + and * associate, so a bracket on the right would only be noise; - does
    # not, and a - (b - c) is a different number from (a - b) - c
    right = render(args[1], mine if op in ('add', 'mul') else mine + 1)
    return _bracket(left + joiner + right, mine, prec)


def _bracket(text, mine, ctx):
    return r'\left( %s \right)' % text if mine < ctx else text


# ------------------------------------------------------------ rearranging
#
# Isolating a quantity is the one piece of real algebra this project does, so
# it is worth being exact about what it will and will not do.
#
# It peels operations off the side the quantity is on, applying the inverse to
# the other side, and it stops the moment it meets something it cannot invert
# uniquely.  The quantity must occur exactly once: x + x = 1 needs collecting
# like terms, which is a different and much larger job, and guessing at it
# would produce confident nonsense.
#
# Even powers are refused outright.  x^2 = 4 does not give x = 2; it gives
# x = \pm 2, and a chain built on the wrong branch is a false statement that
# type checks.  Refusing is the only answer that stays honest.


class CannotIsolate(Exception):
    """Why a quantity could not be moved to one side, in words."""


def isolate(left, right, name):
    """Rearrange left = right into name = something.  Raises if it cannot."""
    if isinstance(left, Opaque) or isinstance(right, Opaque):
        raise CannotIsolate('the equation has a part with no algebraic reading')
    here, there = left, right
    if not here.contains(name):
        here, there = right, left
    occurrences = here.count(name) + there.count(name)
    if occurrences == 0:
        raise CannotIsolate('%s does not appear in the equation' % name)
    if occurrences > 1:
        raise CannotIsolate('%s appears %d times, so isolating it would need '
                            'terms collected first' % (name, occurrences))
    for _ in range(64):
        if isinstance(here, Sym) and here.name == name:
            return there
        here, there = _peel(here, there, name)
    raise CannotIsolate('gave up rearranging for %s' % name)


def _peel(here, there, name):
    """Strip one operation off `here`, applying its inverse to `there`."""
    if isinstance(here, Call):
        inverse = {'sqrt': lambda t: Op('pow', t, Num(2)),
                   'log': lambda t: Call('exp', t),
                   'ln': lambda t: Call('exp', t),
                   'exp': lambda t: Call('ln', t)}.get(here.func)
        if inverse is None:
            raise CannotIsolate('%s has no inverse here' % here.func)
        return here.arg, inverse(there)
    if not isinstance(here, Op):
        raise CannotIsolate('cannot take %r apart' % (here,))
    op, args = here.op, here.args
    if op == 'neg':
        return args[0], Op('neg', there)
    if op == 'pow':
        base, exponent = args
        if base.contains(name):
            if isinstance(exponent, Num) and exponent.value % 2 == 0:
                raise CannotIsolate(
                    'an even power: %s would have two roots, and picking one '
                    'is a choice the equation does not record' % render(here))
            if isinstance(exponent, Num) and exponent.value == 1:
                return base, there
            return base, Op('pow', there, Op('div', Num(1), exponent))
        raise CannotIsolate('%s appears in an exponent' % name)
    left, right = args
    first = left.contains(name)
    other = right if first else left
    inner = left if first else right
    if op == 'add':
        return inner, Op('sub', there, other)
    if op == 'sub':
        if first:
            return inner, Op('add', there, other)
        return inner, Op('sub', other, there)      # a - x = c  ->  x = a - c
    if op == 'mul':
        return inner, Op('div', there, other)
    if op == 'div':
        if first:
            return inner, Op('mul', there, other)  # x / b = c  ->  x = c b
        return inner, Op('div', other, there)      # a / x = c  ->  x = a / c
    raise CannotIsolate('no inverse for %r' % op)


# ------------------------------------------------------------- quantities
#
# The hardest bug in this module was a join that read
#
#     exp(S / k_B) = F d
#
# and meant nothing at all.  Boltzmann's W is a count of microstates; the W in
# W = F d is an energy.  The letters match, so the graph joined them, and the
# result was a false statement that parsed, typechecked and rendered beautifully.
#
# The fix is the thing the 'Overloaded notation' article in this file has been
# saying all along: a glyph is not a quantity.  An equation has to say what its
# letters denote, and two equations may only be joined on a letter they agree
# about.  So each entry carries a `reads` table, the graph grows a third kind of
# node for the quantities themselves, and a pivot with no agreed reading is no
# longer a pivot.
#
# This is also what makes the graph worth walking.  Before, equations were
# linked because they shared a character; now they are linked because they are
# about the same physical thing, which is a claim worth making.

QUANTITIES = {}


def add_quantity(name, dimension, blurb, slug, kind='quantity'):
    QUANTITIES[name] = Quantity(
        name=name, dimension=dimension, blurb=blurb, wiki=WIKI + slug,
        role=kind)
    return QUANTITIES[name]


class Quantity(Node):
    """A physical thing a symbol can denote, independent of how it is written.

    Dimensions are written in the usual M/L/T/I/K/N basis, as a string, because
    this module does not do dimensional analysis -- it records the dimension so
    that something later can, and so that a reader can see at a glance that two
    quantities joined on a pivot really are commensurable.
    """

    kind = 'quantity'
    key_field = 'name'

    @property
    def is_constant(self):
        return self['role'] == 'constant'


# -- the quantities the library talks about ---------------------------------
add_quantity('energy', 'M L^2 T^-2',
             'The capacity to do work, in joules. Kinetic, potential, thermal '
             'and rest energy are all this one quantity, which is why they can '
             'be added and why conversion between them is the subject of most '
             'of mechanics.', 'Energy')
add_quantity('force', 'M L T^-2',
             'A push, in newtons -- the rate at which momentum is delivered.',
             'Force')
add_quantity('mass', 'M',
             'Resistance to acceleration, and the source of gravity. That '
             'those are the same number is the equivalence principle, not a '
             'definition.', 'Mass')
add_quantity('length', 'L',
             'A distance or a size, in metres.', 'Length')
add_quantity('area', 'L^2', 'A surface, in square metres.', 'Area')
add_quantity('volume', 'L^3', 'A region of space, in cubic metres.', 'Volume')
add_quantity('time', 'T', 'A duration or an instant, in seconds.', 'Time')
add_quantity('speed', 'L T^-1',
             'Distance covered per unit time. Velocity is the same quantity '
             'with a direction attached.', 'Speed')
add_quantity('acceleration', 'L T^-2',
             'The rate at which velocity changes.', 'Acceleration')
add_quantity('momentum', 'M L T^-1',
             'Mass times velocity: the conserved quantity that makes '
             'collisions solvable.', 'Momentum')
add_quantity('pressure', 'M L^-1 T^-2',
             'Force per unit area, in pascals.', 'Pressure')
add_quantity('density', 'M L^-3',
             'Mass per unit volume. One of at least four things rho is used '
             'for, and the one it is named after.', 'Density')
add_quantity('temperature', 'K',
             'A measure of the energy per degree of freedom, in kelvin.',
             'Temperature')
add_quantity('entropy', 'M L^2 T^-2 K^-1',
             'A count of the microstates consistent with what is known, in '
             'units that make it add to energy over temperature.', 'Entropy')
add_quantity('microstate count', '1',
             'A pure number: how many arrangements a system could be in. It is '
             'what sits inside Boltzmann\'s logarithm, and it is emphatically '
             'not an energy, however much its letter looks like one.',
             'Microstate_(statistical_mechanics)')
add_quantity('frequency', 'T^-1',
             'Cycles per second, in hertz.', 'Frequency')
add_quantity('angular frequency', 'T^-1',
             'Radians per second. Dimensionally identical to frequency and '
             'numerically different by two pi, which is exactly the sort of '
             'distinction dimensional analysis cannot catch.',
             'Angular_frequency')
add_quantity('wavelength', 'L',
             'The distance between repeats of a wave.', 'Wavelength')
add_quantity('charge', 'I T', 'Electric charge, in coulombs.',
             'Electric_charge')
add_quantity('voltage', 'M L^2 T^-3 I^-1',
             'Potential difference, in volts: energy per unit charge.',
             'Voltage')
add_quantity('current', 'I', 'Charge flow per unit time, in amperes.',
             'Electric_current')
add_quantity('resistance', 'M L^2 T^-3 I^-2',
             'Opposition to current, in ohms.', 'Electrical_resistance')
add_quantity('capacitance', 'M^-1 L^-2 T^4 I^2',
             'Charge stored per volt, in farads.', 'Capacitance')
add_quantity('power', 'M L^2 T^-3',
             'Energy per unit time, in watts.', 'Power_(physics)')
add_quantity('amount', 'N', 'A count of particles, in moles.',
             'Amount_of_substance')
add_quantity('number density', 'L^-3',
             'Particles per unit volume.', 'Number_density')
add_quantity('spring constant', 'M T^-2',
             'Stiffness: force per unit displacement.', 'Hooke%27s_law')
add_quantity('gravitational field', 'L T^-2',
             'The acceleration a gravitational source imposes, independent of '
             'what is falling. Dimensionally an acceleration, and kept apart '
             'from one because g and a appear in the same equations meaning '
             'different things.', 'Gravitational_field')
add_quantity('flux', 'M T^-3',
             'Energy crossing unit area per unit time.', 'Radiant_flux')
add_quantity('hubble parameter', 'T^-1',
             'The expansion rate of the universe, an inverse time.',
             'Hubble%27s_law')

# -- constants, which are quantities that do not vary -----------------------
add_quantity('speed of light', 'L T^-1',
             'Exactly 299792458 m/s, and a conversion factor between space and '
             'time rather than a speed anything travels at.', 'Speed_of_light',
             kind='constant')
add_quantity('planck constant', 'M L^2 T^-1',
             'The quantum of action. Note that h and hbar differ by two pi and '
             'are not interchangeable, which is the commonest way to be out by '
             'a factor of six in quantum mechanics.', 'Planck_constant',
             kind='constant')
add_quantity('reduced planck constant', 'M L^2 T^-1',
             'h over two pi, which is what appears whenever the angle is in '
             'radians -- so, nearly always.', 'Planck_constant',
             kind='constant')
add_quantity('gravitational constant', 'M^-1 L^3 T^-2',
             'Newton\'s G, the weakest and least precisely known of the '
             'constants.', 'Gravitational_constant', kind='constant')
add_quantity('boltzmann constant', 'M L^2 T^-2 K^-1',
             'The conversion between temperature and energy per degree of '
             'freedom.', 'Boltzmann_constant', kind='constant')
add_quantity('gas constant', 'M L^2 T^-2 K^-1 N^-1',
             'The Boltzmann constant per mole rather than per particle.',
             'Gas_constant', kind='constant')
add_quantity('permittivity', 'M^-1 L^-3 T^4 I^2',
             'The permittivity of free space, which sets the strength of the '
             'electrostatic force.', 'Vacuum_permittivity', kind='constant')
add_quantity('elementary charge', 'I T',
             'The charge on a proton. Shares its letter with Euler\'s number, '
             'which is the single most dangerous collision in physics '
             'notation.', 'Elementary_charge', kind='constant')
add_quantity('stefan-boltzmann constant', 'M T^-3 K^-4',
             'The constant in the fourth-power radiation law.',
             'Stefan%E2%80%93Boltzmann_constant', kind='constant')
add_quantity('pi', '1', 'The ratio of a circumference to a diameter.', 'Pi',
             kind='constant')
add_quantity('dimensionless', '1',
             'A pure number: a ratio, a count, an index, or an argument to a '
             'logarithm.', 'Dimensionless_quantity')

# -- geometry, topology and the string ------------------------------------
#
# Two warnings about what follows.
#
# First, most of these are dimensionless, and dimensional analysis therefore
# cannot tell a genus from a tile count from a Hausdorff dimension.  That is
# precisely why they are listed separately rather than all folded into
# 'dimensionless': the dimension string is not what keeps them apart, the name
# is, and a pivot needs the name.
#
# Second, the string entries are in natural units, where hbar and c are one.
# The Regge slope is written L^2 and the tension L^-2 because that is what they
# are once the constants are set to one -- not because a tension is really an
# inverse area.  Restoring the constants is a separate job, and pretending
# otherwise here would put a false dimension in the table.

add_quantity('golden ratio', '1',
             'The positive root of x^2 = x + 1. It is the inflation factor of '
             'the Penrose tilings, and the reason those tilings cannot repeat: '
             'a periodic tiling forces a rational ratio of tile counts, and '
             'this number is not one.', 'Golden_ratio', kind='constant')
add_quantity('inflation factor', '1',
             'What a substitution rule multiplies a length by each time it is '
             'applied. When it is irrational the tiling it generates has no '
             'translational period.', 'Substitution_tiling')
add_quantity('patch area', 'L^2',
             'The area of a finite patch of a tiling. An area, and joinable '
             'to nothing else that is one: a tiling patch can be made as large '
             'as you like, so equating it to a horizon area or a soap film '
             'would be a true conditional about nothing. Dimensional agreement '
             'is not the test -- the test is whether the two equations are '
             'about the same thing.', 'Penrose_tiling')
add_quantity('tile count', '1',
             'How many tiles of one kind appear in a patch. Only ratios of '
             'these are meaningful, since the patch can always be made bigger.',
             'Penrose_tiling')
add_quantity('tile frequency', '1',
             'The limiting fraction of a tiling made of one species of tile. '
             'Unlike a tile count it converges, and for a substitution tiling '
             'it is a component of the Perron eigenvector of the substitution '
             'matrix -- which is why these come out as algebraic numbers '
             'rather than as measurements.', 'Substitution_tiling')
add_quantity('tile area', 'L^2',
             'The area of a single tile, as opposed to a patch of them. Kept '
             'apart from patch area for the reason given there: a tile has a '
             'fixed size and a patch does not, so equating one to the other '
             'would be a statement about nothing.', 'Aperiodic_tiling')
add_quantity('genus', '1',
             'The number of handles on a closed orientable surface: nought for '
             'a sphere, one for a torus. In string perturbation theory it is '
             'also the loop order.', 'Genus_(mathematics)')
add_quantity('euler characteristic', '1',
             'A whole number attached to a surface that no amount of bending '
             'can change. It is what makes topology quantitative, and it is '
             'the exponent the string coupling is raised to.',
             'Euler_characteristic')
add_quantity('covering degree', '1',
             'How many sheets of a covering surface sit over each point of the '
             'surface below.', 'Covering_space')
add_quantity('mean curvature', 'L^-1',
             'The average of the two principal curvatures. Setting it to zero '
             'is what makes a surface minimal.', 'Mean_curvature')
add_quantity('principal curvature', 'L^-1',
             'The largest and smallest curvatures of the normal sections at a '
             'point on a surface.', 'Principal_curvature')
add_quantity('gaussian curvature', 'L^-2',
             'The product of the principal curvatures. Unlike the mean '
             'curvature it survives bending the surface without stretching it, '
             'which is what Gauss called remarkable.', 'Gaussian_curvature')
add_quantity('geodesic curvature', 'L^-1',
             'How far a curve drawn on a surface bends away from being a '
             'geodesic of that surface.', 'Geodesic_curvature')
add_quantity('slope', '1',
             'A partial derivative of a height function: how steeply a surface '
             'written as a graph rises in one direction.', 'Slope')
add_quantity('hausdorff dimension', '1',
             'A dimension that need not be a whole number, defined by how a '
             'covering of the set scales. A Kakeya set can have measure zero '
             'and still have full Hausdorff dimension.', 'Hausdorff_dimension')
add_quantity('count', '1',
             'A plain whole number of things -- steps in a construction, '
             'sheets in a cover.', 'Natural_number')
add_quantity('action', 'M L^2 T^-1',
             'Energy times time: the quantity a physical path makes '
             'stationary. Dimensionally identical to the Planck constant, '
             'which is the point of calling h the quantum of action.',
             'Action_(physics)')
add_quantity('regge slope', 'L^2',
             'Alpha prime, the one free parameter of the string: the square of '
             'the string length, and the slope of the line that mass-squared '
             'and spin lie on.', 'Regge_theory')
add_quantity('string tension', 'L^-2',
             'Energy per unit length of a string, which in natural units is '
             'the reciprocal of the Regge slope up to a factor of two pi.',
             'String_(physics)')
add_quantity('string coupling', '1',
             'The number that controls how readily a worldsheet splits. It is '
             'not put in by hand: it is set by the vacuum value of the '
             'dilaton.', 'String_theory')
add_quantity('spin', '1',
             'Angular momentum in units of hbar, which for the states on a '
             'Regge trajectory is a whole number.', 'Spin_(physics)')
add_quantity('partition function', '1',
             'A sum over configurations, weighted. Everything thermodynamic, '
             'and in string theory everything perturbative, is a derivative of '
             'it.', 'Partition_function_(statistical_mechanics)')
add_quantity('spacetime dimension', '1',
             'How many coordinates it takes to label an event. A count, but '
             'kept apart from other counts on purpose: pivoting the dimension '
             'of spacetime against a number of steps in a construction would '
             'be dimensionally impeccable and entirely meaningless.',
             'Dimension_(vector_space)')

# ---------------------------------------------------------------- readings
#
# What each equation's letters denote.  Keyed by equation name, then by the
# symbol name as the algebra spells it (no backslash, subscript folded in).
#
# An equation missing from this table cannot be joined to anything: a pivot
# needs both sides to agree about what the letter means, and silence is not
# agreement.  That is a deliberate default -- the alternative, assuming the
# common reading, is what produced exp(S/k_B) = F d.

READINGS = {
    'Mass-energy equivalence': {
        'E': 'energy', 'm': 'mass', 'c': 'speed of light'},
    "Newton's second law": {
        'F': 'force', 'm': 'mass', 'a': 'acceleration'},
    "Newton's law of gravitation": {
        'F': 'force', 'G': 'gravitational constant', 'm_1': 'mass',
        'm_2': 'mass', 'r': 'length'},
    "Coulomb's law": {
        'F': 'force', 'pi': 'pi', 'epsilon_0': 'permittivity',
        'q_1': 'charge', 'q_2': 'charge', 'r': 'length'},
    'Coulomb potential energy': {
        'U': 'energy', 'pi': 'pi', 'epsilon_0': 'permittivity',
        'q_1': 'charge', 'q_2': 'charge', 'r': 'length'},
    'Kinetic energy': {
        'E_k': 'energy', 'm': 'mass', 'v': 'speed'},
    'Momentum': {'p': 'momentum', 'm': 'mass', 'v': 'speed'},
    'Work done by a force': {
        'W': 'energy', 'F': 'force', 'd': 'length'},
    'Gravitational potential energy': {
        'U': 'energy', 'm': 'mass', 'g': 'gravitational field', 'h': 'length'},
    'Surface gravity': {
        'g': 'gravitational field', 'G': 'gravitational constant',
        'M': 'mass', 'r': 'length'},
    "Hooke's law": {
        'F': 'force', 'k': 'spring constant', 'x': 'length'},
    'Escape velocity': {
        'v_e': 'speed', 'G': 'gravitational constant', 'M': 'mass',
        'r': 'length'},
    'Angular frequency': {
        'omega': 'angular frequency', 'pi': 'pi', 'f': 'frequency'},
    'Wave speed': {
        'v': 'speed', 'f': 'frequency', 'lambda': 'wavelength'},
    'Planck relation': {
        'E': 'energy', 'h': 'planck constant', 'nu': 'frequency'},
    'de Broglie relation': {
        'lambda': 'wavelength', 'h': 'planck constant', 'p': 'momentum'},
    'Compton wavelength': {
        'lambda_C': 'wavelength', 'h': 'planck constant', 'm': 'mass',
        'c': 'speed of light'},
    'Boltzmann entropy': {
        'S': 'entropy', 'k_B': 'boltzmann constant', 'W': 'microstate count'},
    'Bekenstein-Hawking entropy': {
        'S': 'entropy', 'k_B': 'boltzmann constant', 'c': 'speed of light',
        'A': 'area', 'G': 'gravitational constant',
        'hbar': 'reduced planck constant'},
    'Thermal energy': {
        'E': 'energy', 'k_B': 'boltzmann constant', 'T': 'temperature'},
    'Ideal gas law': {
        'P': 'pressure', 'V': 'volume', 'n': 'amount', 'R': 'gas constant',
        'T': 'temperature'},
    'Heat capacity': {
        'Q': 'energy', 'm': 'mass', 'c_p': 'dimensionless', 'T': 'temperature'},
    'Stefan-Boltzmann law': {
        'j': 'flux', 'sigma': 'stefan-boltzmann constant', 'T': 'temperature'},
    'Density': {'rho': 'density', 'm': 'mass', 'V': 'volume'},
    'Hydrostatic pressure': {
        'P': 'pressure', 'rho': 'density', 'g': 'gravitational field',
        'h': 'length'},
    "Ohm's law": {'V': 'voltage', 'I': 'current', 'R': 'resistance'},
    'Electrical power': {'P': 'power', 'V': 'voltage', 'I': 'current'},
    'Capacitor charge': {'Q': 'charge', 'C': 'capacitance', 'V': 'voltage'},
    'Schwarzschild radius': {
        'r_s': 'length', 'G': 'gravitational constant', 'M': 'mass',
        'c': 'speed of light'},
    'Planck length': {
        'ell_P': 'length', 'hbar': 'reduced planck constant',
        'G': 'gravitational constant', 'c': 'speed of light'},
    "Hubble's law": {
        'v': 'speed', 'H_0': 'hubble parameter', 'D': 'length'},
    'Debye length': {
        'lambda_D': 'length', 'epsilon_0': 'permittivity',
        'k_B': 'boltzmann constant', 'T': 'temperature',
        'n': 'number density', 'e': 'elementary charge'},
    'Plasma frequency': {
        'omega_p': 'angular frequency', 'n': 'number density',
        'e': 'elementary charge', 'epsilon_0': 'permittivity',
        'm_e': 'mass'},
    'Pythagorean theorem': {
        'a': 'length', 'b': 'length', 'c': 'length'},

    # -- tilings, geometry and the string --------------------------------
    #
    # Three of these tables exist only to be read, not to be joined: an
    # equation the algebra has refused cannot be solved for anything, so its
    # readings buy no derivations.  They are here because the appendix prints
    # this table as the library's statement of what its letters mean, and an
    # equation that declines to say is a gap in that statement rather than a
    # saving.

    'Golden ratio': {'phi': 'golden ratio'},
    'Inflation quadratic': {'lambda': 'inflation factor'},
    'Penrose tile ratio': {
        'N_f': 'tile count', 'phi': 'golden ratio', 'N_t': 'tile count'},
    'Inflation of area': {
        'A_prime': 'patch area', 'phi': 'golden ratio', 'A': 'patch area'},
    'Spectre inflation quadratic': {'mu': 'inflation factor'},
    'Spectre inflation factor': {'mu': 'inflation factor'},
    'Spectre reciprocal pair': {
        'g': 'tile frequency', 'mu': 'inflation factor'},
    'Spectre triplet frequency': {'g': 'tile frequency'},
    'Spectre frequency ratio': {
        'v_Theta': 'tile frequency', 'v_Gamma': 'tile frequency',
        'mu': 'inflation factor'},
    'Spectre count recurrence': {
        'N_prime_prime': 'tile count', 'N_prime': 'tile count',
        'N': 'tile count'},
    'Spectre tile area': {
        'A': 'tile area', 'a': 'length', 'b': 'length'},
    'Hat inflation quadratic': {'kappa': 'inflation factor'},
    'Hat inflation factor': {'kappa': 'inflation factor'},
    'Hat constant as a golden power': {
        'kappa': 'inflation factor', 'phi': 'golden ratio'},
    'Hat chirality ratio': {
        'N_u': 'tile count', 'N_r': 'tile count', 'kappa': 'inflation factor'},
    'Hat tile area': {'A_H': 'tile area'},
    'Euler characteristic of a closed surface': {
        'chi': 'euler characteristic', 'g': 'genus'},
    'Riemann-Hurwitz (unbranched)': {
        'chi_C': 'euler characteristic', 'n': 'covering degree',
        'chi_B': 'euler characteristic'},
    'Gauss-Bonnet theorem': {
        'K': 'gaussian curvature', 'k_g': 'geodesic curvature',
        'pi': 'pi', 'chi': 'euler characteristic'},
    'Mean curvature': {
        'H': 'mean curvature', 'kappa_1': 'principal curvature',
        'kappa_2': 'principal curvature'},
    'Minimal surface condition': {'H': 'mean curvature'},
    'Minimal surface equation': {'u_x': 'slope', 'u_y': 'slope'},
    'Catenoid': {'r': 'length', 'c': 'length', 'z': 'length'},
    'Area functional': {'A': 'area'},
    'Kakeya conjecture': {'n': 'hausdorff dimension'},
    'Perron tree bound': {
        'A': 'area', 'C': 'dimensionless', 'n': 'count'},
    'Nambu-Goto action': {'S': 'action', 'T': 'string tension'},
    'String tension': {
        'T': 'string tension', 'pi': 'pi', 'alpha_prime': 'regge slope'},
    'Regge trajectory': {
        'J': 'spin', 'alpha_prime': 'regge slope', 'M': 'mass',
        'alpha_0': 'dimensionless'},
    'String length': {'ell_s': 'length', 'alpha_prime': 'regge slope'},
    'Genus expansion': {
        'Z': 'partition function', 'chi': 'euler characteristic',
        'g_s': 'string coupling'},
    'Critical dimension': {'D': 'spacetime dimension'},
    'Hagedorn temperature': {
        'T_H': 'temperature', 'pi': 'pi', 'alpha_prime': 'regge slope',
        'k_B': 'boltzmann constant'},
}


_SYMBOL_CACHE = {}


def _symbols_present(eq):
    """Every symbol name in an equation, parsed once and remembered."""
    key = eq['name']
    if key not in _SYMBOL_CACHE:
        try:
            _SYMBOL_CACHE[key] = set(read_relation(eq['latex']).symbols())
        except Unreadable:
            _SYMBOL_CACHE[key] = set()
    return _SYMBOL_CACHE[key]


def resolve_feature(eq, feature):
    r"""Which symbol of `eq` a signature feature names.

    The two vocabularies disagree about subscripts.  A signature says
    'epsilon', because the classifier that reads a drawn formula folds the
    subscript away; the algebra says 'epsilon_0', because m_1 and m_2 are two
    masses and the subscript is part of the name.  Where they disagree the
    join machinery used to fail silently -- solve() looked for a symbol called
    'epsilon', found none, and returned None -- so Coulomb's law and the Debye
    length could never be joined on a constant they both state.

    Folding the subscript back is only safe for a constant, and the reason is
    worth stating.  There is one permittivity of free space, so the epsilon_0
    in Coulomb's law and the epsilon_0 in the Debye length are the same number
    and equating them assumes nothing.  There are many energies.  Resolving
    'E' to whichever energy an equation happens to mention produces

        m c^2 = 1/2 m v^2

    which identifies a rest energy with a kinetic one, and

        1/2 m v^2 = k_B T

    which looks like equipartition and is wrong by three halves -- the worse of
    the two, because a reader might not stop.  Requiring the same letter was
    never really about letters: it was a proxy for the two equations meaning
    the same *instance*, and for anything but a constant the proxy is all there
    is.  So the fold is allowed exactly where instance identity is free.

    Ambiguity is refused outright.  Newton's law of gravitation has m_1 and
    m_2, and 'm' names neither of them.
    """
    name = _term_name(feature)
    present = _symbols_present(eq)
    if name in present or not present:
        return name
    hits = [s for s in present if s.split('_')[0] == name]
    if len(hits) != 1:
        return name                  # absent, or two candidates: refuse
    quantity = READINGS.get(eq['name'], {}).get(hits[0])
    entry = QUANTITIES.get(quantity) if quantity else None
    if entry is None or not entry.is_constant:
        return name
    return hits[0]


def reading(eq, quantity):
    """What `eq` takes a symbol to denote, or None if it does not say."""
    eq = _as_equation(eq)
    table = READINGS.get(eq['name'], {})
    return table.get(resolve_feature(eq, quantity))


def agree(a, b, quantity):
    """Do two equations read the same glyph the same way?

    Both must say so.  An equation that has not declared its readings is not
    agreeing with anything, and the join is refused -- which is the whole
    point of the table.
    """
    left = reading(a, quantity)
    right = reading(b, quantity)
    return left is not None and left == right


def disagreements(graph=None):
    """Every pivot two equations share by spelling but not by meaning.

    This is the interesting output of the whole exercise: a list of the places
    where physics reuses a letter, generated rather than remembered.
    """
    graph = graph or GRAPH
    equations = graph.of_kind('equation')
    out = []
    for i, a in enumerate(equations):
        for b in equations[i + 1:]:
            for q in shared_quantities(a, b, interesting=False):
                left, right = reading(a, q), reading(b, q)
                if left and right and left != right:
                    out.append((a, b, q, left, right))
    return out


# ------------------------------------------------------------------- graph
#
# The tables above say what each thing is; this says how they connect.  Most
# edges are derived rather than written down -- an equation's signature already
# names the symbols it uses, and two equations that mention the same quantity
# are related whether or not anyone noticed -- so the graph grows on its own as
# entries are added, which is the point of deriving it.
#
# The edges that cannot be derived are the interesting ones: that the
# time-independent Schrodinger equation is a special case of the time-dependent
# one is a fact about physics, not about notation, so it is stated in LINKS.


class Graph:
    """Nodes and typed edges, with the walks the rest of the project needs."""

    def __init__(self):
        self.nodes = {}                   # key -> Node
        self.edges = []

    def add(self, node):
        self.nodes[node.key] = node
        return node

    def get(self, key):
        return self.nodes.get(key)

    def find(self, label, kind=None):
        """A node by its human label, searched across kinds or within one."""
        for node in self.nodes.values():
            if kind and node.kind != kind:
                continue
            if node.label == label or node[node.key_field] == label:
                return node
        return None

    def link(self, kind, src, dst, note=''):
        """Join two nodes.  Silently ignores a link to a node we do not have."""
        if src is None or dst is None or src is dst:
            return None
        edge = Edge(kind, src, dst, note)
        self.edges.append(edge)
        src.out.append(edge)
        dst.inn.append(edge)
        return edge

    def of_kind(self, kind):
        return [n for n in self.nodes.values() if n.kind == kind]

    def neighbours(self, node, kinds=None):
        """Every node one edge away, in either direction."""
        out = []
        for edge in node.out + node.inn:
            if kinds and edge.kind not in kinds:
                continue
            other = edge.dst if edge.src is node else edge.src
            if other is not node and other not in out:
                out.append(other)
        return out

    def path(self, start, goal, kinds=None, limit=6):
        """A shortest chain of nodes from one to another, or None.

        Breadth first, so the chain it finds is the shortest -- which matters
        when the chain is about to become a derivation, because a longer route
        between the same two equations is a worse explanation of why they are
        connected, not a different one.
        """
        if start is goal:
            return [start]
        seen = {id(start): None}
        frontier = [start]
        for _ in range(limit):
            nxt = []
            for node in frontier:
                for other in self.neighbours(node, kinds):
                    if id(other) in seen:
                        continue
                    seen[id(other)] = node
                    if other is goal:
                        chain = [other]
                        while seen[id(chain[-1])] is not None:
                            chain.append(seen[id(chain[-1])])
                        return list(reversed(chain))
                    nxt.append(other)
            if not nxt:
                break
            frontier = nxt
        return None

    def edge_between(self, a, b, kind=None):
        for edge in a.out + a.inn:
            if kind and edge.kind != kind:
                continue
            if edge.src is b or edge.dst is b:
                return edge
        return None

    def census(self):
        kinds = {}
        for edge in self.edges:
            kinds[edge.kind] = kinds.get(edge.kind, 0) + 1
        return kinds

    def __repr__(self):
        return '<Graph %d nodes, %d edges>' % (len(self.nodes), len(self.edges))


# ---------------------------------------------------------------- features
#
# The classifier in rosettaui turns LaTeX into the feature names an equation's
# signature is written in.  The graph needs the same vocabulary to decide what
# two equations have in common, but it must not import rosettaui -- the
# dependency runs the other way -- so the part that matters here, the bare
# symbol names, is recovered from the signatures themselves.

def quantities(eq):
    """The physical quantities in a signature: features that are not 'S:' tags.

    These are what two equations can meaningfully share.  A shared 'S:frac' says
    only that both happen to be written as a fraction; a shared 'E' says both
    are talking about energy, which is a fact worth an edge.
    """
    return [f for f in eq.features() if not f.startswith('S:')]


def structures(eq):
    """The structural half of a signature: 'S:frac', 'S:nabla2' and friends."""
    return [f[2:] for f in eq.features() if f.startswith('S:')]


# Quantities too common to mean anything.  Two equations both mentioning m are
# not thereby related; nearly every equation in mechanics mentions m.  Pivoting
# a derivation on one of these produces a true statement that explains nothing,
# which is worse than no statement at all.
#
# The list predates the readings table, and was doing two jobs at once: keeping
# out pivots that are uninformative, and keeping out pivots that are ambiguous.
# agree() does the second job now and does it properly, so what is left here
# should only be the first.  Measured against the current library, m suppresses
# twenty-one statements, k and pi eight each and r three, and every one of them
# is either vacuous or unwarranted -- so those stay.
#
# f was different.  It suppressed exactly one statement, omega / 2 pi = v /
# lambda, which relates an angular frequency to a wave speed and is precisely
# the kind of thing the library is for.  A letter that blocks one good join and
# nothing else is not earning its place, so f is gone.
#
# t, x, i, d and a currently suppress nothing at all.  They are kept as a guard
# for entries not yet written, which is a judgement rather than a measurement,
# and worth revisiting if the list ever has to be defended.
COMMON = {'m', 'r', 't', 'x', 'n', 'k', 'pi', 'i', 'd', 'a', 'partial'}


def shared_quantities(a, b, interesting=True):
    """What two equations have in common, most specific first."""
    common = [q for q in quantities(a) if q in quantities(b)]
    if interesting:
        common = [q for q in common if q not in COMMON]
    # a quantity that names the subject of both equations is the better pivot,
    # so rank by how rare it is across the whole library
    return sorted(common, key=lambda q: _rarity.get(q, 0))


_rarity = {}


def _rank_quantities():
    _rarity.clear()
    for eq in EQUATIONS:
        for q in quantities(eq):
            _rarity[q] = _rarity.get(q, 0) + 1


# --------------------------------------------------------- hand-made edges
#
# Relations between equations that no amount of reading the notation would
# reveal.  (source, relation, target, note) -- the note is the sentence the
# derivation prints when it walks across this edge.

LINKS = [
    ('Schrodinger equation (time-independent)', SPECIALISES,
     'Schrodinger equation (time-dependent)',
     'separating the time dependence of a stationary state leaves an '
     'eigenvalue problem in space alone'),
    ('Wave equation (box form)', SPECIALISES, 'Klein-Gordon equation',
     'the massless case: with m = 0 the Klein-Gordon mass term vanishes and '
     'nothing but the d\'Alembertian is left'),
    ("d'Alembert operator", DEFINES, 'Wave equation (box form)',
     'the box is what makes the one-symbol form of the wave equation mean '
     'anything -- it is an abbreviation, not a new idea'),
    ("Laplace's equation", SPECIALISES, "Poisson's equation",
     'the source-free case: Laplace is Poisson with the density set to zero'),
    ('Helmholtz equation', SPECIALISES, 'Wave equation',
     'separating out a single frequency turns the wave equation into a '
     'condition on the spatial part alone'),
    ('Wave equation', FIELD, 'Heat / diffusion equation',
     'the same Laplacian, set equal to a second time derivative rather than a '
     'first -- which is the whole difference between propagating and diffusing'),
    ('Boltzmann entropy', DEFINES, 'Shannon entropy',
     'counting microstates and counting messages are the same sum, differing '
     'only in the base of the logarithm and a constant'),
    ('Bekenstein-Hawking entropy', SPECIALISES, 'Boltzmann entropy',
     'a black hole obeys the same entropy law as a gas, but the microstates '
     'being counted scale with horizon area rather than with volume'),
    ('Schwarzschild radius', SPECIALISES, 'Einstein field equations',
     'the radius falls out of the spherically symmetric vacuum solution'),
    ('Planck relation', DEFINES, 'de Broglie relation',
     'the same Planck constant, read the other way round: if a wave carries '
     'energy in quanta then a particle carries a wavelength'),
    ('Continuity equation', SPECIALISES, 'Ampere-Maxwell law',
     'taking the divergence of the Ampere-Maxwell law forces charge '
     'conservation -- which is why the displacement current had to be there'),
    ('Lorentz factor', DEFINES, 'Mass-energy equivalence',
     'gamma is what the rest energy gets multiplied by once the body moves'),
    ('Surface gravity', SPECIALISES, "Newton's law of gravitation",
     'dividing out the falling mass leaves an acceleration that does not '
     'depend on what is falling, which is the equivalence principle in its '
     'oldest form'),
    ('Gravitational potential energy', LIMIT_OF, 'Surface gravity',
     'm g h is the work done against a gravity treated as constant, which it '
     'is to excellent accuracy over any height small against the radius'),
    ('Compton wavelength', DEFINES, 'Planck relation',
     'the wavelength at which a photon carries exactly a particle\'s rest '
     'energy, which is where relativity and quantum mechanics stop being '
     'separable'),
    ('Momentum', SPECIALISES, "Newton's second law",
     'force is the rate of change of momentum, and m a is that rate when the '
     'mass is what stays constant'),
    ('Work done by a force', DEFINES, 'Kinetic energy',
     'integrating force over distance is what produces the half and the '
     'square -- the energy laws are the force laws, integrated'),
    ("Hooke's law", SPECIALISES, 'Work done by a force',
     'a restoring force linear in displacement stores energy quadratic in it'),
    ('Escape velocity', SPECIALISES, 'Schwarzschild radius',
     'setting the escape velocity to c gives the Schwarzschild radius exactly '
     '-- a coincidence of the Newtonian derivation rather than a proof of the '
     'relativistic one'),
    ('Planck length', DEFINES, 'Bekenstein-Hawking entropy',
     'the horizon area measured in Planck areas is the microstate count, '
     'which is what makes the entropy a number rather than a scale'),
    ('Thermal energy', DEFINES, 'Ideal gas law',
     'the gas law is thermal energy counted per mole rather than per '
     'particle, which is the whole difference between R and k_B'),
    ('Electrical power', SPECIALISES, "Ohm's law",
     'substituting one into the other gives the two forms every electronics '
     'text reaches for next, P = I^2 R and P = V^2 / R'),
    ('Hydrostatic pressure', SPECIALISES, 'Density',
     'the pressure at a depth is the weight of the column above it, so the '
     'density is doing the same job it does in its own definition'),
    ('Angular frequency', DEFINES, 'Planck relation',
     'writing the Planck relation with omega rather than nu is what turns h '
     'into hbar; the two pi has to go somewhere'),
    ('Wave speed', DEFINES, 'de Broglie relation',
     'a wavelength is only meaningful for something that travels, and this is '
     'the relation that says how fast'),
    ("Hubble's law", FIELD, 'Friedmann equation',
     'the Friedmann equation is what H obeys; Hubble\'s law is what H means'),

    # -- tilings, geometry and the string --------------------------------

    ('Golden ratio', SPECIALISES, 'Inflation quadratic',
     'the surd is the solution of the quadratic; the quadratic is what the '
     'number is for'),
    ('Inflation of area', DEFINES, 'Golden ratio',
     'inflation scales lengths by phi, so it scales areas by phi squared -- '
     'the same constant, one dimension up'),
    ('Spectre inflation factor', SPECIALISES, 'Spectre inflation quadratic',
     'the surd is the larger root of the quadratic; the quadratic is what the '
     'number is for'),
    ('Spectre triplet frequency', SPECIALISES, 'Spectre inflation quadratic',
     'and this is the smaller root of the same quadratic, which is why the '
     'two are reciprocal without anyone arranging it'),
    ('Spectre reciprocal pair', DEFINES, 'Spectre inflation quadratic',
     'the constant term of the quadratic is one, so the product of its roots '
     'is one -- the reciprocal relation is read straight off the polynomial'),
    ('Spectre count recurrence', DEFINES, 'Spectre inflation quadratic',
     'the recurrence has the inflation quadratic as its characteristic '
     'polynomial, which is why counts grow like powers of the larger root '
     'while staying whole numbers'),
    ('Spectre inflation quadratic', FIELD, 'Inflation quadratic',
     'the same statement for the one-tile system that the golden ratio makes '
     'for the two-tile one: an inflation factor is a quadratic irrational '
     'either way, and the irrationality is the whole obstruction to a period'),
    ('Hat tile area', SPECIALISES, 'Spectre tile area',
     'the hat is the member of the family with a = 1 and b = root three; '
     'swapping the two lengths gives the turtle and a different area, which '
     'is the asymmetry the formula records'),
    ('Riemann-Hurwitz (unbranched)', SPECIALISES,
     'Euler characteristic of a closed surface',
     'a cover has n times the Euler characteristic of what it covers, so by '
     'chi = 2 - 2g it also has n times the handles, less n - 1 of them'),
    ('Gauss-Bonnet theorem', DEFINES,
     'Euler characteristic of a closed surface',
     'the integral of curvature over a closed surface is 2 pi chi, which is '
     'what makes a topological count something a ruler can measure'),
    ('Mean curvature', DEFINES, 'Minimal surface condition',
     'minimal means H = 0, and this is what H is'),
    ('Minimal surface equation', SPECIALISES, 'Minimal surface condition',
     'the same condition written out for a surface given as a height above '
     'the plane, where it becomes a quasilinear partial differential equation'),
    ('Catenoid', SPECIALISES, 'Minimal surface equation',
     'the rotationally symmetric solution, and the first minimal surface found '
     'that was not the plane'),
    ('Area functional', DEFINES, 'Minimal surface equation',
     'setting the first variation of the area integral to zero is where the '
     'minimal surface equation comes from'),
    ('Perron tree bound', SPECIALISES, 'Kakeya conjecture',
     'the Perron construction settles the measure -- it can be made as small '
     'as you like -- and leaves open the dimension, which is what the '
     'conjecture is about'),
    ('Nambu-Goto action', FIELD, 'Area functional',
     'the same variational problem in a different signature: a soap film '
     'extremises area in Euclidean space, a string extremises area in '
     'Minkowski spacetime, and the minus sign under the root is the only '
     'difference the mathematics sees'),
    ('String tension', DEFINES, 'Nambu-Goto action',
     'the T multiplying the worldsheet area is this tension, and writing it '
     'as one over two pi alpha prime is what introduces the only free '
     'parameter the string has'),
    ('String length', DEFINES, 'String tension',
     'alpha prime is a length squared, so the tension is an inverse area -- '
     'in natural units, the only scale in the theory'),
    ('Euler characteristic of a closed surface', DEFINES, 'Genus expansion',
     'the coupling is raised to minus the Euler characteristic, so chi = 2 - '
     '2g is what turns a sum over surfaces into an expansion ordered by loops'),
    ('Hagedorn temperature', FIELD, 'Boltzmann entropy',
     'counting string states is counting microstates, and they grow '
     'exponentially with energy -- fast enough that above this temperature the '
     'sum defining the partition function stops converging'),
]


def _build_graph():
    """Assemble the graph from the tables.  Idempotent; safe to call again."""
    g = Graph()
    for entry in SYMBOLS.values():
        entry.out, entry.inn = [], []
        g.add(entry)
    for entry in CONCEPTS.values():
        entry.out, entry.inn = [], []
        g.add(entry)
    for eq in EQUATIONS:
        eq.out, eq.inn = [], []
        g.add(eq)

    _rank_quantities()

    # concepts -> what they talk about
    for concept in CONCEPTS.values():
        for latex in concept['symbols']:
            g.link(MENTIONS, concept, SYMBOLS.get(latex))
        for name in concept['equations']:
            g.link(CITES, concept, g.find(name, 'equation'))

    for entry in QUANTITIES.values():
        entry.out, entry.inn = [], []
        g.add(entry)

    # equations -> the physical quantities their letters denote.  This is the
    # edge that makes the graph about physics rather than about spelling.
    for eq in EQUATIONS:
        for symbol, name in sorted(READINGS.get(eq['name'], {}).items()):
            g.link(DENOTES, eq, QUANTITIES.get(name), symbol)

    # equations -> the symbols in their signatures
    for eq in EQUATIONS:
        for q in quantities(eq):
            target = _symbol_for(q)
            if target is not None:
                g.link(USES, eq, target, 'must' if q in eq.get('must', ())
                       else 'nice')

    # equations -> equations, wherever they share a telling quantity
    for i, a in enumerate(EQUATIONS):
        for b in EQUATIONS[i + 1:]:
            common = shared_quantities(a, b)
            if common:
                g.link(SHARES, a, b, common[0])

    # and the relations that had to be stated
    for src, kind, dst, note in LINKS:
        g.link(kind, g.find(src, 'equation'), g.find(dst, 'equation'), note)

    return g


def _symbol_for(feature):
    r"""The symbol entry a feature name refers to: 'hbar' -> \hbar, 'E' -> E."""
    if feature in SYMBOLS:                       # a bare Latin letter
        return SYMBOLS[feature]
    return SYMBOLS.get('\\' + feature)           # a Greek or named command


GRAPH = _build_graph()


def rebuild():
    """Re-derive the graph after entries have been added at runtime."""
    global GRAPH
    _SYMBOL_CACHE.clear()        # an entry may have been added or reworded
    GRAPH = _build_graph()
    return GRAPH


# ------------------------------------------------------------- derivations
#
# Two equations that share a quantity can be joined into one.  If both state
# something about E, then whatever each says E equals must be equal to each
# other -- transitivity, which is the only inference this module makes, and the
# reason a composed statement is a conjecture worth checking rather than a
# guess.
#
#     E = m c^2   and   E = h \nu      share E
#     ->  m c^2 = h \nu
#
# Written out, the join keeps its provenance.  The underbrace under each side
# names the equation it came from; the overbrace over the whole statement names
# the quantity that was eliminated to make it.  Neither is decoration: they are
# what lets the reader -- and rosettalean.py -- recover the derivation from the
# formula.

class Step:
    """One equation in a chain, and the pivot that got us here."""

    __slots__ = ('equation', 'pivot', 'expr', 'note', 'direct',
                 'expr_term')

    def __init__(self, equation, pivot=None, expr=None, note='', direct=True):
        self.equation = equation
        self.pivot = pivot            # the quantity shared with the step before
        self.expr = expr              # what this equation says the pivot equals
        self.note = note
        # False when the equation had to be rearranged to say it.  Worth
        # recording separately from the expression, because a quoted equation
        # and a rearranged one are believable to different degrees and the
        # reader deserves to be told which they are looking at.
        self.direct = direct
        self.expr_term = None         # the Term behind expr, when we have it

    def __repr__(self):
        return '<Step %s via %s>' % (self.equation.label, self.pivot)


class Derivation:
    """A chain of equations joined on shared quantities.

    The chain is the object the rest of the pipeline works on: it renders to a
    single annotated LaTeX statement, and rosettalean.py turns that same chain
    into a Lean conjecture.  Building it is deliberately separate from checking
    it -- a chain can be assembled that is not true, and finding that out is
    the job of the kernel, not of this file.
    """

    def __init__(self, steps=(), pivot=None, quantity=None):
        self.steps = list(steps)
        self.pivot = pivot            # the letter the chain turns on
        # the physical quantity that letter denotes, when the equations say.
        # Preferred in captions: 'all six equal the gravitational constant' is
        # a statement about physics, 'all six equal G' is one about spelling.
        self.quantity = quantity

    @property
    def equations(self):
        return [s.equation for s in self.steps]

    def latex(self, braces=True, relation='='):
        """The chain as one statement.

        With braces, every side carries the name of the equation it came from
        and the whole carries the eliminated quantity -- so the statement says
        where it came from as well as what it claims.
        """
        if len(self.steps) < 2:
            return self.steps[0].equation['latex'] if self.steps else ''
        parts = []
        for step in self.steps:
            body = step.expr or step.equation['latex']
            if braces:
                parts.append(r'\underbrace{%s}_{\text{%s}}'
                             % (body, _tex_escape(step.equation.label)))
            else:
                parts.append(body)
        joined = (' %s ' % relation).join(parts)
        if braces and self.pivot:
            joined = r'\overbrace{%s}^{\text{%s}}' % (
                joined, _tex_escape(self.caption()))
        return joined

    def caption(self):
        """What the overbrace over the whole statement says."""
        word = 'both' if len(self.steps) == 2 else 'all %d' % len(self.steps)
        return '%s equal the %s' % (word, self.name())

    def name(self):
        """What the chain is about, in words."""
        return self.quantity or _pretty(self.pivot)

    def aligned(self, per_line=1):
        r"""The chain as an align* body, one equation to a line.

        A six-way chain does not fit across a page, and breaking it by hand is
        how a generated document starts disagreeing with the data that
        generated it.  The pivot leads, so every line reads as a statement
        about the same quantity rather than as a fragment of a longer one.
        """
        lines = [r'%s &= \underbrace{%s}_{\text{%s}}'
                 % (_pivot_tex(self.pivot), step.expr,
                    _tex_escape(step.equation.label))
                 for step in self.steps]
        return ' \\\\\n'.join(lines)

    def statement(self):
        """The bare claim, with no provenance -- what has to be true."""
        return self.latex(braces=False)

    def prose(self, math='%s'):
        """Why the chain holds, one sentence per join.

        `math` wraps every expression, so a caller that is writing LaTeX can
        pass '$%%s$' and get typeset formulae instead of raw source in the
        middle of a sentence.
        """
        lines = []
        for i, step in enumerate(self.steps):
            if i == 0:
                lines.append('%s gives %s for the %s.'
                             % (step.equation.label, math % step.expr,
                                self.name()))
            else:
                lines.append('%s gives %s for the same quantity.'
                             % (step.equation.label, math % step.expr))
                if step.note:
                    lines.append('(%s)' % step.note)
        lines.append('Every expression here denotes the %s, so they are all '
                     'equal.' % self.name())
        rearranged = [s.equation.label for s in self.steps if not s.direct]
        if rearranged:
            lines.append('(%s had to be rearranged to say so; the join is only '
                         'as good as that rearrangement.)'
                         % ' and '.join(rearranged))
        return ' '.join(lines)

    @property
    def rearranged(self):
        """The steps that needed algebra rather than quotation."""
        return [s for s in self.steps if not s.direct]

    def symbols(self):
        """Every free quantity appearing anywhere in the chain."""
        out = []
        for step in self.steps:
            for q in quantities(step.equation):
                if q not in out:
                    out.append(q)
        return out

    def __len__(self):
        return len(self.steps)

    def __repr__(self):
        return '<Derivation %s on %s>' % (
            ' = '.join(s.equation.label for s in self.steps), self.pivot)



def pivot_tex(quantity):
    """How a pivot should be written for a human: 'alpha_prime' -> \\alpha'.

    Public because the internal name is not fit to print. Anything that shows a
    pivot to a reader -- a caption, a Lean comment, a derivation note -- goes
    through here, so that the spelling the algebra uses internally stays
    internal.
    """
    return _pivot_tex(quantity)


def _pivot_tex(quantity):
    """The pivot as it should be typeset: 'hbar' -> \\hbar, 'alpha_prime' -> \\alpha'.

    The primes come off before the lookup and go back on after it, because the
    symbol table knows \\alpha and has never heard of alpha_prime -- and left
    alone the name would typeset as an italic alpha subscripted with the word
    prime, which is not what anybody wrote.
    """
    name = quantity or ''
    primes = 0
    while name.endswith('_prime'):
        name = name[:-len('_prime')]
        primes += 1
    entry = _symbol_for(name) if name else None
    base = entry['latex'] if entry is not None else (name or '?')
    return base + "'" * primes


def _tex_escape(text):
    """A label going inside \\text{} -- the characters that would break it."""
    for bad, good in (('\\', r'\textbackslash{}'), ('_', r'\_'),
                      ('^', r'\^{}'), ('{', r'\{'), ('}', r'\}'),
                      ('&', r'\&'), ('%', r'\%'), ('#', r'\#'), ('$', r'\$')):
        text = text.replace(bad, good)
    return text


def _pretty(quantity):
    """A feature name as it would be read aloud: 'hbar' -> 'h-bar'.

    Overloaded letters are documented with every reading they have -- E is
    "Energy / electric field" -- but a label on a brace has room for one, and
    the first is the one the entry leads with.
    """
    entry = _symbol_for(quantity) if quantity else None
    if entry is None:
        return quantity or '?'
    return entry['name'].split('/')[0].strip()


# ---------------------------------------------------------------- tidying
#
# Rearranging piles up structure that is correct and unreadable: solving
# F = G m_1 m_2 / r^2 for G gives F over (m_1 m_2 over r^2), a fraction of a
# fraction that no physicist would write.
#
# Only rewrites that hold for every value go in here.  Cancelling the b in
# a b / b is *not* one of them -- it needs b non-zero, and the equation does
# not say so -- and leaving it out is the same decision as refusing even roots:
# the output stays something the reader can check rather than something they
# have to trust.

def simplify(term, depth=0):
    """Tidy a Term using rewrites that are unconditionally valid."""
    if depth > 32 or not isinstance(term, (Op, Call)):
        return term
    if isinstance(term, Call):
        inner = simplify(term.arg, depth + 1)
        # exp(log x) and log(exp x) are x only where x is positive, so they
        # are left alone; sqrt(x^2) is |x|, likewise
        return Call(term.func, inner)
    op = term.op
    args = tuple(simplify(a, depth + 1) for a in term.args)
    if op == 'neg':
        inner = args[0]
        if isinstance(inner, Op) and inner.op == 'neg':
            return inner.args[0]
        return Op('neg', inner)
    if op == 'mul':
        a, b = args
        if a == Num('1'):
            return b
        if b == Num('1'):
            return a
        if isinstance(b, Num) and not isinstance(a, Num):
            a, b = b, a          # 'M 2' is written '2 M'; reals commute
        if (isinstance(b, Op) and b.op == 'mul'
                and isinstance(b.args[0], Num) and not isinstance(a, Num)):
            a, b = b.args[0], Op('mul', a, b.args[1])      # 'rho 8 pi' -> '8 rho pi'
        # a (p/q) is one fraction, not a product with a fraction in it
        if isinstance(b, Op) and b.op == 'div':
            return simplify(Op('div', Op('mul', a, b.args[0]), b.args[1]),
                            depth + 1)
        if isinstance(a, Op) and a.op == 'div':
            return simplify(Op('div', Op('mul', a.args[0], b), a.args[1]),
                            depth + 1)
        return Op('mul', a, b)
    if op == 'div':
        a, b = args
        if b == Num('1'):
            return a
        if isinstance(b, Op) and b.op == 'div':
            # a / (p/q) == a q / p, wherever either side is defined at all
            return simplify(Op('div', Op('mul', a, b.args[1]), b.args[0]),
                            depth + 1)
        if isinstance(a, Op) and a.op == 'div':
            # (p/q) / b == p / (q b)
            return simplify(Op('div', a.args[0], Op('mul', a.args[1], b)),
                            depth + 1)
        return Op('div', a, b)
    if op == 'pow':
        base, exponent = args
        if exponent == Num('1'):
            return base
        return Op('pow', base, exponent)
    return Op(op, *args)


# ------------------------------------------------------------ solving

class Solution:
    """What an equation says a quantity equals, and how hard it was to say.

    `direct` matters to the reader: an equation that already states E is being
    quoted, while one that had to be rearranged is being used, and a derivation
    that hides the difference is hiding the only step in it that could be
    wrong.
    """

    __slots__ = ('term', 'direct', 'source')

    def __init__(self, term, direct, source):
        self.term = term
        self.direct = direct
        self.source = source

    @property
    def latex(self):
        return render(self.term)

    def __str__(self):
        return self.latex

    def __repr__(self):
        return '<Solution %s%s>' % (self.latex, '' if self.direct
                                    else ' (rearranged)')


def solve(eq, quantity):
    """A Solution for what `eq` says `quantity` equals, or None.

    The quantity may be named either way round -- 'hbar' or '\\hbar' -- since
    the signatures speak the first dialect and the LaTeX the second.
    """
    eq = _as_equation(eq)
    parts = eq.sides()
    if parts is None:
        return None
    left_tex, relation, right_tex = parts
    if relation != '=':
        return None
    name = resolve_feature(eq, quantity)
    try:
        left = read_term(left_tex)
        right = read_term(right_tex)
    except Unreadable:
        return None
    for near, far in ((left, right), (right, left)):
        if isinstance(near, Sym) and near.name == name:
            return Solution(far, True, eq)
    try:
        return Solution(simplify(isolate(left, right, name)), False, eq)
    except CannotIsolate:
        return None


def solve_for(eq, quantity):
    r"""What an equation says a quantity equals, as LaTeX, or None.

    Kept returning a string because that is what the derivations print, but it
    is now backed by real rearrangement rather than by the quantity happening
    to stand alone.  What it will not do is still worth knowing: see isolate().
    """
    found = solve(eq, quantity)
    return found.latex if found is not None else None


def _term_name(quantity):
    """A feature name or a LaTeX spelling, as the Term algebra spells it."""
    text = str(quantity)
    if text.startswith('\\'):
        text = text[1:]
    return _COMMAND_SYMBOLS.get('\\' + text, text)


def _as_equation(what, graph=None):
    """An Equation, from one or from the name of one."""
    if isinstance(what, Equation):
        return what
    found = (graph or GRAPH).find(what, 'equation')
    if found is None:
        raise KeyError('no equation called %r' % (what,))
    return found


def join(a, b, pivot=None, graph=None):
    """Join two equations on a quantity they share.  None if they cannot be.

    The join only happens when both equations state the pivot directly, which
    is what makes the result follow by transitivity alone.
    """
    graph = graph or GRAPH
    a, b = _as_equation(a, graph), _as_equation(b, graph)
    options = [pivot] if pivot else shared_quantities(a, b)
    for quantity in options:
        if not agree(a, b, quantity):
            continue              # same letter, different quantity, no join
        left = solve(a, quantity)
        right = solve(b, quantity)
        if left is None or right is None:
            continue
        if left.term == right.term:
            # the two equations say the same thing about the pivot, so the
            # join is x = x.  True, and not worth anybody's time
            continue
        edge = graph.edge_between(a, b)
        # a derived SHARES edge notes only the pivot letter; the sentences
        # worth printing are the hand-written ones in LINKS
        note = edge.note if edge is not None and edge.kind != SHARES else ''
        return Derivation([Step(a, quantity, left.latex, direct=left.direct),
                           Step(b, quantity, right.latex, note,
                                direct=right.direct)],
                          pivot=quantity, quantity=reading(a, quantity))
    return None


def chain(*equations, **kw):
    """Join a whole run of equations that all speak about one quantity."""
    graph = kw.get('graph') or GRAPH
    nodes = [_as_equation(e, graph) for e in equations]
    pivot = kw.get('pivot')
    if pivot is None:
        common = None
        for node in nodes:
            here = set(quantities(node))
            common = here if common is None else (common & here)
        common = sorted(common - COMMON) if common else []
        if not common:
            raise ValueError('these equations share no quantity to join on')
        pivot = sorted(common, key=lambda q: _rarity.get(q, 0))[0]
    steps = []
    for node in nodes:
        found = solve(node, pivot)
        if found is None:
            raise ValueError('%s cannot be solved for %s: see isolate() for '
                             'what the algebra declines to do'
                             % (node.label, pivot))
        steps.append(Step(node, pivot, found.latex, direct=found.direct))
    return Derivation(steps, pivot=pivot)




def family(quantity, graph=None, minimum=3):
    """Every equation that states the same quantity, as one chain.

    This is what the graph is for.  Six equations in this library can be solved
    for the gravitational constant -- Newton's, Schwarzschild's, Hawking's, the
    Planck length, the escape velocity and the surface gravity -- and none of
    them was written down with the others in mind.  Chaining them produces a
    single statement that no one entered, and that is the closest this project
    comes to finding something out.

    Only equations that declare the same reading take part, so the chain is
    about a quantity rather than about a letter.
    """
    graph = graph or GRAPH
    name = _term_name(quantity)
    wanted = None
    members = []
    for eq in graph.of_kind('equation'):
        says = reading(eq, name)
        if says is None:
            continue
        if wanted is None:
            wanted = says
        if says != wanted:
            continue
        found = solve(eq, name)
        if found is None:
            continue
        if any(found.term == s.expr_term for s in members):
            continue                 # the same expression twice is no chain
        step = Step(eq, name, found.latex, direct=found.direct)
        step.expr_term = found.term
        members.append(step)
    if len(members) < minimum:
        return None
    return Derivation(members, pivot=name, quantity=wanted)


def families(graph=None, minimum=3):
    """Every quantity the library states in three or more independent ways.

    Deduplicated by membership, not by the letter asked about.  Two symbols can
    now name one family -- k_B is the Boltzmann constant and so is the k of
    Boltzmann entropy, and since resolve_feature() folds the subscript for a
    constant, asking about either builds the same chain.  Counting it twice
    would overstate what the library knows, and the count is quoted in the
    abstract.
    """
    graph = graph or GRAPH
    seen, members, out = set(), set(), []
    for eq in graph.of_kind('equation'):
        for symbol in READINGS.get(eq['name'], {}):
            if symbol in seen:
                continue
            seen.add(symbol)
            chained = family(symbol, graph, minimum)
            if chained is None:
                continue
            who = tuple(sorted(step.equation['name'] for step in chained.steps))
            if who in members:
                continue
            members.add(who)
            out.append(chained)
    out.sort(key=lambda d: -len(d.steps))
    return out


# --------------------------------------------------------- the whole thing
#
# One display, linking every family the library knows.  It exists because the
# graph makes it possible to ask a question no single entry answers: if every
# equation here is true at once, what does that say?
#
# Fitting it on a page is the constraint that shapes everything below.  Full
# equation names will not go under a brace -- "Newton's law of gravitation" is
# wider than the fraction it labels -- so each entry carries a short form, and
# the short forms have to stay distinct or the display starts lying about
# which equation a term came from.

SHORT = {
    'Mass-energy equivalence': 'mass-energy',
    "Newton's second law": 'Newton II',
    "Newton's law of gravitation": 'Newton grav.',
    "Coulomb's law": 'Coulomb',
    'Coulomb potential energy': 'Coulomb p.e.',
    'Kinetic energy': 'kinetic',
    'Momentum': 'momentum',
    'Work done by a force': 'work',
    'Gravitational potential energy': 'grav. p.e.',
    'Surface gravity': 'surface grav.',
    "Hooke's law": 'Hooke',
    'Escape velocity': 'escape vel.',
    'Angular frequency': 'angular freq.',
    'Wave speed': 'wave speed',
    'Planck relation': 'Planck',
    'de Broglie relation': 'de Broglie',
    'Compton wavelength': 'Compton',
    'Boltzmann entropy': 'Boltzmann',
    'Bekenstein-Hawking entropy': 'Bekenstein-Hawking',
    'Thermal energy': 'thermal',
    'Ideal gas law': 'ideal gas',
    'Heat capacity': 'heat capacity',
    'Stefan-Boltzmann law': 'Stefan-Boltzmann',
    'Density': 'density',
    'Hydrostatic pressure': 'hydrostatic',
    "Ohm's law": 'Ohm',
    'Electrical power': 'elec. power',
    'Capacitor charge': 'capacitor',
    'Schwarzschild radius': 'Schwarzschild',
    'Planck length': 'Planck length',
    "Hubble's law": 'Hubble',
    'Debye length': 'Debye',
    'Plasma frequency': 'plasma freq.',
    'Pythagorean theorem': 'Pythagoras',
    'String tension': 'tension',
    'Regge trajectory': 'Regge',
    'String length': 'string length',
    'Hagedorn temperature': 'Hagedorn',
    'Mean curvature': 'mean curvature',
    'Minimal surface condition': 'minimal',
    'Golden ratio': 'golden ratio',
    'Penrose tile ratio': 'Penrose ratio',
}


def short(eq):
    """A name short enough to sit under a brace.  Falls back to the full one."""
    eq = _as_equation(eq)
    return SHORT.get(eq['name'], eq['name'])


# Which families go into the display, in the order they read best: mechanics
# first, then the quantities that tie mechanics to quantum theory and
# gravitation.  Named rather than computed, because "every family" does not fit
# on a page and choosing by size alone would open with the ugliest one.
GRAND_PIVOTS = ('E', 'F', 'm', 'G', 'h', 'T', 'v', 'g', 'alpha_prime')


def grand(pivots=GRAND_PIVOTS, graph=None, compact=True):
    r"""Every named family as one display: many braces, one side brace.

    Each row is a quantity, overbraced with what it is; each term is an
    expression some equation in the library gives for it, underbraced with
    which. The side brace on the right gathers the rows into a single claim,
    which is the point -- separately these are ordinary formulae, and together
    they are a conjecture about the whole library at once.
    """
    graph = graph or GRAPH
    rows, count = [], 0
    for pivot in pivots:
        chained = family(pivot, graph, minimum=2)
        if chained is None:
            continue
        count += len(chained)
        rows.append(_grand_row(chained, compact))
    if not rows:
        return ''
    body = ' \\\\[1.2ex]\n'.join(rows)
    tally = (r'\begin{array}{l} \text{one conjecture:} \\ '
             r'\text{%d equations, %d quantities} \end{array}'
             % (count, len(rows)))
    return ('\\left.\n\\begin{aligned}\n%s\n\\end{aligned}\n'
            '\\;\\right\\} %s' % (body, tally))


def _grand_row(chained, compact):
    """One quantity, overbraced, equal to everything the library says it is."""
    frac = r'\tfrac' if compact else r'\frac'
    terms = []
    for step in chained.steps:
        expr = step.expr.replace(r'\frac', frac) if compact else step.expr
        terms.append(r'\underbrace{%s}_{\text{\tiny %s}}'
                     % (expr, _tex_escape(short(step.equation))))
    head = r'\overbrace{%s}^{\text{\tiny %s}}' % (
        _pivot_tex(chained.pivot), _tex_escape(chained.name()))
    return '%s &= %s' % (head, ' = '.join(terms))


def grand_members(pivots=GRAND_PIVOTS, graph=None):
    """The (quantity, equations) the display is built from."""
    graph = graph or GRAPH
    out = []
    for pivot in pivots:
        chained = family(pivot, graph, minimum=2)
        if chained is not None:
            out.append(chained)
    return out


def joins_for(eq, graph=None):
    """Every equation this one can actually be joined to, and on what."""
    graph = graph or GRAPH
    out = []
    for other in graph.of_kind('equation'):
        if other is eq:
            continue
        derivation = join(eq, other, graph=graph)
        if derivation is not None:
            out.append((other, derivation.pivot))
    return out


def all_joins(graph=None):
    """Every joinable pair in the library -- what the graph makes available."""
    graph = graph or GRAPH
    equations = graph.of_kind('equation')
    out = []
    for i, a in enumerate(equations):
        for b in equations[i + 1:]:
            derivation = join(a, b, graph=graph)
            if derivation is not None:
                out.append(derivation)
    return out


def ungated_joins(graph=None):
    """Every pair that would join if nobody checked what the letters mean.

    This is the library as it was before the readings table: a pivot is any
    quantity both equations state, and whether they mean the same thing by it
    is not asked.  The difference between this count and all_joins() is what
    declaring the readings actually bought, which is a number the paper would
    otherwise have to be told.
    """
    graph = graph or GRAPH
    equations = graph.of_kind('equation')
    out = []
    for i, a in enumerate(equations):
        for b in equations[i + 1:]:
            for quantity in shared_quantities(a, b):
                left = solve(a, quantity)
                right = solve(b, quantity)
                if left is None or right is None:
                    continue
                if left.term == right.term:
                    continue
                out.append((a, b, quantity))
                break
    return out


def quantity_joins(graph=None):
    """What pivoting on quantities instead of letters would make available.

    Not used to build anything.  It exists so the paper can report the size of
    an alternative design rather than assert it, and so that anyone tempted by
    that design can see its output before adopting it.

    The rule here is the permissive one: two equations may be joined whenever
    each declares *some* letter to denote the same quantity, regardless of
    whether the letters match.  It is what the Hagedorn temperature seems to
    ask for, since it writes T_H where the gas laws write T and consequently
    joins to nothing outside its own cluster.  Running it shows why the
    obvious repair is the wrong one: see resolve_feature() for the cases.
    """
    graph = graph or GRAPH
    equations = graph.of_kind('equation')
    out = []
    for i, a in enumerate(equations):
        for b in equations[i + 1:]:
            ta = READINGS.get(a['name'], {})
            tb = READINGS.get(b['name'], {})
            found = None
            for sa, qa in ta.items():
                for sb, qb in tb.items():
                    if qa != qb:
                        continue
                    left, right = solve(a, sa), solve(b, sb)
                    if left is None or right is None:
                        continue
                    if left.term == right.term:
                        continue
                    found = (a, b, qa, sa, sb)
                    break
                if found:
                    break
            if found:
                out.append(found)
    return out


def folded_joins(graph=None):
    """The joins that exist only because a subscript was folded for a constant.

    The difference resolve_feature() made, as a list rather than a claim.
    """
    out = []
    for derivation in all_joins(graph):
        a, b = derivation.equations
        pivot = derivation.pivot
        if (resolve_feature(a, pivot) != _term_name(pivot)
                or resolve_feature(b, pivot) != _term_name(pivot)):
            out.append(derivation)
    return out


def quantity_join_census(graph=None):
    r"""Classify every statement quantity_joins() would add, and why.

    The paper needs to say what the permissive rule is worth, and 'nearly all
    of it is false' is not a measurement.  Truth is also the wrong test: every
    join in this library is an equation between two expressions that holds only
    where both really do equal the pivot, and that is as true of the
    gravitational family as of anything the permissive rule produces.

    The right test is whether the transitivity step is *licensed* -- whether
    the two equations are about the same instance of the pivot quantity.  Three
    outcomes, and the rule for each is stated here rather than left to
    judgement:

        unlicensed  different symbols, and the quantity is not a constant.  The
                    join asserts that two differently named things are the same
                    instance, which nothing in the library says.
        known       the pivot quantity is already recorded as a family, so the
                    library knows it is multiply determined and is suppressing
                    the pairwise statements deliberately.  Nothing is learnt.
        novel       licensed, and about a quantity no family covers.

    Returns the three lists.  If `novel` is ever non-empty, the permissive rule
    is offering something the library actually wants, and COMMON is probably
    the thing standing in the way.
    """
    graph = graph or GRAPH
    today = set()
    for derivation in all_joins(graph):
        a, b = derivation.equations
        today.add(tuple(sorted((a['name'], b['name']))))
    known_quantities = set(f.quantity for f in families(graph))

    unlicensed, known, novel = [], [], []
    for a, b, quantity, sym_a, sym_b in quantity_joins(graph):
        if tuple(sorted((a['name'], b['name']))) in today:
            continue
        entry = QUANTITIES.get(quantity)
        licensed = (entry is not None and entry.is_constant) or sym_a == sym_b
        if not licensed:
            unlicensed.append((a, b, quantity, sym_a, sym_b))
        elif quantity in known_quantities:
            known.append((a, b, quantity, sym_a, sym_b))
        else:
            novel.append((a, b, quantity, sym_a, sym_b))
    return unlicensed, known, novel


# ---------------------------------------------------------------- browsing
#
# Small accessors so callers do not have to know how the tables are shaped.
# rosettaui builds its menus from these; the selftest below uses them too.


def categories():
    """Symbol categories, in the order they were first defined."""
    out = []
    for entry in SYMBOLS.values():
        if entry['category'] not in out:
            out.append(entry['category'])
    return out


def symbols_in(category):
    """Every symbol filed under one category."""
    return [e for e in SYMBOLS.values() if e['category'] == category]


def concept_categories():
    out = []
    for entry in CONCEPTS.values():
        if entry['category'] not in out:
            out.append(entry['category'])
    return out


def concepts_in(category):
    return [e for e in CONCEPTS.values() if e['category'] == category]


def sourced():
    """Entries whose value was computed somewhere nameable, and where.

    These are the entries a reader cannot check against a textbook, because
    the number was derived rather than quoted. Returning them separately is
    what lets the paper print them as a table instead of burying the
    provenance in a blurb.
    """
    return [(eq, eq['source']) for eq in EQUATIONS if eq.get('source')]


def fields():
    """Every field of physics or maths an equation is filed under."""
    out = []
    for eq in EQUATIONS:
        if eq['field'] not in out:
            out.append(eq['field'])
    return out


def equations_in(field):
    return [eq for eq in EQUATIONS if eq['field'] == field]


def lookup(latex):
    """The entry documenting a glyph, or None."""
    return SYMBOLS.get(latex)


def census():
    """How much knowledge is in here, broken down."""
    return {
        'symbols': len(SYMBOLS),
        'symbol categories': len(categories()),
        'concepts': len(CONCEPTS),
        'concept categories': len(concept_categories()),
        'equations': len(EQUATIONS),
        'equation fields': len(fields()),
        'equation families': len(EQUATION_FAMILIES),
        'constants': len(CONSTANTS),
    }


# ------------------------------------------------------- arithmetic checks
#
# Almost nothing in this library can be checked for truth.  An equation with
# free variables is a claim about the world, and the most a module of this kind
# can ask is whether it is well formed -- which is the whole argument of the
# Lean bridge, and the reason its output is called a conjecture.
#
# A few entries are different.  When an equation pins a name to arithmetic over
# numbers alone -- mu = 4 + sqrt15, phi = (1 + sqrt5)/2 -- there is nothing left
# to be true about the world, and any other entry written entirely in those
# names becomes a statement this module can simply evaluate.  That is a small
# corner, but it is the corner where a mistyped surd hides: 4 + sqrt14 parses,
# typechecks, renders and joins exactly as well as the right answer.

class NotDetermined(Exception):
    """This term contains something the arithmetic cannot put a number to."""


_ARITHMETIC = {
    'add': lambda v: v[0] + v[1], 'sub': lambda v: v[0] - v[1],
    'mul': lambda v: v[0] * v[1], 'div': lambda v: v[0] / v[1],
    'pow': lambda v: v[0] ** v[1], 'neg': lambda v: -v[0],
}


def evaluate(term, known=()):
    """A Term as a float, given values for the names it uses.

    Raises rather than guessing.  A name with no value, a function other than
    a square root, or anything opaque means the term is not determined, and a
    caller that wanted a number should be told so rather than handed one.
    """
    if isinstance(term, Num):
        return float(term.text)
    if isinstance(term, Sym):
        if term.name not in known:
            raise NotDetermined(term.name)
        return known[term.name]
    if isinstance(term, Call):
        if term.func != 'sqrt':
            raise NotDetermined(term.func)
        return math.sqrt(evaluate(term.arg, known))
    if isinstance(term, Op):
        return _ARITHMETIC[term.op]([evaluate(a, known) for a in term.args])
    raise NotDetermined(type(term).__name__)


def _both_sides(eq):
    """(left, right) as Terms for an equation the algebra accepts, or None."""
    if algebraic(eq['latex']) is not None:
        return None
    parts = split_relation(eq['latex'])
    if not parts or parts[1] != '=':
        return None
    try:
        return read_term(parts[0]), read_term(parts[2])
    except Unreadable:
        return None


def declared_constants():
    """Names the library pins to a number, and the number.

    An entry qualifies when one side is a bare name and the other is closed
    arithmetic: mu = 4 + sqrt15 qualifies, mu = 4 + sqrt(n) does not.
    """
    out = {}
    for eq in EQUATIONS:
        sides = _both_sides(eq)
        if sides is None:
            continue
        left, right = sides
        if not isinstance(left, Sym) or right.symbols():
            continue
        try:
            out[left.name] = evaluate(right)
        except NotDetermined:
            continue
    return out


def numeric_checks():
    """Entries that are fully determined by declared_constants().

    Yields (equation, left, right) with both sides already evaluated.  A
    definition like mu = 4 + sqrt15 is skipped: it is what supplied the value,
    so checking it against itself proves nothing.
    """
    known = declared_constants()
    out = []
    for eq in EQUATIONS:
        sides = _both_sides(eq)
        if sides is None:
            continue
        left, right = sides
        if isinstance(left, Sym) and not right.symbols():
            continue                      # this is a definition, not a check
        names = set(left.symbols()) | set(right.symbols())
        if not names or not names <= set(known):
            continue
        try:
            out.append((eq, evaluate(left, known), evaluate(right, known)))
        except NotDetermined:
            continue
    return out


# ---------------------------------------------------------------- selftest
#
# The knowledge base is meant to be added to, so the tests here are the kind
# that catch a copy-paste slip in a new entry: a missing blurb, a duplicated
# key, a signature that can never match.

def _check_symbols(fail):
    for latex, e in SYMBOLS.items():
        where = 'symbol %r' % latex
        for field in ('unicode', 'name', 'category', 'blurb', 'wiki'):
            if not e.get(field):
                fail('%s: empty %s' % (where, field))
        if len(e['blurb']) < 20:
            fail('%s: blurb is too short to teach anything' % where)
        if not e['wiki'].startswith(WIKI) or e['wiki'] == WIKI:
            fail('%s: bad wikipedia link %r' % (where, e['wiki']))
        if e['latex'] != latex:
            fail('%s: entry disagrees with its key (%r)' % (where, e['latex']))


def _check_tables(fail):
    seen = {}
    for name, table, width in (('GREEK_LOWER', GREEK_LOWER, 5),
                               ('GREEK_UPPER', GREEK_UPPER, 5),
                               ('OPERATORS', OPERATORS, 6),
                               ('LATIN', LATIN, 5)):
        for row in table:
            if len(row) != width:
                fail('%s: row %r has %d fields, expected %d'
                     % (name, row[0], len(row), width))
            if row[0] in seen:
                fail('%s: %r already defined in %s' % (name, row[0], seen[row[0]]))
            seen[row[0]] = name


def _check_concepts(fail):
    for title, c in CONCEPTS.items():
        where = 'concept %r' % title
        if not c['body']:
            fail('%s: empty body' % where)
        if not c['category']:
            fail('%s: no category' % where)
        for latex in c['symbols']:
            if latex not in SYMBOLS:
                fail('%s: cross links %r, which is not a symbol' % (where, latex))
        names = set(eq['name'] for eq in EQUATIONS)
        for eq in c['equations']:
            if eq not in names:
                fail('%s: cross links %r, which is not an equation' % (where, eq))


def _check_equations(fail):
    seen = set()
    for eq in EQUATIONS:
        where = 'equation %r' % eq.get('name', '?')
        for field in ('name', 'field', 'latex', 'slug', 'blurb'):
            if not eq.get(field):
                fail('%s: empty %s' % (where, field))
        if eq['name'] in seen:
            fail('%s: duplicate name' % where)
        seen.add(eq['name'])
        if not eq.get('must'):
            fail('%s: no must features, so it can never be identified' % where)
        overlap = set(eq.get('must', [])) & set(eq.get('nice', []))
        if overlap:
            fail('%s: %s listed as both must and nice'
                 % (where, ', '.join(sorted(overlap))))
        source = eq.get('source')
        if source is not None:
            if not isinstance(source, str) or len(source) < 10:
                fail('%s: source is too short to find anything by' % where)
            elif ':' not in source:
                fail('%s: source %r does not name a file or function -- the '
                     'point is to say where the number was computed, not just '
                     'which project it came from' % (where, source))

    # the two monotile substitutions must stay distinguishable.  They give
    # different inflation factors, both correct, and an entry that cites
    # neither matrix is the thing that made them look contradictory.
    for name in ('Spectre inflation factor', 'Hat inflation factor'):
        entry = GRAPH.find(name, 'equation')
        if entry is not None and not entry.get('source'):
            fail('%s states an inflation factor without saying which '
                 'substitution matrix it came from' % name)


def _check_graph(fail):
    g = GRAPH
    for node in g.nodes.values():
        if node.key != '%s:%s' % (node.kind, node[node.key_field]):
            fail('node %r has a key that does not match its fields' % node.label)
    for src, kind, dst, _note in LINKS:
        if g.find(src, 'equation') is None:
            fail('LINKS names %r, which is not an equation' % src)
        if g.find(dst, 'equation') is None:
            fail('LINKS names %r, which is not an equation' % dst)
    for edge in g.edges:
        if edge.src.key not in g.nodes or edge.dst.key not in g.nodes:
            fail('edge %r joins a node that is not in the graph' % edge)
    # every equation that states a quantity directly should be reachable from
    # the others it shares that quantity with -- otherwise the shares edges and
    # the join logic disagree, and one of them is wrong
    for derivation in all_joins():
        a, b = derivation.equations
        if g.edge_between(a, b) is None:
            fail('%s and %s can be joined but are not linked'
                 % (a.label, b.label))
        if len(derivation) != 2:
            fail('a pairwise join produced %d steps' % len(derivation))


def _check_derivations(fail):
    for derivation in all_joins():
        tex = derivation.latex()
        if tex.count(r'\underbrace') != len(derivation):
            fail('%r does not brace every step' % derivation)
        if r'\overbrace' not in tex:
            fail('%r does not record the quantity it was joined on' % derivation)
        for step in derivation.steps:
            if step.expr not in tex:
                fail('%r lost the expression from %s'
                     % (derivation, step.equation.label))
        bare = derivation.statement()
        if r'\underbrace' in bare or r'\overbrace' in bare:
            fail('%r leaves provenance in its bare statement' % derivation)
        if split_relation(bare) is None:
            fail('%r does not read back as a relation' % derivation)



def _check_algebra(fail):
    """The reader, the printer and the rearranger, against each other."""
    for eq in EQUATIONS:
        why = algebraic(eq['latex'])
        if why is not None:
            continue                      # refused on purpose; nothing to test
        # split on whatever relation the statement uses, not on '=' alone:
        # plenty of physics is an inequality, and handing the parser a fragment
        # with a \leq still in it tests the splitter rather than the reader
        parts = split_relation(eq['latex'])
        side = parts[0] if parts else eq['latex']
        try:
            term = read_term(side)
        except Unreadable as exc:
            fail('%s: algebraic() passed it but the parser did not (%s)'
                 % (eq.label, exc))
            continue
        # rendering and reading back must agree, or the printer is lying
        try:
            again = read_term(render(term))
        except Unreadable as exc:
            fail('%s: its own output does not read back (%s)' % (eq.label, exc))
            continue
        if again != term:
            fail('%s: round trip changed it -- %s became %s'
                 % (eq.label, render(term), render(again)))

    # the rearranger must refuse the things it says it refuses
    cases = [
        ('x^{2}', 'a', 'y', 'an even power has two roots'),
        ('x + x', 'x', 'x', 'a repeated symbol needs terms collected'),
    ]
    for left, _unused, name, why in cases:
        try:
            isolate(read_term(left), read_term('c'), name)
        except CannotIsolate:
            continue
        except Unreadable:
            continue
        fail('isolate accepted %r for %s, but %s' % (left, name, why))

    # a prime belongs to the name, and all three spellings of it are the same
    # quantity -- otherwise alpha' joins to alpha, which are different numbers
    spellings = [r"\alpha'", r'\alpha^\prime', r'\alpha^{\prime}']
    reference = None
    for text in spellings:
        try:
            got = read_term(text)
        except Unreadable as exc:
            fail('%s has no reading, but it is a name (%s)' % (text, exc))
            continue
        if not isinstance(got, Sym):
            fail('%s reads as %r, not as a name' % (text, got))
            continue
        if reference is None:
            reference = got
        elif got != reference:
            fail('%s and %s are spellings of one quantity but read as two'
                 % (spellings[0], text))
    if reference is not None and reference == read_term(r'\alpha'):
        fail("alpha' reads as the same quantity as alpha")

    # a brace holding nothing but Greek is an index; a brace holding an
    # expression is an expression, even when a Greek letter occurs in it
    indexed = [r'G_{\mu\nu}', r'A_{\mu \nu}', r'T^{\mu}']
    for text in indexed:
        if algebraic(text) != 'an indexed tensor component':
            fail('%s is a tensor component and should be refused as one' % text)
    for text in (r'e^{i \pi}', r'g_s^{-\chi}', r'x^{2 \chi}'):
        why = algebraic(text)
        if why == 'an indexed tensor component':
            fail('%s is an exponent, not an index' % text)

    # an operator applied to a set is not a factor times a set
    if algebraic(r'\dim_H K') is None:
        fail('dim is being read as a symbol multiplied by its argument')

    # and what it accepts must actually invert
    checks = [('P V', 'n R T', 'V'), ('F', 'm a', 'm'), ('S', 'k \\log W', 'W')]
    for left, right, name in checks:
        try:
            got = isolate(read_term(left), read_term(right), name)
        except CannotIsolate as exc:
            fail('isolate could not solve %s = %s for %s (%s)'
                 % (left, right, name, exc))
            continue
        if simplify(got).contains(name):
            fail('solving for %s left it on both sides' % name)


def _check_readings(fail):
    known = set(QUANTITIES)
    for name, table in READINGS.items():
        if GRAPH.find(name, 'equation') is None:
            fail('READINGS names %r, which is not an equation' % name)
            continue
        eq = GRAPH.find(name, 'equation')
        for symbol, quantity in table.items():
            if quantity not in known:
                fail('%s reads %s as %r, which is not a quantity'
                     % (name, symbol, quantity))
        # a reading for a symbol the equation does not contain is a typo
        why = algebraic(eq['latex'])
        if why is not None:
            continue
        try:
            present = set(read_relation(eq['latex']).symbols())
        except Unreadable:
            continue
        for symbol in table:
            if symbol not in present:
                fail('%s reads %r, which does not appear in it'
                     % (name, symbol))

    # every join must be between equations that agree about the pivot
    for derivation in all_joins():
        a, b = derivation.equations
        if not agree(a, b, derivation.pivot):
            fail('%s joins on %s without an agreed reading'
                 % (derivation, derivation.pivot))
        if derivation.steps[0].expr == derivation.steps[1].expr:
            fail('%s is an identity, not a claim' % derivation)

    # a folded subscript resolves for a constant, because there is only one
    # permittivity of free space and identifying two mentions of it assumes
    # nothing
    if resolve_feature(GRAPH.find("Coulomb's law", 'equation'),
                       'epsilon') != 'epsilon_0':
        fail('epsilon does not resolve to epsilon_0, so constants cannot join')
    if join("Coulomb's law", 'Debye length') is None:
        fail('two equations stating the same constant were not joined')

    # and does not resolve for anything else, because there are many energies,
    # speeds and temperatures, and picking whichever one an equation happens to
    # mention asserts an identity nobody declared
    for a, b, why in [
            ('Mass-energy equivalence', 'Kinetic energy',
             'a rest energy is not a kinetic energy'),
            ('Kinetic energy', 'Thermal energy',
             'that is equipartition, and wrong by three halves'),
            ('Escape velocity', "Hubble's law",
             'an escape velocity is not a recession velocity'),
            ('Ideal gas law', 'Hagedorn temperature',
             'a gas temperature is not the Hagedorn temperature')]:
        if join(a, b) is not None:
            fail('%s and %s were joined: %s' % (a, b, why))

    # an ambiguous fold is refused outright: m_1 and m_2 are two masses, and
    # 'm' names neither
    if resolve_feature(GRAPH.find("Newton's law of gravitation", 'equation'),
                       'm') != 'm':
        fail('m resolved to one of two masses, which is a guess')

    # the alternative pivot rule must still be offering nothing worth having.
    # If this fires, the permissive rule has found a licensed statement about a
    # quantity no family covers, and the reason is probably an over-broad entry
    # in COMMON rather than a case for adopting the rule.
    _unlicensed, _known, novel = quantity_join_census()
    for a, b, quantity, sym_a, sym_b in novel:
        fail('quantity pivoting offers %s + %s on %s (%s/%s), which is '
             'licensed and not already a family'
             % (a.label, b.label, quantity, sym_a, sym_b))

    # f was taken out of COMMON for exactly one statement; it should still be
    # there, or the removal bought nothing
    if join('Angular frequency', 'Wave speed') is None:
        fail('the join f was removed from COMMON for has gone missing')

    # and the collisions we know about must still be caught
    for a, b, q in [('Boltzmann entropy', 'Work done by a force', 'W'),
                    ('Planck relation', 'Gravitational potential energy', 'h'),
                    ('Ideal gas law', "Ohm's law", 'V')]:
        if agree(a, b, q):
            fail('%s and %s should not agree about %s' % (a, b, q))
        if join(a, b, pivot=q) is not None:
            fail('%s and %s were joined on %s anyway' % (a, b, q))



def _check_short(fail):
    """Short labels must stay distinct, or the grand display misattributes."""
    seen = {}
    for name, text in SHORT.items():
        if GRAPH.find(name, 'equation') is None:
            fail('SHORT names %r, which is not an equation' % name)
        if text in seen:
            fail('%r and %r share the short label %r'
                 % (name, seen[text], text))
        seen[text] = name
        if len(text) > 20:
            fail('%r is too long to sit under a brace' % text)
    display = grand()
    for chained in grand_members():
        for step in chained.steps:
            if _tex_escape(short(step.equation)) not in display:
                fail('%s is in the display but unlabelled' % step.equation.label)
    if display.count(r'\underbrace') != sum(len(f) for f in grand_members()):
        fail('the display does not brace every term')
    if display.count(r'\overbrace') != len(grand_members()):
        fail('the display does not brace every row')


def _check_numeric(fail):
    """The corner of the library where truth is decidable, decided."""
    checks = numeric_checks()
    if not checks:
        fail('nothing is numerically determined, so a mistyped surd would '
             'not be caught')
    for eq, left, right in checks:
        if not math.isclose(left, right, rel_tol=1e-12, abs_tol=1e-12):
            fail('%s does not hold on the declared constants: %.12g vs %.12g'
                 % (eq.label, left, right))


def selftest():
    """Validate every entry.  Returns the number of problems found."""
    problems = []

    def fail(msg):
        problems.append(msg)

    _check_symbols(fail)
    _check_tables(fail)
    _check_concepts(fail)
    _check_equations(fail)
    _check_graph(fail)
    _check_derivations(fail)
    _check_algebra(fail)
    _check_readings(fail)
    _check_short(fail)
    _check_numeric(fail)

    for msg in problems:
        print('FAIL  ' + msg)
    if problems:
        print('\n%d problem(s) in the knowledge base.' % len(problems))
    else:
        print('rosettaphys: %d symbols, %d concepts, %d equations, '
              '%d edges, %d joins -- all well formed.'
              % (len(SYMBOLS), len(CONCEPTS), len(EQUATIONS),
                 len(GRAPH.edges), len(all_joins())))
    return len(problems)


def _report():
    print(__doc__.strip().split('\n')[0])
    print()
    for key, value in census().items():
        print('  %-20s %d' % (key, value))
    print('  %-20s %d' % ('quantities', len(QUANTITIES)))
    print('  %-20s %d' % ('readings', sum(len(t) for t in READINGS.values())))
    print()
    print('  graph: %d nodes, %d edges' % (len(GRAPH.nodes), len(GRAPH.edges)))
    for kind, count in sorted(GRAPH.census().items()):
        print('  %-20s %d' % ('  ' + kind, count))
    print()
    joins = all_joins()
    print('  joins available (%d):' % len(joins))
    for derivation in joins:
        mark = ' *' if derivation.rearranged else '  '
        print('   %s %-42s %s' % (mark,
            ' = '.join(s.equation.label for s in derivation.steps)[:42],
            derivation.statement()))
    print('    (* one or both sides had to be rearranged)')
    clashes = disagreements()
    print()
    print('  letters used for two different quantities (%d):' % len(clashes))
    seen = set()
    for a, b, q, left, right in clashes:
        key = (q, tuple(sorted((left, right))))
        if key in seen:
            continue
        seen.add(key)
        print('    %-8s %-24s vs %-24s (%s / %s)'
              % (q, left, right, a.label, b.label))
    print()
    print('  symbol categories:  ' + ', '.join(categories()))
    print('  concept categories: ' + ', '.join(concept_categories()))
    print('  equation fields:    ' + ', '.join(fields()))


if __name__ == '__main__':
    import sys
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    _report()
