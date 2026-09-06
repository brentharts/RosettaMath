#!/usr/bin/env python3
r"""RosettaUI -- an interactive, clickable LaTeX explorer for RosettaMath.

A PyQt5 front end for rosettamath.py.  An equation is parsed into a small
tree, laid out glyph by glyph in a QGraphicsScene, and every glyph becomes a
live object:

    hover ......... tooltip: the symbol's name, its Greek/Latin origin, and
                    what it conventionally denotes in physics and maths
    left click .... offline explanation popup (our own text, no network)
    right click ... context menu -> webbrowser.open() the Wikipedia article

The whole equation is classified too: a signature matcher compares the set of
symbols and structures against a library of well known equations, so the view
can say "this looks like the Klein-Gordon equation" or "this is a diffusion
equation".

Because all the concepts are described and cross linked, the menu bar doubles
as a browsable offline encyclopedia of the maths and physics conventions.

This module is deliberately plain Python -- unlike rosettamath.py it is not
self-hosted and is not written in the translatable LaTeX subset.

    python3 rosettaui.py                  launch the GUI
    python3 rosettaui.py --selftest       headless test of parser/classifier
    python3 rosettaui.py --render-test    offscreen render to /tmp/rosettaui.png
    python3 rosettaui.py --tex '$E=mc^2$' launch with a given equation
"""
import os
import sys
import html
import shutil
import hashlib
import subprocess
import tempfile
import webbrowser

# rosettamath lives next to us; make sure it is importable however we are run
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rosettamath

WIKI = 'https://en.wikipedia.org/wiki/'

# ---------------------------------------------------------------- fonts

# "Computer Modern" is the TeX family *name*, but almost no system installs it
# under that name -- the OpenType successor is "Latin Modern".  Ask for the
# first family that actually exists rather than letting Qt silently fall back.
SERIF_STACK = ['Latin Modern Roman', 'CMU Serif', 'Computer Modern',
               'TeX Gyre Termes', 'DejaVu Serif', 'Times New Roman', 'serif']
MATH_STACK = ['Latin Modern Math', 'DejaVu Math TeX Gyre', 'STIX Two Math',
              'XITS Math', 'DejaVu Serif', 'serif']
MONO_STACK = ['Latin Modern Mono', 'DejaVu Sans Mono', 'Courier New', 'monospace']

_font_cache = {}


def pick_family(stack):
    """First family in stack that the font database really has."""
    key = tuple(stack)
    if key in _font_cache:
        return _font_cache[key]
    from PyQt5.QtGui import QFontDatabase
    have = set(QFontDatabase().families())
    chosen = stack[-1]
    for fam in stack:
        if fam in have:
            chosen = fam
            break
    _font_cache[key] = chosen
    return chosen


# ---------------------------------------------------------------- symbols
#
# Every entry:  unicode, display name, category, blurb, wikipedia slug.
# The blurb is the offline description -- it should say what the symbol *is*
# and what it conventionally *denotes*, since that is the part a newcomer to
# physics notation cannot look up in a syntax reference.

SYMBOLS = {}


def add_symbol(latex, uni, name, category, blurb, slug, aka=''):
    SYMBOLS[latex] = {
        'latex': latex, 'unicode': uni, 'name': name, 'category': category,
        'blurb': blurb, 'wiki': WIKI + slug, 'aka': aka,
    }


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
    CONCEPTS[title] = {
        'title': title, 'category': category, 'body': body.strip(),
        'wiki': WIKI + slug, 'symbols': list(symbols), 'equations': list(equations),
    }


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


# ---------------------------------------------------------------- equations
#
# A signature library.  Each entry lists the features that MUST be present for
# the equation to be a candidate, plus features that raise confidence.  The
# feature vocabulary is produced by extract_features() below: bare symbol names
# ('psi', 'hbar', 'E'), and structural tags prefixed with 'S:' ('S:frac',
# 'S:nabla2', 'S:sup2').

EQUATIONS = [
    dict(name='Mass-energy equivalence', field='Relativity',
         latex=r'E = m c^2', slug='Mass%E2%80%93energy_equivalence',
         must=['E', 'm', 'c', 'S:sup2'], nice=[],
         blurb='Mass and energy are the same thing in different units, and the '
               'conversion factor is enormous. The equation does not say mass '
               'turns into energy; it says a system with energy has inertia, '
               'and a body at rest already carries energy m*c^2.'),
    dict(name='Newton\'s second law', field='Classical mechanics',
         latex=r'F = m a', slug='Newton%27s_laws_of_motion',
         must=['F', 'm', 'a'], nice=[],
         blurb='Force equals mass times acceleration -- more precisely, force '
               'is the rate of change of momentum. It is the definition that '
               'makes mass measurable and turns mechanics into a solvable '
               'differential equation.'),
    dict(name='Newton\'s law of gravitation', field='Classical mechanics',
         latex=r'F = G \frac{m_1 m_2}{r^2}', slug='Newton%27s_law_of_universal_gravitation',
         must=['F', 'G', 'm', 'r', 'S:frac'], nice=['S:sup2', 'S:sub'],
         blurb='An inverse-square attraction between any two masses. The '
               'inverse square is not arbitrary: it is what a flux spreading '
               'over the surface of a sphere must do in three dimensions.'),
    dict(name='Coulomb\'s law', field='Electromagnetism',
         latex=r'F = \frac{1}{4 \pi \epsilon_0} \frac{q_1 q_2}{r^2}',
         slug='Coulomb%27s_law',
         must=['F', 'epsilon', 'r', 'S:frac', 'pi'], nice=['q', 'S:sup2'],
         blurb='The electrostatic force between two charges. Structurally '
               'identical to Newtonian gravity, but roughly 10^36 times '
               'stronger and able to take either sign -- which is why bulk '
               'matter is electrically neutral and gravity wins at large '
               'scales.'),
    dict(name='Schrodinger equation (time-dependent)', field='Quantum mechanics',
         latex=r'i \hbar \frac{\partial \Psi}{\partial t} = \hat{H} \Psi',
         slug='Schr%C3%B6dinger_equation',
         must=['i', 'hbar', 'partial', 'Psi'], nice=['H', 'S:frac', 't', 'S:hat'],
         blurb='The equation of motion for a quantum state. The i on the left '
               'makes it a wave equation rather than a diffusion equation: '
               'instead of smoothing out, solutions rotate in phase and '
               'interfere. It is first order in time, so the present state '
               'determines the entire future.'),
    dict(name='Schrodinger equation (time-independent)', field='Quantum mechanics',
         latex=r'-\frac{\hbar^2}{2m} \nabla^2 \psi + V \psi = E \psi',
         slug='Schr%C3%B6dinger_equation',
         must=['hbar', 'psi', 'E', 'S:nabla2'], nice=['m', 'V', 'S:frac', 'S:sup2'],
         blurb='An eigenvalue problem: only certain energies admit '
               'well-behaved solutions, and that discreteness is where '
               'quantisation comes from. Atomic energy levels are the '
               'eigenvalues of this equation for a Coulomb potential.'),
    dict(name='Klein-Gordon equation', field='Quantum field theory',
         latex=r'\left( \Box + \frac{m^2 c^2}{\hbar^2} \right) \phi = 0',
         slug='Klein%E2%80%93Gordon_equation',
         must=['phi', 'm', 'hbar'], nice=['c', 'S:nabla2', 'partial', 'S:sup2', 'S:frac'],
         blurb='The relativistic wave equation for a spinless field. It is '
               'second order in time, unlike the Schrodinger equation, which '
               'is what makes it Lorentz invariant -- and also what forced the '
               'reinterpretation of its negative-energy solutions as '
               'antiparticles.'),
    dict(name='Dirac equation', field='Quantum field theory',
         latex=r'( i \gamma^\mu \partial_\mu - m ) \psi = 0',
         slug='Dirac_equation',
         must=['i', 'gamma', 'partial', 'psi', 'm'], nice=['mu', 'S:sup', 'S:sub'],
         blurb='The relativistic equation for spin-1/2 particles. Dirac '
               'insisted on first order in time, which required the '
               'coefficients to be matrices; spin and antimatter both fell out '
               'of the algebra rather than being put in by hand.'),
    dict(name='Wave equation', field='Waves',
         latex=r'\frac{\partial^2 u}{\partial t^2} = c^2 \nabla^2 u',
         slug='Wave_equation',
         must=['partial', 'c', 'S:nabla2'], nice=['S:frac', 't', 'S:sup2', 'u'],
         blurb='A second time derivative equal to a Laplacian: disturbances '
               'propagate at fixed speed c without changing shape. Sound, '
               'light, and a plucked string all obey it, and the constant c is '
               'set by the medium.'),
    dict(name='Heat / diffusion equation', field='Thermodynamics',
         latex=r'\frac{\partial u}{\partial t} = \alpha \nabla^2 u',
         slug='Heat_equation',
         must=['partial', 'S:nabla2'], nice=['alpha', 'S:frac', 't', 'u', 'D'],
         blurb='A first time derivative equal to a Laplacian: gradients smooth '
               'out irreversibly. Unlike the wave equation it has a preferred '
               'direction of time -- you cannot run it backwards stably, which '
               'is the arrow of time appearing in a differential equation.'),
    dict(name='Laplace\'s equation', field='Fields',
         latex=r'\nabla^2 \phi = 0', slug='Laplace%27s_equation',
         must=['S:nabla2'], nice=['phi', 'Phi', 'u'],
         blurb='The Laplacian vanishes: the field everywhere equals the '
               'average of its neighbours. Such harmonic functions describe '
               'static fields in empty space, and they have no local maxima or '
               'minima in the interior -- extremes live on the boundary.'),
    dict(name='Poisson\'s equation', field='Fields',
         latex=r'\nabla^2 \phi = \rho', slug='Poisson%27s_equation',
         must=['S:nabla2', 'rho'], nice=['phi', 'Phi', 'epsilon', 'S:frac'],
         blurb='Laplace\'s equation with a source. The density on the right '
               'tells the potential how to curve; solving it recovers the '
               'gravitational or electrostatic potential produced by a given '
               'distribution of mass or charge.'),
    dict(name='Helmholtz equation', field='Waves',
         latex=r'\nabla^2 A + k^2 A = 0', slug='Helmholtz_equation',
         must=['S:nabla2', 'k'], nice=['A', 'S:sup2'],
         blurb='What the wave equation becomes after separating out a single '
               'frequency. k is the wavenumber; the equation governs standing '
               'waves, waveguides and optical modes.'),
    dict(name='Gauss\'s law', field='Electromagnetism',
         latex=r'\nabla \cdot E = \frac{\rho}{\epsilon_0}', slug='Gauss%27s_law',
         must=['nabla', 'rho', 'E'], nice=['epsilon', 'S:frac', 'S:cdot'],
         blurb='The divergence of the electric field is the charge density: '
               'field lines begin and end on charge. Integrated over a closed '
               'surface it says the flux out equals the charge enclosed, '
               'regardless of how that charge is arranged.'),
    dict(name='Gauss\'s law for magnetism', field='Electromagnetism',
         latex=r'\nabla \cdot B = 0', slug='Gauss%27s_law_for_magnetism',
         must=['nabla', 'B'], nice=['S:cdot'],
         blurb='The magnetic field has zero divergence: there are no magnetic '
               'monopoles. Every field line closes on itself, which is why '
               'cutting a magnet in half gives two magnets rather than a north '
               'and a south pole.'),
    dict(name='Faraday\'s law of induction', field='Electromagnetism',
         latex=r'\nabla \times E = -\frac{\partial B}{\partial t}',
         slug='Faraday%27s_law_of_induction',
         must=['nabla', 'E', 'B', 'partial'], nice=['S:times', 'S:frac', 't'],
         blurb='A changing magnetic field creates a circulating electric '
               'field. This is the principle behind every generator and '
               'transformer, and the minus sign (Lenz\'s law) is what keeps '
               'the induced effect opposing the change that caused it.'),
    dict(name='Ampere-Maxwell law', field='Electromagnetism',
         latex=r'\nabla \times B = \mu_0 J + \mu_0 \epsilon_0 \frac{\partial E}{\partial t}',
         slug='Amp%C3%A8re%27s_circuital_law',
         must=['nabla', 'B', 'mu'], nice=['J', 'epsilon', 'partial', 'E', 'S:times'],
         blurb='Currents and changing electric fields both create circulating '
               'magnetic fields. Maxwell\'s addition of the second term is '
               'what made the equations self-consistent and predicted '
               'electromagnetic waves travelling at the speed of light.'),
    dict(name='Continuity equation', field='Conservation laws',
         latex=r'\frac{\partial \rho}{\partial t} + \nabla \cdot J = 0',
         slug='Continuity_equation',
         must=['partial', 'rho', 'nabla'], nice=['J', 't', 'S:frac', 'S:cdot'],
         blurb='The local statement of a conservation law: whatever the '
               'density loses, the flux must carry across the boundary. The '
               'same form governs mass, charge, energy and probability.'),
    dict(name='Navier-Stokes equation', field='Fluid dynamics',
         latex=r'\rho \left( \frac{\partial v}{\partial t} + v \cdot \nabla v \right) = -\nabla p + \eta \nabla^2 v',
         slug='Navier%E2%80%93Stokes_equations',
         must=['rho', 'partial', 'nabla', 'v'], nice=['eta', 'p', 'mu', 'S:nabla2'],
         blurb='Newton\'s second law for a fluid. The nonlinear term in which '
               'the velocity advects itself is what produces turbulence, and '
               'why proving that smooth solutions always exist is an open '
               'Millennium Prize problem.'),
    dict(name='Euler-Lagrange equation', field='Classical mechanics',
         latex=r'\frac{d}{dt} \frac{\partial L}{\partial \dot{q}} - \frac{\partial L}{\partial q} = 0',
         slug='Euler%E2%80%93Lagrange_equation',
         must=['partial', 'L'], nice=['q', 'S:dot', 'S:frac', 't'],
         blurb='The condition for the action to be stationary. Feed it a '
               'Lagrangian and it hands back the equations of motion; for a '
               'particle in a potential it reduces to F = ma, but it works '
               'just as well in awkward coordinates where forces are painful.'),
    dict(name='Boltzmann entropy', field='Thermodynamics',
         latex=r'S = k_B \log W', slug='Boltzmann%27s_entropy_formula',
         must=['S', 'k'], nice=['log', 'W', 'ln', 'S:sub'],
         blurb='Entropy is the logarithm of the number of microstates. This '
               'formula, carved on Boltzmann\'s gravestone, is the bridge '
               'between the microscopic world of atoms and the macroscopic '
               'laws of thermodynamics.'),
    dict(name='Shannon entropy', field='Information theory',
         latex=r'H = -\sum p_i \log p_i', slug='Entropy_(information_theory)',
         must=['S:sum', 'p'], nice=['H', 'log', 'S:sub', 'i'],
         blurb='The average information content of a distribution, measured in '
               'bits when the logarithm is base two. It is Boltzmann\'s formula '
               'again in a different guise, and it sets the hard limit on how '
               'far data can be compressed.'),
    dict(name='Planck relation', field='Quantum mechanics',
         latex=r'E = h \nu', slug='Planck_relation',
         must=['E', 'h'], nice=['nu', 'omega', 'hbar', 'f'],
         blurb='A photon\'s energy is proportional to its frequency, with '
               'Planck\'s constant as the conversion. This is the quantum '
               'hypothesis in its smallest form: light comes in discrete '
               'packets, which is why the photoelectric effect depends on '
               'colour rather than brightness.'),
    dict(name='de Broglie relation', field='Quantum mechanics',
         latex=r'\lambda = \frac{h}{p}', slug='Matter_wave',
         must=['lambda', 'h', 'p'], nice=['S:frac'],
         blurb='Every particle has a wavelength inversely proportional to its '
               'momentum. For everyday objects it is unmeasurably small; for '
               'electrons it is atom-sized, which is why they diffract and why '
               'electron microscopes work.'),
    dict(name='Heisenberg uncertainty principle', field='Quantum mechanics',
         latex=r'\Delta x \Delta p \geq \frac{\hbar}{2}',
         slug='Uncertainty_principle',
         must=['Delta', 'hbar'], nice=['x', 'p', 'geq', 'S:frac'],
         blurb='Position and momentum cannot both be sharply defined. This is '
               'not a limit on instruments but a property of Fourier conjugate '
               'pairs: a narrow wave packet in space is necessarily broad in '
               'wavenumber.'),
    dict(name='Einstein field equations', field='General relativity',
         latex=r'G_{\mu\nu} + \Lambda g_{\mu\nu} = \frac{8 \pi G}{c^4} T_{\mu\nu}',
         slug='Einstein_field_equations',
         must=['mu', 'nu', 'G', 'T'], nice=['Lambda', 'pi', 'c', 'g', 'S:frac', 'S:sub'],
         blurb='Curvature on the left, matter and energy on the right: '
               'spacetime tells matter how to move, matter tells spacetime how '
               'to curve. Ten coupled nonlinear equations, which is why exact '
               'solutions are rare and precious.'),
    dict(name='Schwarzschild radius', field='General relativity',
         latex=r'r_s = \frac{2 G M}{c^2}', slug='Schwarzschild_radius',
         must=['G', 'c', 'r'], nice=['M', 'm', 'S:frac', 'S:sup2', 'S:sub'],
         blurb='The radius at which the escape velocity reaches the speed of '
               'light -- the event horizon of a non-rotating black hole. For '
               'the Sun it is about three kilometres, for the Earth about nine '
               'millimetres.'),
    dict(name='Bekenstein-Hawking entropy', field='General relativity',
         latex=r'S = \frac{k_B c^3 A}{4 G \hbar}', slug='Black_hole_thermodynamics',
         must=['S', 'G', 'hbar', 'c'], nice=['k', 'A', 'S:frac', 'S:sup'],
         blurb='A black hole\'s entropy is proportional to the area of its '
               'horizon, not its volume. That every fundamental constant '
               'appears at once -- quantum, relativistic, gravitational and '
               'thermodynamic -- is why this formula is treated as a clue to '
               'quantum gravity, and it is the origin of the holographic '
               'principle.'),
    dict(name='Lorentz factor', field='Relativity',
         latex=r'\gamma = \frac{1}{\sqrt{1 - \frac{v^2}{c^2}}}',
         slug='Lorentz_factor',
         must=['gamma', 'v', 'c', 'S:sqrt'], nice=['S:frac', 'S:sup2'],
         blurb='The factor by which time dilates and length contracts. It is '
               'essentially one at everyday speeds and diverges as v '
               'approaches c, which is why massive objects cannot reach the '
               'speed of light.'),
    dict(name='Ideal gas law', field='Thermodynamics',
         latex=r'P V = n R T', slug='Ideal_gas_law',
         must=['V', 'T', 'R'], nice=['P', 'n', 'p', 'N', 'k'],
         blurb='Pressure times volume equals amount times temperature. An '
               'excellent approximation whenever the molecules are far enough '
               'apart to ignore their size and mutual attraction.'),
    dict(name='Stefan-Boltzmann law', field='Thermodynamics',
         latex=r'j = \sigma T^4', slug='Stefan%E2%80%93Boltzmann_law',
         must=['sigma', 'T'], nice=['S:sup', 'j', 'P', 'A'],
         blurb='Radiated power scales as the fourth power of temperature. The '
               'steepness is why a modest rise in a star\'s surface '
               'temperature makes it dramatically brighter.'),
    dict(name='Plasma frequency', field='Plasma physics',
         latex=r'\omega_p = \sqrt{\frac{n e^2}{\epsilon_0 m_e}}',
         slug='Plasma_oscillation',
         must=['omega', 'n', 'e', 'epsilon', 'S:sqrt'], nice=['m', 'S:frac', 'S:sub'],
         blurb='The natural oscillation frequency of electrons in a plasma. '
               'Waves below it cannot propagate and are reflected -- which is '
               'how the ionosphere bounces radio signals around the curve of '
               'the Earth.'),
    dict(name='Debye length', field='Plasma physics',
         latex=r'\lambda_D = \sqrt{\frac{\epsilon_0 k_B T}{n e^2}}',
         slug='Debye_length',
         must=['lambda', 'epsilon', 'T', 'n', 'e'], nice=['k', 'S:sqrt', 'S:frac'],
         blurb='The distance over which a charge is screened out by the '
               'surrounding plasma. Beyond it the plasma looks neutral, and a '
               'system is only genuinely a plasma if it is much larger than '
               'this length.'),
    dict(name='Vlasov equation', field='Plasma physics',
         latex=r'\frac{\partial f}{\partial t} + v \cdot \nabla f + \frac{F}{m} \cdot \nabla_v f = 0',
         slug='Vlasov_equation',
         must=['partial', 'f', 'nabla', 'v'], nice=['F', 'm', 't', 'S:frac', 'S:cdot'],
         blurb='Tracks the distribution of particles in position-velocity '
               'space for a collisionless plasma. It is a continuity equation '
               'in six dimensions, with the electromagnetic force supplied '
               'self-consistently by the particles themselves.'),
    dict(name='Friedmann equation', field='Cosmology',
         latex=r'H^2 = \frac{8 \pi G}{3} \rho - \frac{k c^2}{a^2} + \frac{\Lambda c^2}{3}',
         slug='Friedmann_equations',
         must=['H', 'G', 'rho'], nice=['pi', 'Lambda', 'a', 'c', 'k', 'S:frac', 'S:sup2'],
         blurb='Governs the expansion of a homogeneous universe. The competing '
               'terms are matter, spatial curvature and the cosmological '
               'constant, and which one dominates decides whether the universe '
               'expands forever.'),
    dict(name='Euler\'s identity', field='Mathematics',
         latex=r'e^{i \pi} + 1 = 0', slug='Euler%27s_identity',
         must=['e', 'i', 'pi', 'S:sup'], nice=[],
         blurb='Rotating by half a turn in the complex plane lands you at -1. '
               'It links the additive identity, the multiplicative identity, '
               'and the three constants e, i and pi in one line.'),
    dict(name='Pythagorean theorem', field='Mathematics',
         latex=r'a^2 + b^2 = c^2', slug='Pythagorean_theorem',
         must=['a', 'b', 'c', 'S:sup2'], nice=[],
         blurb='In a right triangle the squares on the legs sum to the square '
               'on the hypotenuse. Generalised, it is the definition of '
               'distance in Euclidean space -- and changing the signs gives '
               'the spacetime interval of relativity.'),
    dict(name='Quadratic formula', field='Mathematics',
         latex=r'x = \frac{-b \pm \sqrt{b^2 - 4ac}}{2a}',
         slug='Quadratic_formula',
         must=['x', 'S:sqrt', 'S:frac', 'pm'], nice=['a', 'b', 'c', 'S:sup2'],
         blurb='The roots of a quadratic. The discriminant under the root '
               'decides everything: positive gives two real roots, zero a '
               'repeated one, negative a complex conjugate pair.'),
    dict(name='Bayes\' theorem', field='Probability',
         latex=r'P(A \mid B) = \frac{P(B \mid A) P(A)}{P(B)}',
         slug='Bayes%27_theorem',
         must=['P', 'S:frac'], nice=['A', 'B', 'mid'],
         blurb='How to update a belief when evidence arrives. The prior is '
               'multiplied by how well the hypothesis predicted the data and '
               'renormalised -- the whole of Bayesian inference is repeated '
               'application of this one line.'),
    dict(name='Normal distribution', field='Probability',
         latex=r'f(x) = \frac{1}{\sigma \sqrt{2\pi}} e^{-\frac{(x-\mu)^2}{2\sigma^2}}',
         slug='Normal_distribution',
         must=['sigma', 'mu', 'pi', 'S:exp_or_e'], nice=['x', 'S:frac', 'S:sqrt', 'S:sup2'],
         blurb='The bell curve. The central limit theorem explains its '
               'ubiquity: add up enough independent small effects and the '
               'total is normally distributed almost regardless of what you '
               'started with.'),
    dict(name='Kullback-Leibler divergence', field='Information theory',
         latex=r'D(P \parallel Q) = \sum P(x) \log \frac{P(x)}{Q(x)}',
         slug='Kullback%E2%80%93Leibler_divergence',
         must=['S:sum', 'log', 'P'], nice=['Q', 'D', 'S:frac', 'x'],
         blurb='The relative entropy between two distributions: the extra '
               'information cost of using the wrong model. It is never '
               'negative, zero only when the distributions agree, and is not '
               'symmetric -- so it is a divergence, not a distance.'),
    dict(name='Geometric series', field='Mathematics',
         latex=r'\sum_{n=0}^{\infty} r^n = \frac{1}{1-r}',
         slug='Geometric_series',
         must=['S:sum', 'r', 'infty'], nice=['n', 'S:frac', 'S:sup', 'S:sub'],
         blurb='A sum with a constant ratio between terms converges whenever '
               'that ratio is less than one in magnitude. It is the workhorse '
               'behind perturbation expansions and the resolvent of an '
               'operator.'),
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


# ---------------------------------------------------------------- parsing
#
# A small LaTeX math parser producing a tree we can lay out glyph by glyph.
# rosettamath.py parses LaTeX for *meaning* (it wants Python out the other
# end); here we parse the same subset for *shape*, because the UI has to know
# that a fraction is stacked and an exponent is raised.

class Node:
    """One piece of an equation.  kind decides which fields are meaningful."""

    def __init__(self, kind, **kw):
        self.kind = kind
        self.latex = kw.get('latex', '')
        self.text = kw.get('text', '')
        self.children = kw.get('children', [])
        self.base = kw.get('base')
        self.sup = kw.get('sup')
        self.sub = kw.get('sub')
        self.num = kw.get('num')
        self.den = kw.get('den')
        self.body = kw.get('body')
        self.accent = kw.get('accent', '')
        self.left = kw.get('left', '')
        self.right = kw.get('right', '')
        # filled in by the layout pass
        self.w = 0.0
        self.above = 0.0
        self.below = 0.0

    def kids(self):
        out = list(self.children)
        for f in (self.base, self.sup, self.sub, self.num, self.den, self.body):
            if isinstance(f, Node):
                out.append(f)
        return out

    def __repr__(self):
        if self.kind in ('sym', 'num', 'text'):
            return '%s(%s)' % (self.kind, self.text or self.latex)
        return '%s%r' % (self.kind, self.kids())


ACCENTS = {r'\vec': '\u2192', r'\hat': '\u0302', r'\dot': '\u02d9',
           r'\ddot': '\u00a8', r'\bar': '\u00af', r'\tilde': '\u007e',
           r'\overline': '\u00af', r'\widehat': '\u0302'}

# commands that take one braced argument and are otherwise transparent
FONT_CMDS = {r'\text', r'\mathrm', r'\mathbf', r'\mathit', r'\mathcal',
             r'\mathbb', r'\mathsf', r'\operatorname', r'\texttt', r'\textbf'}

# commands we simply drop (spacing, sizing, alignment)
IGNORED = {r'\left', r'\right', r'\big', r'\Big', r'\bigg', r'\Bigg', r'\,',
           r'\;', r'\:', r'\!', r'\quad', r'\qquad', r'\displaystyle',
           r'\limits', r'\nolimits', r'\tiny', r'\small', r'\scriptstyle'}

BIG_OPS = {r'\sum', r'\prod', r'\int', r'\oint', r'\iint', r'\bigcup',
           r'\bigcap', r'\lim'}


def tokenize(s):
    """LaTeX math string -> flat token list."""
    toks = []
    i = 0
    n = len(s)
    while i < n:
        c = s[i]
        if c == '\\':
            j = i + 1
            while j < n and s[j].isalpha():
                j += 1
            if j == i + 1:
                j += 1                       # single-character command like \{
            toks.append(s[i:j])
            i = j
        elif c.isdigit():
            j = i
            while j < n and (s[j].isdigit() or (s[j] == '.' and j + 1 < n
                                                and s[j + 1].isdigit())):
                j += 1
            toks.append(s[i:j])
            i = j
        elif c in ' \t\n':
            i += 1
        else:
            toks.append(c)
            i += 1
    return toks


class Parser:
    def __init__(self, toks):
        self.toks = toks
        self.i = 0

    def peek(self):
        return self.toks[self.i] if self.i < len(self.toks) else None

    def next(self):
        t = self.peek()
        if t is not None:
            self.i += 1
        return t

    def parse_row(self, stop=('}',)):
        items = []
        while True:
            t = self.peek()
            if t is None or t in stop:
                break
            atom = self.parse_atom()
            if atom is None:
                continue
            # attach scripts to the atom just produced
            while self.peek() in ('^', '_'):
                mark = self.next()
                script = self.parse_atom()
                if script is None:
                    break
                if mark == '^':
                    if atom.kind in ('sup', 'sub') and atom.sup is None:
                        atom.sup = script
                    else:
                        atom = Node('script', base=atom, sup=script)
                else:
                    if atom.kind == 'script' and atom.sub is None:
                        atom.sub = script
                    else:
                        atom = Node('script', base=atom, sub=script)
            items.append(atom)
        return Node('row', children=items)

    def parse_group(self):
        """Next atom or braced group, as a row."""
        if self.peek() == '{':
            self.next()
            row = self.parse_row()
            if self.peek() == '}':
                self.next()
            return row
        a = self.parse_atom()
        return Node('row', children=[a] if a else [])

    def parse_atom(self):
        t = self.next()
        if t is None:
            return None
        if t == '{':
            row = self.parse_row()
            if self.peek() == '}':
                self.next()
            return row
        if t == '}':
            return None
        if t.startswith('\\'):
            if t in IGNORED:
                # \left( and \right) still carry a delimiter we want to keep
                if t in (r'\left', r'\right'):
                    d = self.peek()
                    if d in ('(', ')', '[', ']', '|', '.', r'\{', r'\}',
                             r'\langle', r'\rangle'):
                        self.next()
                        if d == '.':
                            return None
                        return Node('sym', latex=d, text=disp(d))
                return None
            if t == r'\frac' or t == r'\dfrac' or t == r'\tfrac':
                return Node('frac', num=self.parse_group(), den=self.parse_group())
            if t == r'\sqrt':
                index = None
                if self.peek() == '[':
                    self.next()
                    idx = []
                    while self.peek() not in (']', None):
                        idx.append(self.next())
                    if self.peek() == ']':
                        self.next()
                    index = Parser(idx).parse_row()
                return Node('sqrt', body=self.parse_group(), sup=index)
            if t in ACCENTS:
                return Node('accent', accent=t, body=self.parse_group(),
                            latex=t)
            if t in FONT_CMDS:
                g = self.parse_group()
                return Node('text', text=flatten_text(g), latex=t)
            if t == r'\begin' or t == r'\end':
                self.parse_group()           # swallow the environment name
                return None
            return Node('sym', latex=t, text=disp(t))
        if t[0].isdigit():
            return Node('num', latex=t, text=t)
        return Node('sym', latex=t, text=t)


# ASCII characters whose maths glyph differs from the keyboard one
DISPLAY_CHARS = {'-': '\u2212', "'": '\u2032'}


def disp(latex):
    """Display text for a command: its unicode if we know it, else the name."""
    if latex in DISPLAY_CHARS:
        return DISPLAY_CHARS[latex]
    e = SYMBOLS.get(latex)
    if e:
        return e['unicode']
    if latex in ACCENTS:
        return ACCENTS[latex]
    if latex.startswith('\\') and len(latex) == 2 and not latex[1].isalpha():
        return latex[1]                      # \{ \} \% \_ ...
    return latex.lstrip('\\')


def flatten_text(node):
    if node is None:
        return ''
    if node.kind in ('sym', 'num', 'text'):
        return node.text
    return ''.join(flatten_text(k) for k in node.kids())


def parse_latex(src):
    """A LaTeX fragment (with or without $ delimiters) -> tree."""
    src = src.strip()
    if src.startswith('$$') and src.endswith('$$'):
        src = src[2:-2]
    elif src.startswith('$') and src.endswith('$') and len(src) > 1:
        src = src[1:-1]
    src = src.replace(r'\\', ' ')
    return Parser(tokenize(src)).parse_row(stop=())


# ---------------------------------------------------------------- features

def extract_features(node, acc=None):
    """Tree -> the token set the equation classifier matches against."""
    if acc is None:
        acc = set()
    if node is None:
        return acc
    k = node.kind
    if k == 'frac':
        acc.add('S:frac')
    elif k == 'sqrt':
        acc.add('S:sqrt')
    elif k == 'accent':
        acc.add('S:' + node.accent.lstrip('\\'))
    elif k == 'script':
        if node.sup is not None:
            acc.add('S:sup')
            if flatten_text(node.sup).strip() == '2':
                acc.add('S:sup2')
            base = flatten_text(node.base).strip()
            if base in ('\u2207', 'nabla'):
                acc.add('S:nabla2')
            if base == 'e':
                acc.add('S:exp_or_e')
        if node.sub is not None:
            acc.add('S:sub')
    elif k in ('sym', 'num', 'text'):
        lx = node.latex or node.text
        if lx.startswith('\\'):
            name = lx.lstrip('\\')
            acc.add(name)
            if lx == r'\nabla':
                acc.add('nabla')
            if lx in (r'\sum',):
                acc.add('S:sum')
            if lx in (r'\prod',):
                acc.add('S:prod')
            if lx in (r'\int', r'\oint', r'\iint'):
                acc.add('S:int')
            if lx == r'\times':
                acc.add('S:times')
            if lx == r'\cdot':
                acc.add('S:cdot')
            if lx == r'\exp':
                acc.add('S:exp_or_e')
        elif len(lx) == 1 and lx.isalpha():
            acc.add(lx)
    for child in node.kids():
        extract_features(child, acc)
    return acc


def nabla_squared_present(node):
    """\nabla^2 written as a script, which extract_features already catches."""
    return 'S:nabla2' in extract_features(node)


def classify(node, raw=''):
    """Rank the equation library against a parsed tree.

    Returns a list of (entry, score, matched_nice) best first.
    """
    feats = extract_features(node)
    if r'\begin{cases}' in raw or 'cases' in raw:
        feats.add('S:cases')
    hits = []
    for eq in EQUATIONS:
        must = set(eq['must'])
        if not must.issubset(feats):
            continue
        nice = set(eq['nice']) & feats
        # specificity: a long must-list matching is much stronger evidence
        score = 2.0 * len(must) + len(nice)
        hits.append((eq, score, sorted(nice)))
    hits.sort(key=lambda h: -h[1])
    return hits[:3]


def family_of(node):
    """Fallback description when nothing in the library matches."""
    feats = extract_features(node)
    for need, text in EQUATION_FAMILIES:
        if set(need).issubset(feats):
            return text
    return ''


def describe_equation(node, raw=''):
    """Plain-text 'this looks like ...' verdict for the tooltip and panel."""
    hits = classify(node, raw)
    if not hits:
        fam = family_of(node)
        if fam:
            return 'Not a match for anything in the library, but this is %s.' % fam
        return 'No match in the equation library.'
    eq, score, nice = hits[0]
    conf = 'looks like' if score >= 8 else 'is similar to'
    out = 'This %s the %s (%s).\n\n%s' % (conf, eq['name'], eq['field'], eq['blurb'])
    if len(hits) > 1:
        out += '\n\nOther candidates: ' + ', '.join(h[0]['name'] for h in hits[1:])
    return out


# ------------------------------------------------- LaTeX -> unicode (offline)

SUPS = {'0': '\u2070', '1': '\u00b9', '2': '\u00b2', '3': '\u00b3',
        '4': '\u2074', '5': '\u2075', '6': '\u2076', '7': '\u2077',
        '8': '\u2078', '9': '\u2079', '+': '\u207a', '-': '\u207b',
        '(': '\u207d', ')': '\u207e', 'n': '\u207f', 'i': '\u2071'}
SUBS = {'0': '\u2080', '1': '\u2081', '2': '\u2082', '3': '\u2083',
        '4': '\u2084', '5': '\u2085', '6': '\u2086', '7': '\u2087',
        '8': '\u2088', '9': '\u2089', '+': '\u208a', '-': '\u208b',
        '(': '\u208d', ')': '\u208e', 'a': '\u2090', 'e': '\u2091',
        'i': '\u1d62', 'o': '\u2092', 'x': '\u2093', 'n': '\u2099',
        'p': '\u209a', 's': '\u209b', 't': '\u209c', 'm': '\u2098'}


def to_unicode(node):
    """Best-effort unicode rendering of a tree.

    Good enough for tooltips and list entries; genuinely stacked things like
    fractions degrade to an inline slash, which is why the popup also offers a
    real pdflatex-typeset image.
    """
    if node is None:
        return ''
    k = node.kind
    if k == 'row':
        return ''.join(to_unicode(c) for c in node.children)
    if k in ('sym', 'num', 'text'):
        return node.text or disp(node.latex)
    if k == 'frac':
        return '(%s)/(%s)' % (to_unicode(node.num), to_unicode(node.den))
    if k == 'sqrt':
        return '\u221a(%s)' % to_unicode(node.body)
    if k == 'accent':
        return to_unicode(node.body) + ACCENTS.get(node.accent, '')
    if k == 'script':
        out = to_unicode(node.base)
        if node.sub is not None:
            s = to_unicode(node.sub)
            out += ''.join(SUBS.get(ch, ch) for ch in s) if all(
                ch in SUBS for ch in s) else '_' + s
        if node.sup is not None:
            s = to_unicode(node.sup)
            out += ''.join(SUPS.get(ch, ch) for ch in s) if all(
                ch in SUPS for ch in s) else '^' + s
        return out
    return ''.join(to_unicode(c) for c in node.kids())


def latex_to_unicode(src):
    return to_unicode(parse_latex(src))


# ------------------------------------------------- LaTeX -> PNG (pdflatex)

CACHE_DIR = os.path.join(tempfile.gettempdir(), 'rosettaui-cache')

TEX_DOC = r'''\documentclass[12pt]{article}
\usepackage[margin=1cm,paperwidth=20cm,paperheight=6cm]{geometry}
\usepackage{amsmath,amssymb}
\pagestyle{empty}
\begin{document}
\noindent\[ %s \]
\end{document}
'''


def have_tools():
    """(pdflatex, rasteriser) availability, for graceful degradation.

    ImageMagick's `convert` hands PDFs to Ghostscript, which is often not
    installed; poppler's pdftoppm/pdftocairo rasterise them directly and are
    far more commonly present.  Try whatever is here.
    """
    raster = (shutil.which('pdftoppm') or shutil.which('pdftocairo') or
              shutil.which('magick') or shutil.which('convert'))
    return shutil.which('pdflatex') is not None, raster


def _rasterise(pdf, png, density):
    """PDF -> PNG by whichever backend exists.  True on success."""
    tool = shutil.which('pdftoppm')
    if tool:
        # -singlefile makes it write exactly png, not png-1.png
        stem = png[:-4] if png.endswith('.png') else png
        if _run([tool, '-png', '-r', str(density), '-singlefile', pdf, stem]):
            return os.path.exists(png)
    tool = shutil.which('pdftocairo')
    if tool:
        stem = png[:-4] if png.endswith('.png') else png
        if _run([tool, '-png', '-r', str(density), '-singlefile', pdf, stem]):
            return os.path.exists(png)
    tool = shutil.which('magick') or shutil.which('convert')
    if tool:
        cmd = [tool]
        if os.path.basename(tool) == 'magick':
            cmd.append('convert')
        cmd += ['-density', str(density), pdf, '-quality', '90', png]
        if _run(cmd):
            return os.path.exists(png)
    return False


def _trim(png):
    """Crop the page margins away if ImageMagick is around.  Best effort."""
    tool = shutil.which('magick') or shutil.which('convert')
    if not tool:
        return
    cmd = [tool]
    if os.path.basename(tool) == 'magick':
        cmd.append('convert')
    cmd += [png, '-trim', '+repage', '-bordercolor', 'white', '-border', '14',
            png]
    _run(cmd)


def _run(cmd, cwd=None, timeout=60):
    try:
        subprocess.run(cmd, cwd=cwd, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, timeout=timeout, check=True)
        return True
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired, OSError):
        return False


def render_latex_png(src, density=200):
    """Typeset a fragment with pdflatex and rasterise it.  None on failure.

    QTextEdit cannot render LaTeX, so for anything the unicode approximation
    mangles -- stacked fractions, big operators, matrices -- we shell out to
    the real typesetter and show the result as an image.
    """
    has_tex, raster = have_tools()
    if not has_tex or not raster:
        return None
    src = src.strip().strip('$')
    if not src:
        return None
    os.makedirs(CACHE_DIR, exist_ok=True)
    key = hashlib.md5(('%s|%d' % (src, density)).encode('utf-8')).hexdigest()
    png = os.path.join(CACHE_DIR, key + '.png')
    if os.path.exists(png):
        return png
    work = tempfile.mkdtemp(prefix='rosettaui-')
    try:
        with open(os.path.join(work, 'eq.tex'), 'w') as fh:
            fh.write(TEX_DOC % src)
        if not _run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error',
                     'eq.tex'], cwd=work, timeout=30):
            return None
        if not _rasterise(os.path.join(work, 'eq.pdf'), png, density):
            return None
        _trim(png)
    finally:
        shutil.rmtree(work, ignore_errors=True)
    return png if os.path.exists(png) else None


# ------------------------------------------------- rosettamath bridge

def to_python(src):
    """Run the equation through rosettamath and return the generated Python."""
    src = src.strip()
    try:
        if '\\State' in src or '\\Function' in src:
            return rosettamath.tex2py(src)
        if '$' not in src:
            src = '$' + src + '$'
        return rosettamath.eq2py(src)
    except Exception as exc:                 # a partial equation is not a crash
        return '# rosettamath could not translate this:\n# %s: %s' % (
            type(exc).__name__, exc)


def python_health(py):
    """Does the generated Python actually compile?

    Worth surfacing rather than hiding: an equation that will not translate
    cleanly is usually relying on a convention the reader is supposed to
    supply, and saying which one is the teachable moment.
    """
    if py.lstrip().startswith('#'):
        return False, 'rosettamath could not translate this fragment.'
    try:
        compile(py, '<rosettamath>', 'exec')
        return True, ''
    except SyntaxError as exc:
        hint = ''
        first = py.splitlines()[0] if py.splitlines() else ''
        if first.startswith('def ') and '(' not in first:
            hint = ('The left-hand side is a bare symbol rather than f(x), so '
                    'rosettamath has nothing to use as a parameter list. Write '
                    'the equation in function form -- S(A) = ... -- to get a '
                    'callable back.')
        elif 'invalid syntax' in str(exc):
            hint = ('Two names sit next to each other with nothing between '
                    'them. Implicit multiplication is obvious to a reader but '
                    'not to a parser; make it explicit with \\cdot.')
        return False, ('This does not compile as Python (%s). %s'
                       % (exc.msg, hint)).strip()


def from_python(source_code):
    """Reverse direction, via rosettamath's Python2Tex."""
    try:
        return rosettamath.py2tex(source_code)
    except Exception as exc:
        return '%% py2tex failed: %s: %s' % (type(exc).__name__, exc)


# ---------------------------------------------------------------- Qt layer

try:
    from PyQt5.QtCore import Qt, QRectF, QTimer
    from PyQt5.QtGui import (QFont, QFontMetricsF, QColor, QCursor, QPainter,
                             QBrush, QPen, QPixmap, QKeySequence, QPainterPath)
    from PyQt5.QtWidgets import (QApplication, QMainWindow, QGraphicsView,
                                 QGraphicsScene, QGraphicsSimpleTextItem,
                                 QGraphicsRectItem, QGraphicsPathItem,
                                 QGraphicsItem, QMenu,
                                 QDialog, QVBoxLayout, QHBoxLayout, QTextEdit,
                                 QPushButton, QLabel, QLineEdit, QTabWidget,
                                 QListWidget, QSplitter, QWidget, QAction,
                                 QScrollArea, QMessageBox, QFileDialog,
                                 QPlainTextEdit, QListWidgetItem, QComboBox)
    QT_OK = True
except ImportError as _exc:                  # --selftest still works
    QT_OK = False
    QT_ERROR = str(_exc)


# role -> colour.  Colour-coding the roles is itself a teaching device: it
# makes visible the distinction between a variable, a constant and an operator
# that mathematical typesetting leaves implicit.
ROLE_COLOURS = {
    'greek': '#6a3d9a',
    'constant': '#0f7b6c',
    'operator': '#8a5000',
    'relation': '#8a5000',
    'variable': '#1a1a2e',
    'number': '#333333',
    'function': '#1f5fa0',
    'structure': '#555555',
}
HOVER_COLOUR = '#c1121f'


def role_of(node):
    """Classify a leaf for colouring and for the tooltip's 'Role:' line."""
    if node.kind == 'num':
        return 'number'
    lx = node.latex or node.text
    entry = SYMBOLS.get(lx)
    if entry:
        cat = entry['category']
        if cat == 'Greek letters':
            return 'greek'
        if cat == 'Constants':
            return 'constant'
        if cat in ('Relations',):
            return 'relation'
        if cat in ('Operators', 'Calculus', 'Set theory', 'Logic', 'Quantum'):
            return 'operator'
        if cat == 'Functions':
            return 'function'
        if cat == 'Structures':
            return 'structure'
        return 'variable'
    if lx in '+-=<>/*':
        return 'relation'
    if lx in '()[]{},':
        return 'structure'
    if len(lx) == 1 and lx.isalpha():
        return 'variable'
    return 'structure'


def lookup(node):
    """The knowledge-base entry for a leaf, or None."""
    if node is None:
        return None
    return SYMBOLS.get(node.latex) or SYMBOLS.get(node.text)


def tooltip_for(node):
    """The hover text: name, origin, and conventional meaning."""
    entry = lookup(node)
    role = role_of(node)
    if entry is None:
        txt = node.text or node.latex
        if node.kind == 'num':
            return 'Numeric literal %s\nRole: number' % txt
        return ('%s\nRole: %s\nNo entry in the glossary yet -- right-click to '
                'search Wikipedia.' % (txt, role))
    blurb = entry['blurb']
    if len(blurb) > 320:
        blurb = blurb[:317].rsplit(' ', 1)[0] + '...'
    lines = ['%s   (%s)' % (entry['name'], entry['unicode']),
             'LaTeX: %s     Role: %s' % (entry['latex'], role),
             'Category: %s' % entry['category'], '', blurb, '',
             'Left-click for the full description, right-click for Wikipedia.']
    return '\n'.join(lines)


if QT_OK:

    class Glyph(QGraphicsSimpleTextItem):
        """One interactive character of the equation."""

        def __init__(self, text, node, ui, size, italic=False):
            super().__init__(text)
            self.node = node
            self.ui = ui
            self.role = role_of(node)
            font = QFont(pick_family(SERIF_STACK), int(size))
            font.setItalic(italic)
            self.setFont(font)
            self.base_colour = QColor(ROLE_COLOURS.get(self.role, '#000000'))
            self.setBrush(QBrush(self.base_colour))
            self.setAcceptHoverEvents(True)
            self.setCursor(QCursor(Qt.PointingHandCursor))
            self.setToolTip(tooltip_for(node))
            self.setFlag(QGraphicsItem.ItemIsSelectable, False)

        def hoverEnterEvent(self, event):
            self.setBrush(QBrush(QColor(HOVER_COLOUR)))
            entry = lookup(self.node)
            if self.ui is not None:
                self.ui.status(entry['name'] + ' -- ' + entry['blurb'][:110]
                               if entry else (self.node.text or self.node.latex))
            super().hoverEnterEvent(event)

        def hoverLeaveEvent(self, event):
            self.setBrush(QBrush(self.base_colour))
            super().hoverLeaveEvent(event)

        def mousePressEvent(self, event):
            if event.button() == Qt.LeftButton and self.ui is not None:
                self.ui.explain_symbol(self.node)
            super().mousePressEvent(event)

        def contextMenuEvent(self, event):
            if self.ui is not None:
                self.ui.symbol_context_menu(self.node, event.screenPos())
            event.accept()

    class Rule(QGraphicsRectItem):
        """A fraction bar or radical stroke -- clickable, like a glyph."""

        def __init__(self, w, h, node, ui, tip):
            super().__init__(0, 0, w, h)
            self.node = node
            self.ui = ui
            self.setBrush(QBrush(QColor('#1a1a2e')))
            self.setPen(QPen(Qt.NoPen))
            self.setAcceptHoverEvents(True)
            self.setCursor(QCursor(Qt.PointingHandCursor))
            self.setToolTip(tip)

        def hoverEnterEvent(self, event):
            self.setBrush(QBrush(QColor(HOVER_COLOUR)))
            super().hoverEnterEvent(event)

        def hoverLeaveEvent(self, event):
            self.setBrush(QBrush(QColor('#1a1a2e')))
            super().hoverLeaveEvent(event)

        def mousePressEvent(self, event):
            if event.button() == Qt.LeftButton and self.ui is not None:
                self.ui.explain_symbol(self.node)
            super().mousePressEvent(event)

        def contextMenuEvent(self, event):
            if self.ui is not None:
                self.ui.symbol_context_menu(self.node, event.screenPos())
            event.accept()

    class Radical(QGraphicsPathItem):
        """A square-root sign drawn to fit its contents.

        A glyph cannot do this: the surd has to grow with whatever is under
        it, so it is a path -- tick, diagonal, then the bar over the top.
        """

        def __init__(self, width, height, surd, thickness, node, ui, tip):
            super().__init__()
            path = QPainterPath()
            path.moveTo(0.0, height * 0.66)
            path.lineTo(surd * 0.28, height * 0.56)
            path.lineTo(surd * 0.50, height * 0.98)
            path.lineTo(surd * 0.86, height * 0.02)
            path.lineTo(width, 0.0)
            self.setPath(path)
            self.node = node
            self.ui = ui
            self.base_pen = QPen(QColor('#1a1a2e'), thickness)
            self.base_pen.setJoinStyle(Qt.MiterJoin)
            self.setPen(self.base_pen)
            self.setBrush(QBrush(Qt.NoBrush))
            self.setAcceptHoverEvents(True)
            self.setCursor(QCursor(Qt.PointingHandCursor))
            self.setToolTip(tip)

        def hoverEnterEvent(self, event):
            self.setPen(QPen(QColor(HOVER_COLOUR), self.base_pen.widthF()))
            super().hoverEnterEvent(event)

        def hoverLeaveEvent(self, event):
            self.setPen(self.base_pen)
            super().hoverLeaveEvent(event)

        def mousePressEvent(self, event):
            if event.button() == Qt.LeftButton and self.ui is not None:
                self.ui.explain_symbol(self.node)
            super().mousePressEvent(event)

        def contextMenuEvent(self, event):
            if self.ui is not None:
                self.ui.symbol_context_menu(self.node, event.screenPos())
            event.accept()

    class MathLayout:
        """Two-pass layout: measure the tree, then place real items.

        Measuring first is what lets fractions and roots size themselves around
        their contents instead of guessing.
        """

        SCRIPT = 0.72          # font ratio for scripts
        MIN_SIZE = 7.0

        def __init__(self, scene, ui, base_size=34.0):
            self.scene = scene
            self.ui = ui
            self.base_size = base_size

        # -- metrics -----------------------------------------------------
        def metrics(self, size, italic=False):
            font = QFont(pick_family(SERIF_STACK), int(size))
            font.setItalic(italic)
            return QFontMetricsF(font)

        def is_italic(self, node):
            """Single Latin letters are italic in maths; operators are not."""
            if node.kind != 'sym':
                return False
            t = node.latex or node.text
            return len(t) == 1 and t.isalpha()

        @staticmethod
        def starts_with_rule(node):
            """Does this subtree draw a horizontal line along its top edge?"""
            while node is not None and node.kind == 'row':
                node = node.children[0] if node.children else None
            return node is not None and node.kind in ('sqrt', 'frac')

        def gap_before(self, node):
            """Thin space around relations and binary operators."""
            t = (node.latex or node.text)
            if t in ('=', '+', '-', '<', '>') or t in (
                    r'\pm', r'\mp', r'\neq', r'\leq', r'\geq', r'\approx',
                    r'\equiv', r'\propto', r'\to', r'\in', r'\land', r'\lor',
                    r'\cdot', r'\times', r'\sim', r'\ll', r'\gg'):
                return 0.28
            return 0.06

        # -- pass 1 ------------------------------------------------------
        def measure(self, node, size):
            if node is None:
                return
            k = node.kind
            if k == 'row':
                w = 0.0
                above = below = 0.0
                for idx, child in enumerate(node.children):
                    self.measure(child, size)
                    if idx:
                        w += self.gap_before(child) * size
                    w += child.w
                    above = max(above, child.above)
                    below = max(below, child.below)
                if not node.children:
                    fm = self.metrics(size)
                    above, below = fm.ascent() * 0.7, fm.descent()
                node.w, node.above, node.below = w, above, below

            elif k in ('sym', 'num', 'text'):
                italic = self.is_italic(node)
                fm = self.metrics(size, italic)
                text = node.text or node.latex
                text = DISPLAY_CHARS.get(text, text) if node.kind == 'sym' \
                    else text
                node.w = fm.horizontalAdvance(text)
                node.above = fm.ascent()
                node.below = fm.descent()
                node._size = size
                node._italic = italic
                node._draw = text

            elif k == 'frac':
                s2 = max(size * 0.95, self.MIN_SIZE)
                self.measure(node.num, s2)
                self.measure(node.den, s2)
                pad = size * 0.22
                node.w = max(node.num.w, node.den.w) + 2 * pad
                axis = self.metrics(size).ascent() * 0.30
                gap = size * 0.26
                # a nested root or fraction puts its own horizontal rule right
                # against ours, so give those extra clearance
                if self.starts_with_rule(node.den):
                    gap += size * 0.22
                node.above = axis + gap + node.num.above + node.num.below
                node.below = -axis + gap + node.den.above + node.den.below
                node._axis = axis
                node._pad = pad
                node._gap = gap

            elif k == 'sqrt':
                self.measure(node.body, size)
                if node.sup is not None:
                    self.measure(node.sup, max(size * 0.55, self.MIN_SIZE))
                node.above = node.body.above + size * 0.34
                node.below = node.body.below + size * 0.08
                # the hook has to widen as it gets taller or it degenerates
                # into a thin spike
                height = node.above + node.below
                surd = max(size * 0.55, height * 0.26)
                node.w = node.body.w + surd + size * 0.28
                node._surd = surd

            elif k == 'accent':
                self.measure(node.body, size)
                node.w = node.body.w
                node.above = node.body.above + size * 0.30
                node.below = node.body.below
                node._size = size

            elif k == 'script':
                self.measure(node.base, size)
                ssize = max(size * self.SCRIPT, self.MIN_SIZE)
                wsup = wsub = 0.0
                rise = drop = 0.0
                if node.sup is not None:
                    self.measure(node.sup, ssize)
                    wsup = node.sup.w
                    rise = node.base.above * 0.48
                if node.sub is not None:
                    self.measure(node.sub, ssize)
                    wsub = node.sub.w
                    drop = node.base.below + size * 0.12
                node.w = node.base.w + max(wsup, wsub) + size * 0.04
                node.above = max(node.base.above,
                                 rise + (node.sup.above if node.sup else 0))
                node.below = max(node.base.below,
                                 drop + (node.sub.below if node.sub else 0))
                node._rise = rise
                node._drop = drop
                node._ssize = ssize
            else:
                node.w = node.above = node.below = 0.0

        # -- pass 2 ------------------------------------------------------
        def place(self, node, x, baseline):
            """Create the scene items.  x is the left edge, baseline the y."""
            if node is None:
                return
            k = node.kind
            if k == 'row':
                cx = x
                for idx, child in enumerate(node.children):
                    if idx:
                        cx += self.gap_before(child) * self.base_size
                    self.place(child, cx, baseline)
                    cx += child.w

            elif k in ('sym', 'num', 'text'):
                item = Glyph(node._draw, node, self.ui, node._size,
                             getattr(node, '_italic', False))
                item.setPos(x, baseline - node.above)
                self.scene.addItem(item)

            elif k == 'frac':
                bar_y = baseline - node._axis
                cx = x + node._pad
                nx = cx + (node.w - 2 * node._pad - node.num.w) / 2.0
                dx = cx + (node.w - 2 * node._pad - node.den.w) / 2.0
                self.place(node.num, nx,
                           bar_y - node._gap - node.num.below)
                self.place(node.den, dx,
                           bar_y + node._gap + node.den.above)
                rule = Rule(node.w, max(1.6, self.base_size * 0.045), node,
                            self.ui, tooltip_for(Node('sym', latex='\\frac')))
                rule.setPos(x, bar_y)
                self.scene.addItem(rule)

            elif k == 'sqrt':
                surd = node._surd
                top = baseline - node.above
                height = node.above + node.below
                snode = Node('sym', latex='\\sqrt', text='\u221a')
                rad = Radical(node.w, height, surd,
                              max(1.4, self.base_size * 0.042), snode, self.ui,
                              tooltip_for(snode))
                rad.setPos(x, top)
                self.scene.addItem(rad)
                self.place(node.body, x + surd + self.base_size * 0.12, baseline)
                if node.sup is not None:
                    self.place(node.sup, x + surd * 0.15,
                               top + node.sup.above * 0.9)

            elif k == 'accent':
                self.place(node.body, x, baseline)
                mark = ACCENTS.get(node.accent, '^')
                item = Glyph(mark, Node('sym', latex=node.accent, text=mark),
                             self.ui, node._size * 0.9)
                item.setPos(x + node.body.w / 2.0 - node._size * 0.22,
                            baseline - node.above - node._size * 0.12)
                self.scene.addItem(item)

            elif k == 'script':
                self.place(node.base, x, baseline)
                sx = x + node.base.w + self.base_size * 0.02
                if node.sup is not None:
                    self.place(node.sup, sx, baseline - node._rise)
                if node.sub is not None:
                    self.place(node.sub, sx, baseline + node._drop)

        def render(self, node):
            self.measure(node, self.base_size)
            self.place(node, 0.0, node.above)
            return node


# ---------------------------------------------------------------- HTML views

CSS = """
<style>
body { font-family: serif; font-size: 11pt; color: #1a1a2e; }
h2 { margin-bottom: 2px; }
.sub { color: #666; font-size: 9pt; margin-top: 0; }
.uni { font-size: 24pt; color: #6a3d9a; }
.tex { font-family: monospace; background: #f0f0f0; padding: 1px 4px; }
.tag { color: #0f7b6c; font-size: 9pt; }
</style>
"""


def esc(s):
    return html.escape(s, quote=False)


def _wrap(text, width):
    """Crude word wrap, so the note lines up as a Python comment block."""
    words = text.split()
    lines, cur = [], ''
    for w in words:
        if cur and len(cur) + 1 + len(w) > width:
            lines.append(cur)
            cur = w
        else:
            cur = (cur + ' ' + w).strip()
    if cur:
        lines.append(cur)
    return lines


def symbol_html(entry, node=None):
    if entry is None:
        t = (node.text or node.latex) if node else '?'
        return CSS + ('<h2>%s</h2><p class="sub">Not in the glossary yet.</p>'
                      '<p>Right-click it to search Wikipedia, or add an entry '
                      'to the SYMBOLS table in rosettaui.py.</p>' % esc(t))
    return CSS + """
<h2>%s</h2>
<p class="sub">%s</p>
<p><span class="uni">%s</span> &nbsp; <span class="tex">%s</span></p>
<p>%s</p>
<p class="tag">Wikipedia: %s</p>
""" % (esc(entry['name']), esc(entry['category']), esc(entry['unicode']),
       esc(entry['latex']), esc(entry['blurb']), esc(entry['wiki']))


def concept_html(c):
    body = ''.join('<p>%s</p>' % esc(p.strip().replace('\n', ' '))
                   for p in c['body'].split('\n\n') if p.strip())
    rel = ''
    if c['symbols']:
        parts = []
        for s in c['symbols']:
            e = SYMBOLS.get(s)
            if e:
                parts.append('%s (%s)' % (e['unicode'], e['name']))
        if parts:
            rel = '<p class="tag">Related symbols: %s</p>' % esc(', '.join(parts))
    return CSS + '<h2>%s</h2><p class="sub">%s</p>%s%s<p class="tag">%s</p>' % (
        esc(c['title']), esc(c['category']), body, rel, esc(c['wiki']))


def equation_html(eq):
    return CSS + """
<h2>%s</h2>
<p class="sub">%s</p>
<p><span class="uni">%s</span></p>
<p><span class="tex">%s</span></p>
<p>%s</p>
<p class="tag">Wikipedia: %s</p>
""" % (esc(eq['name']), esc(eq['field']), esc(latex_to_unicode(eq['latex'])),
       esc(eq['latex']), esc(eq['blurb']), esc(WIKI + eq['slug']))


if QT_OK:

    class InfoDialog(QDialog):
        """Offline explanation popup: our own text, plus optional real typeset."""

        def __init__(self, parent, title, body_html, wiki=None, tex=None):
            super().__init__(parent)
            self.setWindowTitle(title)
            self.resize(560, 460)
            self.wiki = wiki
            self.tex = tex
            lay = QVBoxLayout(self)

            self.view = QTextEdit()
            self.view.setReadOnly(True)
            self.view.setHtml(body_html)
            lay.addWidget(self.view)

            self.image = QLabel()
            self.image.setAlignment(Qt.AlignCenter)
            self.image.hide()
            lay.addWidget(self.image)

            row = QHBoxLayout()
            if wiki:
                b = QPushButton('Open Wikipedia')
                b.clicked.connect(lambda: webbrowser.open(wiki))
                row.addWidget(b)
            if tex:
                has_tex, conv = have_tools()
                b = QPushButton('Typeset with pdflatex')
                b.setEnabled(bool(has_tex and conv))
                if not (has_tex and conv):
                    b.setToolTip('Needs pdflatex plus pdftoppm or ImageMagick')
                b.clicked.connect(self.typeset)
                row.addWidget(b)
            row.addStretch(1)
            close = QPushButton('Close')
            close.clicked.connect(self.accept)
            row.addWidget(close)
            lay.addLayout(row)

        def typeset(self):
            """QTextEdit cannot render LaTeX, so shell out and show a PNG."""
            png = render_latex_png(self.tex)
            if not png:
                QMessageBox.warning(self, 'Typesetting failed',
                                    'pdflatex or ImageMagick could not render '
                                    'this fragment.')
                return
            pix = QPixmap(png)
            if pix.width() > 520:
                pix = pix.scaledToWidth(520, Qt.SmoothTransformation)
            self.image.setPixmap(pix)
            self.image.show()

    class BrowserDialog(QDialog):
        """The mini offline encyclopedia: filterable list plus article pane."""

        def __init__(self, parent, title, entries, to_html, get_wiki,
                     get_tex=None):
            super().__init__(parent)
            self.setWindowTitle(title)
            self.resize(880, 560)
            self.entries = entries
            self.to_html = to_html
            self.get_wiki = get_wiki
            self.get_tex = get_tex

            lay = QVBoxLayout(self)
            self.filter = QLineEdit()
            self.filter.setPlaceholderText('Filter...')
            self.filter.textChanged.connect(self.refill)
            lay.addWidget(self.filter)

            split = QSplitter(Qt.Horizontal)
            self.list = QListWidget()
            self.list.currentRowChanged.connect(self.show_current)
            split.addWidget(self.list)
            self.text = QTextEdit()
            self.text.setReadOnly(True)
            split.addWidget(self.text)
            split.setSizes([260, 620])
            lay.addWidget(split)

            row = QHBoxLayout()
            self.wiki_btn = QPushButton('Open Wikipedia')
            self.wiki_btn.clicked.connect(self.open_wiki)
            row.addWidget(self.wiki_btn)
            if get_tex is not None:
                self.load_btn = QPushButton('Load into the viewer')
                self.load_btn.clicked.connect(self.load_into_viewer)
                row.addWidget(self.load_btn)
            row.addStretch(1)
            close = QPushButton('Close')
            close.clicked.connect(self.accept)
            row.addWidget(close)
            lay.addLayout(row)

            self.shown = []
            self.refill('')

        def refill(self, text=''):
            text = text.lower().strip()
            self.list.clear()
            self.shown = []
            for label, obj in self.entries:
                if text and text not in label.lower() and \
                        text not in str(obj).lower():
                    continue
                self.shown.append(obj)
                self.list.addItem(QListWidgetItem(label))
            if self.shown:
                self.list.setCurrentRow(0)

        def current(self):
            r = self.list.currentRow()
            return self.shown[r] if 0 <= r < len(self.shown) else None

        def show_current(self, _row=None):
            obj = self.current()
            if obj is not None:
                self.text.setHtml(self.to_html(obj))

        def open_wiki(self):
            obj = self.current()
            if obj is not None:
                webbrowser.open(self.get_wiki(obj))

        def load_into_viewer(self):
            obj = self.current()
            if obj is not None and self.parent() is not None:
                self.parent().load(self.get_tex(obj))
                self.accept()

    class EquationView(QGraphicsView):
        """Graphics view that hands empty-space right-clicks to the window."""

        def __init__(self, scene, ui):
            super().__init__(scene)
            self.ui = ui
            self.setRenderHint(QPainter.Antialiasing)
            self.setRenderHint(QPainter.TextAntialiasing)

        def contextMenuEvent(self, event):
            if self.itemAt(event.pos()) is None:
                self.ui.equation_context_menu(event.globalPos())
                event.accept()
            else:
                super().contextMenuEvent(event)


DEFAULT_EQUATION = r'-\frac{\hbar^2}{2m} \nabla^2 \psi + V \psi = E \psi'


if QT_OK:

    class RosettaWindow(QMainWindow):

        def __init__(self, initial=DEFAULT_EQUATION):
            super().__init__()
            self.setWindowTitle('RosettaUI -- interactive LaTeX for RosettaMath')
            self.resize(1180, 700)
            self.current_tex = ''
            self.tree = None

            central = QWidget()
            outer = QVBoxLayout(central)

            # --- input row
            row = QHBoxLayout()
            row.addWidget(QLabel('LaTeX:'))
            self.entry = QLineEdit()
            self.entry.setFont(QFont(pick_family(MONO_STACK), 11))
            self.entry.returnPressed.connect(self.render_from_entry)
            row.addWidget(self.entry, 1)
            btn = QPushButton('Render')
            btn.clicked.connect(self.render_from_entry)
            row.addWidget(btn)
            self.picker = QComboBox()
            self.picker.addItem('-- jump to an equation --', '')
            for eq in EQUATIONS:
                self.picker.addItem('%s  (%s)' % (eq['name'], eq['field']),
                                    eq['latex'])
            self.picker.currentIndexChanged.connect(self.pick_equation)
            row.addWidget(self.picker)
            outer.addLayout(row)

            # --- viewer + panels
            split = QSplitter(Qt.Horizontal)
            self.scene = QGraphicsScene(self)
            self.scene.setBackgroundBrush(QColor(252, 251, 248))
            self.view = EquationView(self.scene, self)
            split.addWidget(self.view)

            self.tabs = QTabWidget()
            self.sym_panel = QTextEdit(); self.sym_panel.setReadOnly(True)
            self.eq_panel = QTextEdit(); self.eq_panel.setReadOnly(True)
            self.py_panel = QPlainTextEdit(); self.py_panel.setReadOnly(True)
            self.py_panel.setFont(QFont(pick_family(MONO_STACK), 10))
            self.tabs.addTab(self.sym_panel, 'Symbol')
            self.tabs.addTab(self.eq_panel, 'This equation')
            self.tabs.addTab(self.py_panel, 'Python (rosettamath)')
            split.addWidget(self.tabs)
            split.setSizes([700, 470])
            outer.addWidget(split, 1)

            self.setCentralWidget(central)
            self.statusBar().showMessage('Hover a symbol; left-click to explain, '
                                         'right-click for Wikipedia.')
            self.build_menus()
            self.load(initial)

        # ---------------------------------------------------------- menus
        def build_menus(self):
            bar = self.menuBar()

            m = bar.addMenu('&File')
            a = QAction('Export equation as PNG...', self)
            a.triggered.connect(self.export_png)
            m.addAction(a)
            a = QAction('Typeset this equation with pdflatex', self)
            a.triggered.connect(self.typeset_current)
            m.addAction(a)
            m.addSeparator()
            a = QAction('Quit', self)
            a.setShortcut(QKeySequence.Quit)
            a.triggered.connect(self.close)
            m.addAction(a)

            # equations grouped by field
            m = bar.addMenu('&Equations')
            fields = {}
            for eq in EQUATIONS:
                fields.setdefault(eq['field'], []).append(eq)
            for field in sorted(fields):
                sub = m.addMenu(field)
                for eq in fields[field]:
                    a = QAction(eq['name'], self)
                    a.triggered.connect(
                        lambda _c=False, t=eq['latex']: self.load(t))
                    sub.addAction(a)
            m.addSeparator()
            a = QAction('Browse all equations...', self)
            a.triggered.connect(self.browse_equations)
            m.addAction(a)

            # concepts grouped by category
            m = bar.addMenu('&Concepts')
            cats = {}
            for c in CONCEPTS.values():
                cats.setdefault(c['category'], []).append(c)
            for cat in sorted(cats):
                sub = m.addMenu(cat)
                for c in sorted(cats[cat], key=lambda c: c['title']):
                    a = QAction(c['title'], self)
                    a.triggered.connect(
                        lambda _c=False, t=c['title']: self.show_concept(t))
                    sub.addAction(a)
            m.addSeparator()
            a = QAction('Browse all concepts...', self)
            a.triggered.connect(self.browse_concepts)
            m.addAction(a)

            # symbols grouped by category
            m = bar.addMenu('&Symbols')
            cats = {}
            for e in SYMBOLS.values():
                cats.setdefault(e['category'], []).append(e)
            for cat in sorted(cats):
                sub = m.addMenu(cat)
                for e in sorted(cats[cat], key=lambda e: e['name']):
                    a = QAction('%s   %s' % (e['unicode'], e['name']), self)
                    a.triggered.connect(
                        lambda _c=False, k=e['latex']: self.show_symbol_entry(k))
                    sub.addAction(a)
            m.addSeparator()
            a = QAction('Browse all symbols...', self)
            a.triggered.connect(self.browse_symbols)
            m.addAction(a)

            m = bar.addMenu('&Tools')
            a = QAction('Python -> LaTeX (py2tex)...', self)
            a.triggered.connect(self.python_to_latex)
            m.addAction(a)
            a = QAction('Run rosettamath self test', self)
            a.triggered.connect(self.run_selftest)
            m.addAction(a)

            m = bar.addMenu('&Help')
            a = QAction('About RosettaUI', self)
            a.triggered.connect(self.about)
            m.addAction(a)

        # ---------------------------------------------------------- loading
        def status(self, msg):
            self.statusBar().showMessage(msg)

        def pick_equation(self, idx):
            tex = self.picker.itemData(idx)
            if tex:
                self.load(tex)

        def render_from_entry(self):
            self.load(self.entry.text())

        def load(self, tex):
            """Parse, lay out and analyse a new equation."""
            tex = (tex or '').strip()
            if not tex:
                return
            self.current_tex = tex
            if self.entry.text() != tex:
                self.entry.setText(tex)
            self.scene.clear()
            try:
                self.tree = parse_latex(tex)
                MathLayout(self.scene, self).render(self.tree)
            except Exception as exc:
                self.tree = None
                item = QGraphicsSimpleTextItem('parse error: %s' % exc)
                self.scene.addItem(item)
                self.status('Could not parse that fragment.')
            rect = self.scene.itemsBoundingRect()
            self.scene.setSceneRect(rect.adjusted(-30, -30, 30, 30))
            self.view.fitInView(self.scene.sceneRect(), Qt.KeepAspectRatio)
            self.update_equation_panel()
            self.update_python_panel()

        def resizeEvent(self, event):
            super().resizeEvent(event)
            if self.scene.sceneRect().width():
                self.view.fitInView(self.scene.sceneRect(), Qt.KeepAspectRatio)

        # ---------------------------------------------------------- panels
        def update_equation_panel(self):
            if self.tree is None:
                return
            verdict = describe_equation(self.tree, self.current_tex)
            hits = classify(self.tree, self.current_tex)
            feats = sorted(extract_features(self.tree))
            body = CSS + '<h2>This equation</h2><p class="sub">%s</p>' % \
                esc(latex_to_unicode(self.current_tex))
            body += ''.join('<p>%s</p>' % esc(p) for p in verdict.split('\n\n'))
            if hits:
                eq = hits[0][0]
                body += '<p class="tag">Wikipedia: %s</p>' % esc(WIKI + eq['slug'])
            body += '<p class="tag">Detected features: %s</p>' % esc(
                ', '.join(feats))
            self.eq_panel.setHtml(body)

        def update_python_panel(self):
            py = to_python(self.current_tex)
            ok, note = python_health(py)
            head = '# generated by rosettamath from:\n# %s\n' % self.current_tex
            if ok:
                head += '# this compiles and can be exec\'d\n'
            else:
                head += '#\n# NOTE: ' + '\n#       '.join(
                    _wrap(note, 66)) + '\n'
            self.py_panel.setPlainText(head + '\n' + py)

        # ---------------------------------------------------------- actions
        def explain_symbol(self, node):
            entry = lookup(node)
            self.sym_panel.setHtml(symbol_html(entry, node))
            self.tabs.setCurrentIndex(0)
            title = entry['name'] if entry else (node.text or node.latex)
            dlg = InfoDialog(self, title, symbol_html(entry, node),
                             wiki=entry['wiki'] if entry else None,
                             tex=(entry['latex'] if entry else None))
            dlg.exec_()

        def show_symbol_entry(self, latex):
            self.explain_symbol(Node('sym', latex=latex, text=disp(latex)))

        def show_concept(self, title):
            c = CONCEPTS[title]
            InfoDialog(self, c['title'], concept_html(c), wiki=c['wiki']).exec_()

        def symbol_context_menu(self, node, screen_pos):
            entry = lookup(node)
            menu = QMenu(self)
            label = entry['name'] if entry else (node.text or node.latex)
            if entry:
                a = menu.addAction('Wikipedia: %s' % entry['name'])
                a.triggered.connect(lambda: webbrowser.open(entry['wiki']))
            else:
                term = node.text or node.latex.lstrip('\\')
                a = menu.addAction('Search Wikipedia for "%s"' % term)
                a.triggered.connect(lambda: webbrowser.open(
                    'https://en.wikipedia.org/w/index.php?search=' + term))
            a = menu.addAction('Explain "%s" offline' % label)
            a.triggered.connect(lambda: self.explain_symbol(node))
            menu.addSeparator()
            a = menu.addAction('Copy LaTeX (%s)' % (node.latex or node.text))
            a.triggered.connect(lambda: QApplication.clipboard().setText(
                node.latex or node.text))
            if entry:
                related = [e for e in EQUATIONS
                           if entry['latex'].lstrip('\\') in e['must'] + e['nice']]
                if related:
                    sub = menu.addMenu('Equations using this symbol')
                    for eq in related[:12]:
                        act = sub.addAction(eq['name'])
                        act.triggered.connect(
                            lambda _c=False, t=eq['latex']: self.load(t))
            menu.addSeparator()
            a = menu.addAction('About this whole equation')
            a.triggered.connect(lambda: self.equation_context_menu(screen_pos))
            menu.exec_(screen_pos)

        def equation_context_menu(self, global_pos):
            menu = QMenu(self)
            hits = classify(self.tree, self.current_tex) if self.tree else []
            if hits:
                for eq, score, _n in hits:
                    a = menu.addAction('Wikipedia: %s' % eq['name'])
                    a.triggered.connect(
                        lambda _c=False, s=eq['slug']: webbrowser.open(WIKI + s))
                menu.addSeparator()
            a = menu.addAction('Explain this equation')
            a.triggered.connect(self.explain_equation)
            a = menu.addAction('Typeset with pdflatex')
            a.triggered.connect(self.typeset_current)
            a = menu.addAction('Copy LaTeX')
            a.triggered.connect(
                lambda: QApplication.clipboard().setText(self.current_tex))
            menu.exec_(global_pos)

        def explain_equation(self):
            if self.tree is None:
                return
            hits = classify(self.tree, self.current_tex)
            body = CSS + '<h2>%s</h2>' % esc(
                hits[0][0]['name'] if hits else 'Unidentified equation')
            body += '<p class="uni">%s</p>' % esc(
                latex_to_unicode(self.current_tex))
            body += ''.join('<p>%s</p>' % esc(p) for p in
                            describe_equation(self.tree,
                                              self.current_tex).split('\n\n'))
            InfoDialog(self, 'Equation', body,
                       wiki=(WIKI + hits[0][0]['slug']) if hits else None,
                       tex=self.current_tex).exec_()

        def typeset_current(self):
            png = render_latex_png(self.current_tex)
            if not png:
                QMessageBox.warning(
                    self, 'Typesetting failed',
                    'This needs pdflatex plus a PDF rasteriser (pdftoppm, '
                    'pdftocairo, or ImageMagick with Ghostscript) on PATH.')
                return
            dlg = QDialog(self)
            dlg.setWindowTitle('Typeset by pdflatex')
            lay = QVBoxLayout(dlg)
            lbl = QLabel()
            pix = QPixmap(png)
            if pix.width() > 900:
                pix = pix.scaledToWidth(900, Qt.SmoothTransformation)
            lbl.setPixmap(pix)
            area = QScrollArea()
            area.setWidget(lbl)
            lay.addWidget(area)
            b = QPushButton('Close')
            b.clicked.connect(dlg.accept)
            lay.addWidget(b)
            dlg.resize(min(940, pix.width() + 60), min(400, pix.height() + 90))
            dlg.exec_()

        def export_png(self):
            path, _ = QFileDialog.getSaveFileName(
                self, 'Export equation', 'equation.png', 'PNG (*.png)')
            if not path:
                return
            from PyQt5.QtGui import QImage
            rect = self.scene.sceneRect()
            img = QImage(int(rect.width()), int(rect.height()),
                         QImage.Format_ARGB32)
            img.fill(QColor(252, 251, 248))
            painter = QPainter(img)
            painter.setRenderHint(QPainter.Antialiasing)
            self.scene.render(painter)
            painter.end()
            img.save(path)
            self.status('Wrote ' + path)

        # ---------------------------------------------------------- browsers
        def browse_symbols(self):
            entries = [('%s  %s   [%s]' % (e['unicode'], e['name'],
                                           e['category']), e)
                       for e in sorted(SYMBOLS.values(),
                                       key=lambda e: (e['category'], e['name']))]
            BrowserDialog(self, 'Symbols', entries,
                          lambda e: symbol_html(e), lambda e: e['wiki']).exec_()

        def browse_concepts(self):
            entries = [('%s   [%s]' % (c['title'], c['category']), c)
                       for c in sorted(CONCEPTS.values(),
                                       key=lambda c: (c['category'], c['title']))]
            BrowserDialog(self, 'Concepts', entries, concept_html,
                          lambda c: c['wiki']).exec_()

        def browse_equations(self):
            entries = [('%s   [%s]' % (e['name'], e['field']), e)
                       for e in sorted(EQUATIONS,
                                       key=lambda e: (e['field'], e['name']))]
            BrowserDialog(self, 'Equations', entries, equation_html,
                          lambda e: WIKI + e['slug'],
                          get_tex=lambda e: e['latex']).exec_()

        # ---------------------------------------------------------- tools
        def python_to_latex(self):
            dlg = QDialog(self)
            dlg.setWindowTitle('Python -> LaTeX (rosettamath.py2tex)')
            dlg.resize(760, 560)
            lay = QVBoxLayout(dlg)
            lay.addWidget(QLabel('Python source:'))
            src = QPlainTextEdit('def energy(omega):\n'
                                 '    return scipy.constants.hbar * omega\n')
            src.setFont(QFont(pick_family(MONO_STACK), 10))
            lay.addWidget(src)
            lay.addWidget(QLabel('Generated pseudocode:'))
            out = QPlainTextEdit()
            out.setReadOnly(True)
            out.setFont(QFont(pick_family(MONO_STACK), 10))
            lay.addWidget(out)
            row = QHBoxLayout()
            b = QPushButton('Translate')
            b.clicked.connect(
                lambda: out.setPlainText(from_python(src.toPlainText())))
            row.addWidget(b)
            row.addStretch(1)
            c = QPushButton('Close')
            c.clicked.connect(dlg.accept)
            row.addWidget(c)
            lay.addLayout(row)
            dlg.exec_()

        def run_selftest(self):
            try:
                rosettamath.selftest(rosettamath.latex2py, 'stage 0')
                stage1, src = rosettamath.bootstrap()
                rosettamath.selftest(stage1['latex2py'], 'stage 1')
                QMessageBox.information(
                    self, 'rosettamath',
                    'Self test passed and the bootstrap reached a fixed '
                    'point.\n%d lines of Python were generated from the LaTeX '
                    'source.' % len(src.splitlines()))
            except Exception as exc:
                QMessageBox.critical(self, 'rosettamath',
                                     '%s: %s' % (type(exc).__name__, exc))

        def about(self):
            InfoDialog(self, 'About', CSS + """
<h2>RosettaUI</h2>
<p class="sub">An interactive front end for RosettaMath</p>
<p>Every glyph in the equation above is a live object. Hover it for its name
and conventional meaning, left-click for a full offline description, and
right-click to open the relevant Wikipedia article.</p>
<p>The equation as a whole is matched against a library of %d well known
equations, so the viewer can tell you what it resembles. The menus browse %d
symbols and %d longer articles on notation and convention.</p>
<p>The Python tab shows what rosettamath.py makes of the same LaTeX, which is
the point of the exercise: the equation you read and the code you run are the
same artefact.</p>
""" % (len(EQUATIONS), len(SYMBOLS), len(CONCEPTS))).exec_()


# ---------------------------------------------------------------- entry points

def selftest():
    """Headless checks: parser, unicode, classifier, knowledge-base sanity."""
    ok = True

    def check(label, cond):
        nonlocal ok
        print('  %-58s %s' % (label, 'ok' if cond else 'FAIL'))
        ok = ok and bool(cond)

    print('parser')
    t = parse_latex(r'E = m c^2')
    check('E = mc^2 has 4 top-level atoms', len(t.children) == 4)
    check('the c carries a superscript', t.children[3].kind == 'script')
    t = parse_latex(r'\frac{a}{b}')
    check('fraction parses with numerator and denominator',
          t.children[0].kind == 'frac' and t.children[0].num is not None)
    t = parse_latex(r'\sqrt{1 - v^2}')
    check('square root parses', t.children[0].kind == 'sqrt')
    t = parse_latex(r'x_i^2')
    check('sub and superscript combine on one base',
          t.children[0].sub is not None or t.children[0].base.sub is not None)
    check('unbalanced input does not raise',
          parse_latex(r'\frac{a}{') is not None)
    check('empty input does not raise', parse_latex('') is not None)

    print('unicode')
    check('greek resolves', latex_to_unicode(r'\alpha + \beta') == '\u03b1+\u03b2')
    check('superscript digit lifts', latex_to_unicode('x^2') == 'x\u00b2')
    check('hbar resolves', '\u210f' in latex_to_unicode(r'\hbar \omega'))
    check('fraction degrades to a slash',
          latex_to_unicode(r'\frac{a}{b}') == '(a)/(b)')

    print('classifier')
    cases = [
        (r'E = m c^2', 'Mass-energy equivalence'),
        (r'i \hbar \frac{\partial \Psi}{\partial t} = \hat{H} \Psi',
         'Schrodinger equation (time-dependent)'),
        (r'-\frac{\hbar^2}{2m} \nabla^2 \psi + V \psi = E \psi',
         'Schrodinger equation (time-independent)'),
        (r'\frac{\partial^2 u}{\partial t^2} = c^2 \nabla^2 u', 'Wave equation'),
        (r'\nabla \cdot B = 0', "Gauss's law for magnetism"),
        (r'\frac{\partial \rho}{\partial t} + \nabla \cdot J = 0',
         'Continuity equation'),
        (r'\gamma = \frac{1}{\sqrt{1 - \frac{v^2}{c^2}}}', 'Lorentz factor'),
        (r'S = \frac{k_B c^3 A}{4 G \hbar}', 'Bekenstein-Hawking entropy'),
        (r'\lambda_D = \sqrt{\frac{\epsilon_0 k_B T}{n e^2}}', 'Debye length'),
        (r'x = \frac{-b \pm \sqrt{b^2 - 4ac}}{2a}', 'Quadratic formula'),
        (r'\left( \Box + \frac{m^2 c^2}{\hbar^2} \right) \phi = 0',
         'Klein-Gordon equation'),
        (r'( i \gamma^\mu \partial_\mu - m ) \psi = 0', 'Dirac equation'),
    ]
    for tex, want in cases:
        hits = classify(parse_latex(tex), tex)
        got = hits[0][0]['name'] if hits else '(none)'
        check('%-46s -> %s' % (tex[:46], want), got == want)
    check('nonsense matches nothing', not classify(parse_latex('q = w + 7'), ''))
    check('bare Laplacian falls back to a family',
          'partial differential' in family_of(parse_latex(r'\nabla^2 u = '
                                                          r'\partial u')))

    print('knowledge base')
    check('%d symbols' % len(SYMBOLS), len(SYMBOLS) > 100)
    check('%d equations' % len(EQUATIONS), len(EQUATIONS) > 30)
    check('%d concepts' % len(CONCEPTS), len(CONCEPTS) > 10)
    check('every symbol has a wiki url',
          all(e['wiki'].startswith('http') for e in SYMBOLS.values()))
    check('every symbol has a blurb',
          all(len(e['blurb']) > 20 for e in SYMBOLS.values()))
    check('every equation slug is set',
          all(e['slug'] and e['blurb'] for e in EQUATIONS))
    check('every equation in the library parses',
          all(parse_latex(e['latex']) is not None for e in EQUATIONS))
    check('every equation identifies as itself or a sibling',
          all(classify(parse_latex(e['latex']), e['latex'])
              for e in EQUATIONS))
    check('every concept cites real symbols',
          all(s in SYMBOLS for c in CONCEPTS.values() for s in c['symbols']))

    print('rosettamath bridge')
    py = to_python(r'$E(m) = m \cdot c^2$')
    check('eq2py still produces a def', py.startswith('def E(m)'))
    scope = {'c': 299792458}
    fn = rosettamath.latex2py(r'$E(m) = m \cdot c^2$', scope)
    check('and the result executes', fn(1) == 299792458 ** 2)
    check('py2tex round trip returns pseudocode',
          '\\Function' in from_python('def f(x):\n    return x + 1\n'))
    good, _ = python_health(to_python(r'$K(m, v) = \frac{1}{2} \cdot m \cdot v^2$'))
    check('a function-form equation compiles', good)
    bad, note = python_health(to_python(r'$S = \frac{k_B c^3 A}{4 G \hbar}$'))
    check('a bare-symbol equation is flagged, with a reason',
          (not bad) and 'function form' in note)

    # environment-dependent, so reported but never fatal
    print('typesetting (optional)')
    has_tex, raster = have_tools()
    print('  %-58s %s' % ('pdflatex', 'found' if has_tex else 'missing'))
    print('  %-58s %s' % ('pdf rasteriser',
                          os.path.basename(raster) if raster else 'missing'))
    if has_tex and raster:
        png = render_latex_png(r'E = mc^2')
        print('  %-58s %s' % ('typeset a fragment', png or 'FAILED'))

    print('\n%s' % ('all checks passed' if ok else 'FAILURES ABOVE'))
    return 0 if ok else 1


def render_test(path='/tmp/rosettaui.png',
                tex=r'-\frac{\hbar^2}{2m} \nabla^2 \psi + V \psi = E \psi'):
    """Lay the equation out offscreen and save it, to check the layout engine."""
    os.environ.setdefault('QT_QPA_PLATFORM', 'offscreen')
    from PyQt5.QtGui import QImage
    app = QApplication(sys.argv[:1])
    scene = QGraphicsScene()
    scene.setBackgroundBrush(QColor(252, 251, 248))
    tree = parse_latex(tex)
    MathLayout(scene, None).render(tree)
    rect = scene.itemsBoundingRect().adjusted(-20, -20, 20, 20)
    scene.setSceneRect(rect)
    img = QImage(int(rect.width()), int(rect.height()), QImage.Format_ARGB32)
    img.fill(QColor(252, 251, 248))
    p = QPainter(img)
    p.setRenderHint(QPainter.Antialiasing)
    p.setRenderHint(QPainter.TextAntialiasing)
    scene.render(p)
    p.end()
    img.save(path)
    n = len(scene.items())
    print('rendered %d items (%dx%d) -> %s'
          % (n, img.width(), img.height(), path))
    return 0 if n else 1


def main(argv):
    if '--selftest' in argv:
        return selftest()
    tex = DEFAULT_EQUATION
    if '--tex' in argv:
        tex = argv[argv.index('--tex') + 1]
    if '--render-test' in argv:
        return render_test(tex=tex)
    if not QT_OK:
        print('PyQt5 is required for the GUI: %s' % QT_ERROR, file=sys.stderr)
        print('Try: pip install PyQt5   (or apt install python3-pyqt5)',
              file=sys.stderr)
        return 1
    app = QApplication(argv)
    win = RosettaWindow(tex)
    win.show()
    return app.exec_()


if __name__ == '__main__':
    sys.exit(main(sys.argv))
