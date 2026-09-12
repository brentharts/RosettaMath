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

    dict(name=, field=, latex=, slug=, must=[], nice=[], blurb=)

EQUATION_FAMILIES -- the fallback when no single equation matches: a feature
set paired with a description of the genre it belongs to.

CONSTANTS maps symbol names to scipy.constants attributes, which is what stops
c and hbar being inferred as function arguments during translation.

    python3 rosettaphys.py             a census of the knowledge base
    python3 rosettaphys.py --selftest  check every entry is well formed
"""

WIKI = 'https://en.wikipedia.org/wiki/'


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
         must=['phi', 'm', 'hbar'],
         nice=['c', 'Box', 'S:nabla2', 'partial', 'S:sup2', 'S:frac'],
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
    dict(name="d'Alembert operator", field='Relativity',
         latex=r'\Box = \frac{1}{c^2} \frac{\partial^2}{\partial t^2} - \nabla^2',
         slug="D'Alembert_operator",
         must=['Box', 'S:nabla2', 'partial'], nice=['c', 'S:frac', 'S:sup2', 't'],
         blurb='The definition of the box operator: a second time derivative '
               'against a spatial Laplacian, with the relative minus sign that '
               'is the whole difference between Minkowski spacetime and '
               'Euclidean space. Written out this way it is clear why the '
               'operator is Lorentz invariant and the Laplacian alone is not.'),
    dict(name='Wave equation (box form)', field='Waves',
         latex=r'\Box \psi = 0', slug='Wave_equation',
         must=['Box'], nice=['psi', 'phi', 'A', 'u', 'F'],
         blurb='The wave equation written with the d\'Alembertian. Compressing '
               'the time and space derivatives into one symbol makes the '
               'relativistic content visible at a glance: the equation has the '
               'same form in every inertial frame, and its solutions propagate '
               'at exactly the speed c buried inside the operator.'),
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


def selftest():
    """Validate every entry.  Returns the number of problems found."""
    problems = []

    def fail(msg):
        problems.append(msg)

    _check_symbols(fail)
    _check_tables(fail)
    _check_concepts(fail)
    _check_equations(fail)

    for msg in problems:
        print('FAIL  ' + msg)
    if problems:
        print('\n%d problem(s) in the knowledge base.' % len(problems))
    else:
        print('rosettaphys: %d symbols, %d concepts, %d equations -- all well formed.'
              % (len(SYMBOLS), len(CONCEPTS), len(EQUATIONS)))
    return len(problems)


def _report():
    print(__doc__.strip().split('\n')[0])
    print()
    for key, value in census().items():
        print('  %-20s %d' % (key, value))
    print()
    print('  symbol categories:  ' + ', '.join(categories()))
    print('  concept categories: ' + ', '.join(concept_categories()))
    print('  equation fields:    ' + ', '.join(fields()))


if __name__ == '__main__':
    import sys
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    _report()
