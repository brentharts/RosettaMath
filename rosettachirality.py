#!/usr/bin/env python3
r"""rosettachirality.py -- the bridge from RosettaPhys to chirality-standard-model.

Thirteen entries in the 'Lie algebras and chirality' group of rosettaphys.py
are drawn from Emad Mostaque's chirality-standard-model repository and from the
lisi/ bridge in brentharts' fork of it.  This module makes the claim that they
describe those repositories testable, in three layers.

* The library's own algebra reads and evaluates each entry that is scalar
  algebra, against the arithmetic the entry states (dimension counts, orbit
  sizes, the Freudenthal-Tits table, the family anomaly).
* Numbers the library cannot get from algebra alone are computed independently
  of both repositories, in exact rational arithmetic: the content of one
  Standard Model family from the weights of the 10 and the 5-bar of SU(5) under
  the paper's cocharacter, from which the charge lattice, the hypercharge
  sums, the five-thirds normalisation and the net chiral class are read off.
* A second route to the family, when the fork's lisi/sm_charges.py is there:
  the 16 weights of the 27 read off the E8 roots by inner products, compared
  with the SU(5) route for the five summands, the five thirds and the sums.
* The repository's own data and code are put through the entries: its E8 root
  system (240 = 72 + 6 + 6*27, rank by linear algebra), its E6 certificate
  (orbit sizes, the Weyl order, the triple count, rank plus root count for each
  pair type, and the certificate's recorded digest), and the exact nullspace
  computation of the triality dimensions in lisi/check_magic_square.py.

It does not touch the paper's proofs, the Lean files or the physics.  The
repository's claim is a uniqueness theorem over a stated domain; what is
checked here is that the arithmetic the library quotes from it is the
arithmetic its code produces.

    python3 rosettachirality.py             what was checked, and what was not
    python3 rosettachirality.py --selftest  the bridge, end to end

The repository is found in $CHIRALITY_DIR or in a chirality-standard-model
directory beside this one; it needs numpy and sympy.  Without it, the library
side and the independent computations still run and the missing side is
reported.
"""

import hashlib
import importlib.util
import itertools
import json
import math
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rosettaphys as P

REFERENCES = ('chirality2026', 'lisi2026')


def locate():
    for path in (os.environ.get('CHIRALITY_DIR'),
                 os.path.join(HERE, '..', 'chirality-standard-model'),
                 os.path.join(HERE, 'chirality-standard-model'),
                 os.path.expanduser('~/chirality-standard-model')):
        if path and os.path.exists(os.path.join(path, 'lisi', 'e8.py')):
            return os.path.abspath(path)
    return None


_CACHE = {}


def _import(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def load():
    """(e8 module, magic-square module, certificate dict, root path) or None."""
    if 'ns' in _CACHE:
        return _CACHE['ns']
    root = locate()
    ns = None
    if root is not None:
        sys.dont_write_bytecode = True
        lisi = os.path.join(root, 'lisi')
        try:
            if lisi not in sys.path:
                sys.path.insert(0, lisi)
            e8 = _import('chirality_lisi_e8', os.path.join(lisi, 'e8.py'))
            magic = _import('chirality_lisi_magic',
                            os.path.join(lisi, 'check_magic_square.py'))
            with open(os.path.join(root, 'verification', 'certificates',
                                   'e6_extrema_certificate.json')) as handle:
                cert = json.load(handle)
            ns = (e8, magic, cert, root)
        except Exception as error:
            _CACHE['error'] = '%s: %s' % (type(error).__name__, error)
    _CACHE['ns'] = ns
    return ns


def available():
    return load() is not None


def load_sm():
    """The fork's lisi/sm_charges.py, or None.  It reads one Standard Model
    family off the E8 roots; the file was added to the fork after the rest of
    lisi/, so an older checkout may not have it."""
    if 'sm' in _CACHE:
        return _CACHE['sm']
    sm = None
    ns = load()
    if ns is not None:
        path = os.path.join(ns[3], 'lisi', 'sm_charges.py')
        if os.path.exists(path):
            try:
                sm = _import('chirality_lisi_sm', path)
            except Exception as error:
                _CACHE['sm_error'] = '%s: %s' % (type(error).__name__, error)
    _CACHE['sm'] = sm
    return sm


def _entry(name):
    entry = P.GRAPH.find(name, 'equation')
    if entry is None:
        raise KeyError('no equation called %r' % name)
    return entry


def predicts(name, known):
    return P.evaluate(P.read_relation(_entry(name)['latex']).right, known)


class Check:
    def __init__(self, equation, what, library, reference, tolerance):
        self.equation, self.what = equation, what
        self.library, self.reference, self.tolerance = library, reference, tolerance

    @property
    def error(self):
        if self.reference == 0:
            return abs(self.library)
        return abs(self.library - self.reference) / abs(self.reference)

    @property
    def ok(self):
        return self.error <= self.tolerance


# -------------------------------------------- Weyl orders and root counts
#
# Standard closed forms, written out here so the orbit sizes and pair
# dimensions are computed by something other than the repository.

def weyl_order(kind, n):
    if kind == 'A':
        return math.factorial(n + 1)
    if kind == 'D':
        return 2 ** (n - 1) * math.factorial(n)
    raise ValueError(kind)


def roots_and_rank(kind, n):
    if kind == 'A':
        return n * (n + 1), n
    if kind == 'D':
        return 2 * n * (n - 1), n
    raise ValueError(kind)


def parse_type(text):
    """'A2+A1+A1' -> [('A', 2), ('A', 1), ('A', 1)]."""
    return [(part[0], int(part[1:])) for part in text.split('+')]


def type_dimension(text):
    """Roots plus rank, summed over the simple components of a root system."""
    roots = rank = 0
    for kind, n in parse_type(text):
        r, k = roots_and_rank(kind, n)
        roots, rank = roots + r, rank + k
    return roots, rank


# The standard dimension of a simple algebra, for an independent check that
# rank plus root count is what the dimension is.
def simple_dimension(kind, n):
    return {'A': n * (n + 2), 'D': n * (2 * n - 1)}[kind]


# ------------------------------------------- one Standard Model family
#
# The paper restricts the 27 along E6 > Spin(10) > SU(5) > S(U(3) x U(2)) and
# reads the family off the 10 and the 5-bar.  The circle in the centre of the
# faithful Standard Model group is eta(z) = diag(z^-2 I_3, z^3 I_2), oriented so
# the (3,2) in the 10 has integer charge one.  Everything below is computed from
# the weights of the 5, with colour triality t and weak parity s counted from
# the indices.

_CHARGE = {1: -2, 2: -2, 3: -2, 4: 3, 5: 3}


def _states(sign, indices):
    """One state: (colour triality, weak parity, integer charge)."""
    colour = sum(1 for i in indices if i <= 3)
    weak = sum(1 for i in indices if i >= 4)
    q = sum(_CHARGE[i] for i in indices)
    return ((sign * colour) % 3, (sign * weak) % 2, sign * q)


def five():
    return [_states(1, (i,)) for i in range(1, 6)]


def five_bar():
    return [_states(-1, (i,)) for i in range(1, 6)]


def ten():
    return [_states(1, pair) for pair in itertools.combinations(range(1, 6), 2)]


def multiplets(states):
    """Group states into (t, s, q) -> count, and name the shape of each."""
    counts = {}
    for key in states:
        counts[key] = counts.get(key, 0) + 1
    out = {}
    for (t, s, q), n in counts.items():
        colour = 3 if t else 1
        weak = 2 if s else 1
        out[(t, s, q)] = (colour, weak, n)
    return out


def family():
    """The 10 plus the 5-bar: the five summands of one family."""
    return multiplets(ten() + five_bar())


def conjugate(key):
    t, s, q = key
    return ((-t) % 3, s, -q)


def hypercharge(key):
    return Fraction(key[2], 6)


def family_sums():
    """Sum Y, Y^3, Y^2, T3^2, and the mixed SU(3)^2 Y and SU(2)^2 Y sums."""
    sy = sy3 = sy2 = st3 = Fraction(0)
    su3y = su2y = Fraction(0)
    for key, (colour, weak, n) in family().items():
        y = hypercharge(key)
        sy += n * y
        sy3 += n * y ** 3
        sy2 += n * y ** 2
        if weak == 2:
            st3 += colour * Fraction(1, 2)       # two states, T3 = +-1/2
            su2y += colour * y * Fraction(1, 2)  # index 1/2 per doublet
        if colour == 3:
            su3y += weak * y * Fraction(1, 2)    # index 1/2 per triplet
    return {'Y': sy, 'Y3': sy3, 'Y2': sy2, 'T3sq': st3,
            'SU3Y': su3y, 'SU2Y': su2y}


def chiral_class(states):
    """Net chirality: for each non-self-dual pair, multiplicity minus its dual's.

    Keyed by the canonical member of the pair, the lexicographically smaller
    key, so the class is a function of the multiset and nothing else.
    """
    counts = {}
    for key in states:
        counts[key] = counts.get(key, 0) + 1
    out = {}
    for key in counts:
        dual = conjugate(key)
        if dual == key:
            continue
        canon = min(key, dual)
        net = counts.get(canon, 0) - counts.get(conjugate(canon), 0)
        if net:
            out[canon] = net
    return out


def family_module(copies):
    """V restricted to the Standard Model group: copies of 27 = 16 + 10 + 1.

    16 = 10 + 5-bar + 1 under SU(5); the 10 of Spin(10) is a 5 and a 5-bar.
    """
    one = [(0, 0, 0)]
    twentyseven = (ten() + five_bar() + one          # the 16
                   + five() + five_bar()             # the 10
                   + one)                            # the singlet
    assert len(twentyseven) == 27
    return twentyseven * copies


# ------------------------------------------------- SU(3) cubic anomaly

def _gell_mann():
    import numpy as np
    s3 = math.sqrt(3.0)
    mats = [
        [[0, 1, 0], [1, 0, 0], [0, 0, 0]],
        [[0, -1j, 0], [1j, 0, 0], [0, 0, 0]],
        [[1, 0, 0], [0, -1, 0], [0, 0, 0]],
        [[0, 0, 1], [0, 0, 0], [1, 0, 0]],
        [[0, 0, -1j], [0, 0, 0], [1j, 0, 0]],
        [[0, 0, 0], [0, 0, 1], [0, 1, 0]],
        [[0, 0, 0], [0, 0, -1j], [0, 1j, 0]],
        [[1 / s3, 0, 0], [0, 1 / s3, 0], [0, 0, -2 / s3]],
    ]
    return [np.array(m, dtype=complex) / 2 for m in mats]


def _anomaly_tensor(generators):
    import numpy as np
    n = len(generators)
    out = np.zeros((n, n, n))
    for a in range(n):
        for b in range(n):
            for c in range(n):
                t = generators[a] @ (generators[b] @ generators[c]
                                     + generators[c] @ generators[b])
                out[a, b, c] = 0.5 * np.trace(t).real
    return out


def anomalies():
    """Cubic anomaly tensors of 3, 3-bar, the doublet, and 27 x 3 through the 3."""
    import numpy as np
    gens = _gell_mann()
    a3 = _anomaly_tensor(gens)
    a3bar = _anomaly_tensor([-g.conj() for g in gens])
    pauli = [np.array(m, dtype=complex) / 2 for m in
             ([[0, 1], [1, 0]], [[0, -1j], [1j, 0]], [[1, 0], [0, -1]])]
    a2 = _anomaly_tensor(pauli)
    v = _anomaly_tensor([np.kron(np.eye(27), g) for g in gens])
    return a3, a3bar, a2, v


# ------------------------------------------------- library-only checks

# The Freudenthal-Tits table for R, C, H, O, which is standard.
MAGIC = [[3, 8, 21, 52], [8, 16, 35, 78], [21, 35, 66, 133], [52, 78, 133, 248]]
TRIALITY = [0, 2, 9, 28]
DIVISION = [1, 2, 4, 8]


def _check_closed_forms():
    out = []
    for name, roots, rank, dim in (('E8', 240, 8, 248), ('E7', 126, 7, 133),
                                   ('E6', 72, 6, 78), ('F4', 48, 4, 52),
                                   ('G2', 12, 2, 14), ('SU(3)', 6, 2, 8)):
        out.append(Check('Lie algebra dimension', 'D = R + r for %s' % name,
                         predicts('Lie algebra dimension',
                                  {'R': float(roots), 'r': float(rank)}),
                         float(dim), 1e-12))
    v = predicts('Product representation dimension', {'D_a': 27.0, 'D_b': 3.0})
    out.append(Check('Product representation dimension', '27 times 3 is 81',
                     v, 81.0, 1e-12))
    out.append(Check('Adjoint branching',
                     '248 = 86 + 2 times 81 (E6 + SU(3), and the 27 over the 3)',
                     predicts('Adjoint branching', {'D_h': 86.0, 'D_V': v}),
                     248.0, 1e-12))
    for label, kind, n, expected in (
            ('D5', 'D', 5, 27), ('A5+A1', None, None, 36),
            ('A2 cubed', None, None, 40)):
        if kind == 'D':
            stabiliser = weyl_order('D', 5)
        elif label == 'A5+A1':
            stabiliser = weyl_order('A', 5) * weyl_order('A', 1)
        else:
            # three A2's can be permuted among themselves: the paper's 6^3 * 6
            stabiliser = weyl_order('A', 2) ** 3 * math.factorial(3)
        out.append(Check('Orbit size',
                         'W(E6) of order 51840 over the stabiliser of %s' % label,
                         predicts('Orbit size', {'w': 51840.0,
                                                 's': float(stabiliser)}),
                         float(expected), 1e-12))
    out.append(Check('Orbit size', '51840 is the product of the degrees of E6',
                     float(math.prod((2, 5, 6, 8, 9, 12))), 51840.0, 0.0))
    out.append(Check('Triple space', '27 times 36 times 40 is 38880',
                     predicts('Triple space', {'n_1': 27.0, 'n_2': 36.0,
                                               'n_3': 40.0}), 38880.0, 1e-12))
    for i, a in enumerate(DIVISION):
        for j, b in enumerate(DIVISION):
            out.append(Check('Magic square dimension',
                             'L(%s, %s) from the triality dimensions'
                             % ('RCHO'[i], 'RCHO'[j]),
                             predicts('Magic square dimension',
                                      {'tau_A': float(TRIALITY[i]),
                                       'tau_B': float(TRIALITY[j]),
                                       'a': float(a), 'b': float(b)}),
                             float(MAGIC[i][j]), 1e-12))
    out.append(Check('Magic square dimension',
                     'L(O, O) is the D4 times D4 count of E8, 28 + 28 + 3*64',
                     float(28 + 28 + 3 * 64), 248.0, 0.0))
    return out


def _check_family():
    """Computed from the weights of the 10 and the 5-bar, not from a table."""
    out = []
    fam = family()
    expected = {(1, 1, 1): (3, 2, Fraction(1, 6)),      # Q
                (2, 0, -4): (3, 1, Fraction(-2, 3)),    # u^c
                (0, 0, 6): (1, 1, Fraction(1)),         # e^c
                (2, 0, 2): (3, 1, Fraction(1, 3)),      # d^c
                (0, 1, -3): (1, 2, Fraction(-1, 2))}    # L
    out.append(Check('Hypercharge', 'five summands, with the paper\'s shapes',
                     float(len(fam)), 5.0, 0.0))
    for key, (colour, weak, y) in expected.items():
        shape = fam.get(key)
        ok = shape is not None and shape[0] == colour and shape[1] == weak \
            and shape[2] == colour * weak
        out.append(Check('Hypercharge',
                         'summand with (t, s, q) = %s has dimensions (%d, %d)'
                         % (key, colour, weak), float(ok), 1.0, 0.0))
        out.append(Check('Hypercharge', 'Y = q/6 = %s for q = %d' % (y, key[2]),
                         predicts('Hypercharge', {'q': float(key[2])}),
                         float(y), 1e-12))
    for key in fam:
        t, s, q = key
        out.append(Check('Charge lattice',
                         'q + 2t + 3s = %d is a multiple of six for %s'
                         % (q + 2 * t + 3 * s, key),
                         float((q + 2 * t + 3 * s) % 6), 0.0, 0.0))
    # and the lattice is not trivially satisfied: a bad charge fails
    out.append(Check('Charge lattice', 'q = 2 on a colour singlet doublet fails',
                     float((2 + 0 + 3) % 6 != 0), 1.0, 0.0))
    sums = family_sums()
    out.append(Check('Anomaly-free hypercharge', 'sum of Y over the family',
                     float(sums['Y']), 0.0, 0.0))
    out.append(Check('Anomaly-free hypercharge', 'sum of Y^3 over the family',
                     float(sums['Y3']), 0.0, 0.0))
    out.append(Check('Anomaly-free hypercharge', 'SU(3)^2 Y sum',
                     float(sums['SU3Y']), 0.0, 0.0))
    out.append(Check('Anomaly-free hypercharge', 'SU(2)^2 Y sum',
                     float(sums['SU2Y']), 0.0, 0.0))
    k = sums['Y2'] / sums['T3sq']
    out.append(Check('Hypercharge normalisation',
                     'sum Y^2 / sum T3^2 over one family is 5/3',
                     float(k), 5.0 / 3.0, 1e-12))
    # the number the CICY entry uses for the same conversion
    five_thirds = predicts('Electromagnetic coupling at the Z',
                           {'alpha_2': 1.0, 'alpha_1': 1.0}) - 1.0
    out.append(Check('Hypercharge normalisation',
                     'the five thirds in the electromagnetic coupling',
                     float(k), five_thirds, 1e-12))
    # the 16 adds the singlet, which has Y = 0 and changes neither sum
    sixteen = ten() + five_bar() + [(0, 0, 0)]
    y2 = sum(Fraction(q, 6) ** 2 for _t, _s, q in sixteen)
    out.append(Check('Hypercharge normalisation',
                     'the singlet in the 16 changes neither sum',
                     float(y2 / sums['T3sq']), 5.0 / 3.0, 1e-12))
    return out


def _check_chirality():
    out = []
    one = family_module(1)
    out.append(Check('Net chiral class', 'a 27 has 27 states', float(len(one)),
                     27.0, 0.0))
    chi_f = chiral_class(ten() + five_bar())
    out.append(Check('Net chiral class',
                     'one family is five chiral summands, none self-dual',
                     float(len(chi_f)), 5.0, 0.0))
    for n in (1, 2, 3):
        chi_v = chiral_class(family_module(n))
        ratio = {key: Fraction(chi_v.get(key, 0), chi_f[key]) for key in chi_f}
        out.append(Check('Net chiral class',
                         '%d copies of the 27 have net chirality %d times one '
                         'family\'s, summand by summand' % (n, n),
                         float(set(ratio.values()) == {Fraction(n)}), 1.0, 0.0))
        out.append(Check('Net chiral class',
                         'and nothing else is chiral: %d summands in all, '
                         'vector-like pairs and singlets cancel' % n,
                         float(len(chi_v)), 5.0, 0.0))
        out.append(Check('Net chiral class', 'chi_V = N_gen chi_F for N_gen = %d' % n,
                         predicts('Net chiral class',
                                  {'N_gen': float(n), 'chi_F': 1.0}),
                         float(n), 1e-12))
    return out


def _check_anomaly():
    try:
        import numpy  # noqa: F401
    except ImportError:
        return []
    out = []
    a3, a3bar, a2, v = anomalies()
    scale = abs(a3).max()
    out.append(Check('Cubic anomaly coefficient',
                     'the 3 of SU(3) has a nonzero cubic anomaly',
                     float(scale > 0.05), 1.0, 0.0))
    out.append(Check('Cubic anomaly coefficient',
                     'the 3-bar has the opposite sign (odd under duality)',
                     float(abs(a3bar + a3).max()), 0.0, 1e-12))
    out.append(Check('Cubic anomaly coefficient',
                     'the doublet of SU(2) has none', float(abs(a2).max()),
                     0.0, 1e-12))
    out.append(Check('Anomaly of a product representation',
                     '27 x 3 through the 3: A_V against D_a A_b, largest entry',
                     float(abs(v).max()),
                     predicts('Anomaly of a product representation',
                              {'D_a': 27.0, 'A_b': float(scale)}), 1e-9))
    out.append(Check('Anomaly of a product representation',
                     'entry by entry, the tensor is 27 times the 3\'s',
                     float(abs(v - 27 * a3).max()), 0.0, 1e-9))
    return out


def checks_independent():
    """Everything that needs neither repository."""
    return _check_family() + _check_chirality() + _check_anomaly()


# ------------------------------------------------------ repository checks

def e8_branching(e8):
    """Root counts by SU(3) weight, and ranks, from the repository's roots."""
    import numpy as np
    roots = e8.e8_roots()
    alpha = (2, -2, 0, 0, 0, 0, 0, 0)
    beta = (0, 2, -2, 0, 0, 0, 0, 0)
    labels = {}
    for r in roots:
        labels.setdefault((e8.inner(r, alpha), e8.inner(r, beta)), []).append(r)
    zero = labels[(0, 0)]
    three = {(1, 0), (-1, 1), (0, -1)}
    threebar = {(0, 1), (1, -1), (-1, 0)}
    adjoint = {(2, -1), (-1, 2), (1, 1), (-2, 1), (1, -2), (-1, -1)}
    su3 = [r for k in adjoint for r in labels[k]]
    rank = lambda rs: int(np.linalg.matrix_rank(np.array(rs, dtype=float)))
    return {
        'roots': len(roots), 'rank_e8': rank(roots),
        'e6_roots': len(zero), 'rank_e6': rank(zero),
        'su3_roots': len(su3), 'rank_su3': rank(su3),
        'per_weight': sorted({len(labels[k]) for k in three | threebar}),
        'weights_of_3': len(three), 'labels': set(labels),
        'expected_labels': {(0, 0)} | three | threebar | adjoint,
    }


def _check_sm_charges():
    """The family computed from the E8 roots, against the one from SU(5).

    Two routes to the same five summands: the paper's, through the weights of
    the 10 and the 5-bar of SU(5), written out in this module; and the
    fork's, through the 16 weights of the 27 and inner products with roots.
    """
    sm = load_sm()
    if sm is None:
        return []
    model = sm.build()
    f16 = model.families['16']
    # the colour class '3' is the class of the quark doublet in both routes
    colour = {0: '1', 1: '3', 2: '3b'}
    mine = {}
    for (t, s, q), (_c, weak, n) in family().items():
        mine[(colour[t], weak, sp_rational(Fraction(q, 6)))] = n
    theirs = dict(sm.content(f16))
    singlet = ('1', 1, sp_rational(Fraction(0)))
    theirs.pop(singlet)       # the singlet nu^c is not in the 10 + 5-bar of SU(5)
    out = [Check('Hypercharge', 'the five summands from the E8 roots are the '
                                'five from SU(5), with the same multiplicities',
                 float(mine == theirs), 1.0, 0.0)]
    y2 = sum(r['Y'] ** 2 for r in f16)
    t32 = sum(r['T3'] ** 2 for r in f16)
    out.append(Check('Hypercharge normalisation',
                     'sum Y^2 / sum T3^2 over the 16 read off the E8 weights is 5/3',
                     float(y2 / t32), 5.0 / 3.0, 1e-12))
    out.append(Check('Anomaly-free hypercharge',
                     'sum Y^3 over the 16 read off the E8 weights',
                     float(sum(r['Y'] ** 3 for r in f16)), 0.0, 0.0))
    out.append(Check('Charge lattice',
                     'q = 6Y is an integer with q + 2t + 3s = 0 mod 6 on all '
                     'sixteen E8 weights',
                     float(all((6 * r['Y']).is_integer and
                               (int(6 * r['Y']) + 2 * {'1': 0, '3': 1, '3b': 2}[r['color']]
                                + 3 * (r['su2'] - 1)) % 6 == 0 for r in f16)),
                     1.0, 0.0))
    return out


def sp_rational(x):
    import sympy
    return sympy.Rational(x.numerator, x.denominator)


def checks():
    ns = load()
    if ns is None:
        return []
    e8, magic, cert, root = ns
    out = []
    b = e8_branching(e8)
    counts = cert['finite_object_counts']

    # E8 and its pieces, by root count and linear algebra
    for label, roots, rank in (('E8', b['roots'], b['rank_e8']),
                               ('E6', b['e6_roots'], b['rank_e6']),
                               ('SU(3)', b['su3_roots'], b['rank_su3'])):
        dims = {'E8': 248, 'E6': 78, 'SU(3)': 8}
        out.append(Check('Lie algebra dimension',
                         'roots and rank of %s from the E8 root system' % label,
                         predicts('Lie algebra dimension',
                                  {'R': float(roots), 'r': float(rank)}),
                         float(dims[label]), 1e-12))
    out.append(Check('Lie algebra dimension',
                     'the repository\'s E6 root count matches its certificate',
                     float(b['e6_roots']), float(counts['roots']), 0.0))
    d_h = (predicts('Lie algebra dimension', {'R': float(b['e6_roots']),
                                              'r': float(b['rank_e6'])})
           + predicts('Lie algebra dimension', {'R': float(b['su3_roots']),
                                                'r': float(b['rank_su3'])}))
    d_v = predicts('Product representation dimension',
                   {'D_a': float(b['per_weight'][0]),
                    'D_b': float(b['weights_of_3'])})
    out.append(Check('Adjoint branching',
                     'E8 from the pieces the root system actually has: '
                     '(78 + 8) + 2 x (27 x 3)',
                     predicts('Adjoint branching', {'D_h': d_h, 'D_V': d_v}),
                     predicts('Lie algebra dimension',
                              {'R': float(b['roots']),
                               'r': float(b['rank_e8'])}), 1e-12))
    out.append(Check('Adjoint branching',
                     'the 240 roots fall into exactly the labels of '
                     '(78,1) + (1,8) + (27,3) + (27-bar,3-bar)',
                     float(b['labels'] == b['expected_labels']), 1.0, 0.0))
    out.append(Check('Adjoint branching',
                     'every weight of the 3 carries exactly 27 roots',
                     float(b['per_weight'] == [27]), 1.0, 0.0))

    # orbit sizes, the Weyl order and the triple count, against the certificate
    expected = {'D5_orbit': ('D5', weyl_order('D', 5)),
                'A5_plus_A1_orbit': ('A5+A1', weyl_order('A', 5)
                                     * weyl_order('A', 1)),
                'A2_cubed_orbit': ('A2^3', weyl_order('A', 2) ** 3
                                   * math.factorial(3))}
    sizes = []
    for key, (label, stabiliser) in expected.items():
        size = predicts('Orbit size', {'w': float(counts['weyl_group_order']),
                                       's': float(stabiliser)})
        sizes.append(size)
        out.append(Check('Orbit size',
                         'orbit of %s: %d / %d against the certificate'
                         % (label, counts['weyl_group_order'], stabiliser),
                         size, float(counts[key]), 1e-12))
    out.append(Check('Orbit size', 'the certificate\'s Weyl order is 51840',
                     float(counts['weyl_group_order']), 51840.0, 0.0))
    out.append(Check('Triple space', 'product of the three orbit sizes against '
                                     'the certificate\'s triple space',
                     predicts('Triple space', {'n_1': sizes[0], 'n_2': sizes[1],
                                               'n_3': sizes[2]}),
                     float(counts['triple_space']), 1e-12))
    total = sum(counts['maximal_proper_types'].values())
    out.append(Check('Orbit size', 'the three orbits are all 103 maximal subsystems',
                     float(total), float(counts['maximal_proper_closed_subsystems']),
                     0.0))

    # rank plus root count for each pair type the certificate lists
    for row in cert['intrinsic_pair_selector']['pair_parent_types']:
        roots, rank = type_dimension(row['type'])
        out.append(Check('Lie algebra dimension',
                         'pair type %s: roots %d and rank %d from the type name'
                         % (row['type'], roots, rank),
                         predicts('Lie algebra dimension',
                                  {'R': float(roots), 'r': float(rank)}),
                         float(row['semisimple_dimension']), 1e-12))
        standard = sum(simple_dimension(k, n) for k, n in parse_type(row['type']))
        out.append(Check('Lie algebra dimension',
                         'pair type %s: the certificate\'s dimension is the '
                         'standard dimension of its simple factors' % row['type'],
                         float(row['semisimple_dimension']), float(standard), 0.0))
        out.append(Check('Lie algebra dimension',
                         'pair type %s: the certificate\'s own root count and '
                         'rank are the ones computed from the name' % row['type'],
                         float((row['root_count'], row['rank']) == (roots, rank)),
                         1.0, 0.0))

    # the certificate has not drifted from its recorded digest
    path = os.path.join(root, 'verification', 'certificates')
    with open(os.path.join(path, 'e6_extrema_certificate.json'), 'rb') as handle:
        digest = hashlib.sha256(handle.read()).hexdigest()
    with open(os.path.join(path, 'e6_extrema_certificate.sha256')) as handle:
        recorded = handle.read().split()[0]
    out.append(Check('Orbit size', 'the certificate matches its recorded SHA-256',
                     float(digest == recorded), 1.0, 0.0))

    # triality dimensions as exact nullspaces, then the magic square from them
    tri = [magic.tri_dim(n) for n in DIVISION]
    out.append(Check('Magic square dimension',
                     'the repository\'s exact nullspaces give tri = 0, 2, 9, 28',
                     float(tri == TRIALITY), 1.0, 0.0))
    for i, a in enumerate(DIVISION):
        for j, c in enumerate(DIVISION):
            out.append(Check('Magic square dimension',
                             'L(%s, %s) from the repository\'s triality dimensions'
                             % ('RCHO'[i], 'RCHO'[j]),
                             predicts('Magic square dimension',
                                      {'tau_A': float(tri[i]),
                                       'tau_B': float(tri[j]),
                                       'a': float(a), 'b': float(c)}),
                             float(MAGIC[i][j]), 1e-12))
    out.append(Check('Magic square dimension',
                     'L(O, O) is the dimension the E8 root system has',
                     predicts('Magic square dimension',
                              {'tau_A': float(tri[3]), 'tau_B': float(tri[3]),
                               'a': 8.0, 'b': 8.0}),
                     predicts('Lie algebra dimension',
                              {'R': float(b['roots']),
                               'r': float(b['rank_e8'])}), 1e-12))
    out.extend(_check_sm_charges())
    # the family count is the number of SU(3) weights on the family index
    out.append(Check('Net chiral class',
                     'the three: the weights of the 3 over which the 27 repeats',
                     float(b['weights_of_3']),
                     float(set(Fraction(chiral_class(family_module(
                         b['weights_of_3']))[key],
                         chiral_class(ten() + five_bar())[key])
                         for key in chiral_class(ten() + five_bar())).pop()),
                     0.0))
    return out


# ----------------------------------------------------------- reporting

def ours():
    out = []
    for key in REFERENCES:
        out.extend(P.cited(key))
    return out


def unchecked():
    """Entries the algebra declines to read, so they cannot be evaluated."""
    names = []
    for entry in ours():
        try:
            P.read_relation(entry['latex'])
        except Exception:
            names.append(entry['name'])
    return names


def not_compared():
    compared = {c.equation for c in
                _check_closed_forms() + checks_independent() + checks()}
    return sorted(e['name'] for e in ours() if e['name'] not in compared)


def _report():
    print('rosettachirality: the chirality-standard-model repository, as seen '
          'from RosettaPhys')
    for key in REFERENCES:
        print('  %s' % P.cite_text(key))
    print('  %d entries cite them' % len(ours()))
    root = locate()
    print('  chirality-standard-model found at %s'
          % (root or 'nowhere (set CHIRALITY_DIR)'))
    if root and not available():
        print('  but it did not import: %s' % _CACHE.get('error'))
    print()
    groups = (('the library against what it states', _check_closed_forms()),
              ('computed independently of both repositories',
               checks_independent()),
              ('the repository\'s roots, certificate and code', checks()))
    for title, results in groups:
        print('  %s' % title)
        for c in results:
            print('    %-4s %-36s %s' % ('ok' if c.ok else 'FAIL',
                                         c.equation, c.what))
        print()
    print('  entries the algebra does not read (checked by direct '
          'computation instead): %s' % (', '.join(unchecked()) or 'none'))
    print('  not put through anything: %s' % (', '.join(not_compared()) or 'none'))


def selftest():
    failures = []

    def check(label, ok):
        print('  %-70s %s' % (label, 'ok' if ok else 'FAIL'))
        if not ok:
            failures.append(label)

    print('the library side')
    cited = ours()
    check('both references are in the library',
          all(k in P.REFERENCES for k in REFERENCES))
    check('thirteen entries cite them', len(cited) == 13)
    check('all are in the Lie algebras and chirality group',
          all(e['field'] == 'Lie algebras and chirality' for e in cited))
    check('each names a file in one of the two repositories',
          all(e['source'].startswith(('emad-ii/chirality-standard-model: ',
                                      'brentharts/chirality-standard-model: '))
              for e in cited))
    check('the entries the algebra cannot read are the three that use traces '
          'and sums',
          sorted(unchecked()) == ['Anomaly-free hypercharge',
                                  'Cubic anomaly coefficient',
                                  'Hypercharge normalisation'])
    for c in _check_closed_forms():
        check('%s: %s' % (c.equation, c.what), c.ok)
    print()
    print('computed independently of both repositories')
    for c in checks_independent():
        check('%s: %s' % (c.equation, c.what), c.ok)
    print()
    if not available():
        print('the chirality-standard-model repository')
        print('  skipped: not importable (CHIRALITY_DIR; needs numpy and sympy)')
        print()
        print('rosettachirality: library side only, %d failure(s).'
              % len(failures))
        return len(failures)
    print('the chirality-standard-model repository')
    results = checks()
    for c in results:
        check('%s: %s' % (c.equation, c.what), c.ok)
    print()
    check('every entry is compared with something',
          not not_compared())
    if failures:
        print('%d failure(s): %s' % (len(failures), '; '.join(failures)))
    else:
        print('rosettachirality: %d checks against the repository, all agree.'
              % len(results))
    return len(failures)


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    _report()
