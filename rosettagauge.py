#!/usr/bin/env python3
r"""rosettagauge.py -- the gauge-group entries of RosettaPhys, put through the repositories.

Eight entries of rosettaphys.py were written for the Yang-Mills paper rather
than taken from a repository, and none of them carries a source: the dimension
of SU(N), the dual Coxeter number of a simply laced algebra, the adjoint index,
the one-loop coefficient for any group, the transmutation slope of the O(N)
model and of an SU(N) lattice, and the block step each induces.  What the
group adds is the thread from the size of a group to the slope of its coupling,
and the leading-order statement of what blocking a lattice by a length factor
does to that coupling.

They are textbook arithmetic, so there is no repository to cite them to.  This
module does the opposite: it takes the numbers each repository holds and puts
them back through the entries.

* the laboratory's own group code (ymlab) for the dimension of SU(2) and SU(3),
  and its symbolic slopes for the two transmutation slopes and the factor-two
  coupling shift, taken at a coupling large enough that its correction terms
  vanish;
* the chirality repository's audit of the exceptional algebras, for the
  dimension, rank and dual Coxeter number of E6, E7, E8, F4 and G2;
* the CICY repository's Standard Model coefficient b_3 = -7;
* the nariai repository's linear inflation factor, as the length factor of the
  block step.

What it does not do is test the block step.  The entries state it at leading
order, with the tiling entering through the logarithm of one number, and
`block_table` sets that beside what the laboratory predicts at the couplings it
runs and what its simulations measured.  Those differ, by a factor that depends
on the lattice, and the table says by how much.  Whether an aperiodic
inflation is a legitimate blocking of a lattice at all is not a thing any of
these numbers can say.

    python3 rosettagauge.py             the tables, and what was not checked
    python3 rosettagauge.py --selftest  the bridge, end to end
"""

import importlib
import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rosettaphys as P
import rosettachirality as CH
import rosettacicy as CI
import rosettaym as Y
import rosettanariai as NR

ENTRIES = (
    'Special unitary dimension',
    'Dual Coxeter number (simply laced)',
    'Adjoint index',
    'One-loop coefficient (any group)',
    'Spin-model transmutation slope',
    'Gauge transmutation slope',
    'Spin block coupling',
    'Gauge block coupling',
)

#: the length factor of the block steps the paper compares, as a name and a
#: way to get it: 2 is the usual blocking, the other is one Spectre inflation
FACTOR_TWO = 2.0


def _entry(name):
    entry = P.GRAPH.find(name, 'equation')
    if entry is None:
        raise KeyError('no equation called %r' % name)
    return entry


def predicts(name, known):
    """The right-hand side of a library entry, evaluated."""
    known = dict(known)
    known.setdefault('pi', math.pi)
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


_CACHE = {}


# ------------------------------------------------ the library's arithmetic
#
# Every number below is read out of an entry, never typed in beside it, so a
# change to an entry changes the table.

def su_dimension(n):
    return predicts('Special unitary dimension', {'N': n})


def dual_coxeter(dimension, rank):
    """h from the dimension and the rank, through the two entries that give it.

    The roots are the dimension less the rank (the entry for the dimension,
    solved for R); the quotient of the roots by the rank is the number.
    """
    roots = dimension - rank
    return predicts('Dual Coxeter number (simply laced)',
                    {'R': roots, 'r': rank})


def pure_gauge_b(h):
    """The one-loop coefficient of the pure gauge theory, n_f = 0."""
    return predicts('One-loop coefficient (any group)',
                    {'T_a': h, 'n_f': 0.0, 'T_f': 0.5})


def slope_per_inverse_coupling(h):
    """How fast the log of the mass falls with 1/g^2, for any group.

    From the pure-gauge coefficient: the gauge coupling obeys
    dg/d ln(mu) = -b0 g^3 with b0 = -b / (16 pi^2), so ln a = -1 / (2 b0 g^2)
    and the slope in 1/g^2 is 1 / (2 b0).  For SU(N) with beta = 2N/g^2 this
    divided by 2N is the transmutation slope, which is checked.
    """
    b0 = -pure_gauge_b(h) / (16.0 * math.pi ** 2)
    return 1.0 / (2.0 * b0)


def spin_slope(n):
    return predicts('Spin-model transmutation slope', {'N': n})


def gauge_slope(n):
    return predicts('Gauge transmutation slope', {'N': n})


def linear_factor():
    return predicts('Spectre linear inflation', {})


def block_shift(kind, slope, factor):
    """How far a block step lowers the coupling, as a positive number.

    The entry gives the new coupling; the shift is what it subtracts.
    """
    name, symbol = {'spin': ('Spin block coupling', 'r_s'),
                    'gauge': ('Gauge block coupling', 'r_g')}[kind]
    new = predicts(name, {'beta_0': 0.0, 'ell': factor, symbol: slope})
    return -new


# ------------------------------------------------------------ the repositories

def audit():
    """The chirality repository's audit of the exceptional algebras, or None."""
    if 'audit' in _CACHE:
        return _CACHE['audit']
    data = None
    ns = CH.load()
    if ns is not None:
        path = os.path.join(ns[3], 'verification', 'certificates',
                            'exceptional_rank_deficient_audit.json')
        if os.path.exists(path):
            with open(path) as handle:
                data = json.load(handle)
    _CACHE['audit'] = data
    return data


#: the dimension, rank and dual Coxeter number the exceptional algebras have in
#: any table; the audit is checked against these when it is there, and these
#: stand in for it when it is not
EXCEPTIONAL = {
    'E6': (78, 6, 12), 'E7': (133, 7, 18), 'E8': (248, 8, 30),
    'F4': (52, 4, 9), 'G2': (14, 2, 4),
}


def exceptional(name):
    """(dimension, rank, dual Coxeter number) for an exceptional algebra."""
    data = audit()
    if data is not None and name in data['ambients']:
        a = data['ambients'][name]
        return a['dimension'], a['rank'], a['dual_coxeter_number']
    return EXCEPTIONAL[name]


def lab():
    """Everything the laboratory supplies, or None if it is not there."""
    if 'lab' in _CACHE:
        return _CACHE['lab']
    out = None
    if Y.available():
        try:
            Y.load()
            findings = importlib.import_module('ymlab.findings')
            out = {
                'on_comparison': findings.on_comparison(),
                'symbolic': importlib.import_module('ymlab.symbolic'),
                'groups': importlib.import_module('ymlab.group_interface'),
                'su3': importlib.import_module('ymlab.su3'),
            }
        except Exception as error:
            _CACHE['lab_error'] = '%s: %s' % (type(error).__name__, error)
            out = None
    _CACHE['lab'] = out
    return out


def lab_algebra_dimension(group, samples=60, epsilon=1e-5):
    """The dimension of a group's Lie algebra, found from its own code.

    Elements near the identity, taken from the group's small_random, are
    U = 1 + H + ...; the traceless part of the anti-Hermitian part of U is H
    to first order, and the rank of a stack of them is the number of
    independent directions the group's elements actually move in.
    """
    import numpy as np
    rng = np.random.default_rng(2026)
    rows = []
    for _ in range(samples):
        u = group.small_random(epsilon, rng)
        a = (u - u.conj().T) / 2.0
        a = a - (np.trace(a) / a.shape[0]) * np.eye(a.shape[0])
        rows.append(np.concatenate([a.real.ravel(), a.imag.ravel()]))
    s = np.linalg.svd(np.array(rows), compute_uv=False)
    return int((s > 1e-6 * s[0]).sum())


def lab_slope(kind, n, beta=1e9):
    """The laboratory's symbolic log-slope, magnitude, at a coupling so large
    that its correction terms vanish; it is then the leading term alone."""
    L = lab()
    S = L['symbolic']
    model = S.on_mass_log_slope() if kind == 'spin' else S.su_n_log_spacing_slope()
    return abs(model.numeric(n, beta))


# ---------------------------------------------------------------- the checks

def _check_library():
    """The entries against each other and against closed forms, no repository."""
    out = []
    for n in (2, 3, 4, 5):
        out.append(Check('Special unitary dimension',
                         'SU(%d): the closed form n(n+2) for A_(n-1)' % n,
                         su_dimension(n), CH.simple_dimension('A', n - 1), 0))
        roots, rank = CH.roots_and_rank('A', n - 1)
        out.append(Check('Dual Coxeter number (simply laced)',
                         'SU(%d): roots %d over rank %d is N' % (n, roots, rank),
                         dual_coxeter(su_dimension(n), rank), n, 0))
    for n in (4, 5):
        roots, rank = CH.roots_and_rank('D', n)
        out.append(Check('Dual Coxeter number (simply laced)',
                         'D%d: roots over rank is 2n - 2' % n,
                         dual_coxeter(CH.simple_dimension('D', n), rank),
                         2 * n - 2, 0))
    # the one-loop coefficient of any group, specialised to SU(N) with
    # fundamentals, is the entry that was already in the library
    for n, nf in ((3, 6), (3, 16), (2, 3)):
        out.append(Check('One-loop coefficient (any group)',
                         'SU(%d) with %d flavours: the specialised entry' % (n, nf),
                         predicts('One-loop coefficient (any group)',
                                  {'T_a': float(n), 'n_f': float(nf), 'T_f': 0.5}),
                         predicts('One-loop coefficient (QCD)',
                                  {'N': float(n), 'n_f': float(nf)}), 1e-12))
    # and the slope that comes of it, by the route through the coefficient,
    # is the entry for the slope
    for n in (2, 3, 4):
        out.append(Check('Gauge transmutation slope',
                         'SU(%d): through the pure-gauge coefficient, '
                         '24 pi^2 / (11 h) over 2N' % n,
                         slope_per_inverse_coupling(float(n)) / (2.0 * n),
                         gauge_slope(float(n)), 1e-12))
    # the same length factor in both block steps gives the logarithm of it
    for s in (2.0, linear_factor()):
        for n in (3.0, 4.0):
            out.append(Check('Spin block coupling',
                             'N = %g, s = %.4f: ln(s) over the slope' % (n, s),
                             block_shift('spin', spin_slope(n), s),
                             math.log(s) / (2.0 * math.pi / (n - 2.0)), 1e-12))
    return out


def _check_audit():
    out = []
    if audit() is None:
        return out
    for name in ('E6', 'E7', 'E8'):
        d, r, h = exceptional(name)
        out.append(Check('Dual Coxeter number (simply laced)',
                         '%s: the audit\'s dual Coxeter number, from its '
                         'dimension and rank' % name,
                         dual_coxeter(d, r), h, 0))
    data = audit()
    out.append(Check('Adjoint index',
                     'the audit takes the adjoint index to be the dual '
                     'Coxeter number',
                     1.0 if data['normalization']['T_adjoint'] == 'h_dual'
                     else 0.0, 1.0, 0))
    rows = e8_index_rows()
    for row in rows or ():
        out.append(Check('Adjoint index',
                         'E8 > E6 x SU(3), from %s: the indices of the '
                         'pieces add up to the dual Coxeter number of E8'
                         % row['view'].strip('$').replace('_', ''),
                         float(row['total']), float(row['h_e8']), 0))
    return out


def not_simply_laced():
    """(name, library's R / r, the audit's dual Coxeter number) for F4 and G2.

    The entry says the quotient is exact only when the roots have one length.
    These are the two exceptional algebras where they do not, and the quotient
    is not the dual Coxeter number; this is the entry's stated limit, seen.
    """
    out = []
    for name in ('F4', 'G2'):
        d, r, h = exceptional(name)
        out.append((name, dual_coxeter(d, r), h))
    return out


def _check_cicy():
    if not CI.available():
        return []
    return [Check('One-loop coefficient (any group)',
                  'SU(3) with six flavours is the Standard Model\'s b_3',
                  predicts('One-loop coefficient (any group)',
                           {'T_a': 3.0, 'n_f': 6.0, 'T_f': 0.5}),
                  CI.SM[2], 1e-12)]


def _check_nariai():
    if not NR.available():
        return []
    mod = NR.load()
    out = [Check('Spin block coupling',
                 'the length factor of the step is the repository\'s LINEAR',
                 linear_factor(), mod.LINEAR, 1e-12)]
    for n in (3.0, 4.0):
        out.append(Check('Spin block coupling',
                         'N = %g: ln(LINEAR) over the slope, independently' % n,
                         block_shift('spin', spin_slope(n), mod.LINEAR),
                         math.log(mod.LINEAR) * (n - 2.0) / (2.0 * math.pi),
                         1e-12))
    return out


def _check_lab():
    L = lab()
    if L is None:
        return []
    out = []
    for name, group in (('SU(2)', L['groups'].su2_group()),
                        ('SU(3)', L['groups'].su3_group())):
        out.append(Check('Special unitary dimension',
                         '%s: the rank of the group\'s own elements near the '
                         'identity' % name,
                         su_dimension(group.dimension),
                         lab_algebra_dimension(group), 0))
    out.append(Check('Special unitary dimension',
                     'SU(3): the eight Gell-Mann matrices',
                     su_dimension(3), len(L['su3'].gell_mann_matrices()), 0))
    for n in (3, 4):
        out.append(Check('Spin-model transmutation slope',
                         'N = %d: the laboratory\'s symbolic slope at '
                         'beta = 1e9' % n,
                         spin_slope(float(n)), lab_slope('spin', n), 1e-9))
    for n in (2, 3):
        out.append(Check('Gauge transmutation slope',
                         'SU(%d): the laboratory\'s two-loop slope at '
                         'beta = 1e9' % n,
                         gauge_slope(float(n)), lab_slope('gauge', n), 1e-9))
    S = L['symbolic']
    for kind, n in (('spin', 3), ('spin', 4), ('gauge', 2), ('gauge', 3)):
        slope = spin_slope(float(n)) if kind == 'spin' else gauge_slope(float(n))
        out.append(Check('%s block coupling' % kind.capitalize(),
                         '%s %d: the laboratory\'s coupling shift for a factor '
                         'of two, at beta = 1e9' % (kind, n),
                         block_shift(kind, slope, FACTOR_TWO),
                         S.beta_for_factor_two(lab_slope(kind, n)), 1e-9))
    return out


def checks():
    return (_check_library() + _check_audit() + _check_cicy()
            + _check_nariai() + _check_lab())


def not_compared():
    """Entries no check mentions -- they are still only library statements."""
    done = {c.equation for c in checks()}
    return [name for name in ENTRIES if name not in done]


# ------------------------------------------------------------------ tables

def exponent_family():
    """One row for each system whose mass falls as exp(-r times a coupling).

    Each row names its coupling, because the slope depends on which one: the
    O(N) rows are in the model's own inverse temperature, the SU(N) rows in
    beta = 2N / g^2, and every gauge row also gives the slope per 1/g^2, which
    is the one that compares groups.  The step column is how far the coupling
    moves for one Spectre inflation, in the row's own coupling, and
    `step_inverse` the same in 1/g^2 for the gauge groups.  The exceptional
    rows are arithmetic: nobody has put those groups on a lattice here, and
    the normalisation is the audit's, with the long roots of squared length
    two, which makes the adjoint index the dual Coxeter number.
    """
    ell = linear_factor()
    rows = []
    for n in (3, 4):
        r = spin_slope(float(n))
        rows.append({'system': 'O(%d) model' % n, 'kind': 'spin',
                     'coupling': r'$\beta$', 'dimension': None, 'rank': None,
                     'h': None, 'slope': r, 'per_inverse': None,
                     'step_inverse': None,
                     'step': block_shift('spin', r, ell),
                     'step_two': block_shift('spin', r, FACTOR_TWO)})
    for n in (2, 3):
        r = gauge_slope(float(n))
        h = float(n)
        rows.append({'system': 'SU(%d) lattice' % n, 'kind': 'gauge',
                     'coupling': r'$\beta = 2N/g^2$',
                     'dimension': int(su_dimension(n)), 'rank': n - 1, 'h': n,
                     'slope': r, 'per_inverse': slope_per_inverse_coupling(h),
                     'step_inverse': math.log(ell)
                     / slope_per_inverse_coupling(h),
                     'step': block_shift('gauge', r, ell),
                     'step_two': block_shift('gauge', r, FACTOR_TWO)})
    for name in ('E6', 'E7', 'E8'):
        d, rk, hh = exceptional(name)
        h = dual_coxeter(d, rk)
        per = slope_per_inverse_coupling(h)
        rows.append({'system': name, 'kind': 'exceptional',
                     'coupling': r'$1/g^2$', 'dimension': d, 'rank': rk,
                     'h': int(round(h)), 'slope': per, 'per_inverse': per,
                     'step_inverse': math.log(ell) / per,
                     'step': math.log(ell) / per,
                     'step_two': math.log(FACTOR_TWO) / per})
    return rows


def _range(values):
    values = [abs(float(v)) for v in values if v == v and v != 0]
    return (min(values), max(values)) if values else None


def block_table():
    """The block step at leading order, as predicted by the laboratory, and measured.

    One row for each of the four lattices the laboratory compares, and for
    each of the two length factors: the leading-order shift, the shift the
    laboratory's full formula predicts at the coupling it runs the model at,
    and the range of shifts the local slopes of its simulations imply.  The
    O(N) simulations are the OpenAI fork's Monte Carlo; the SU(2) ones are the
    laboratory's Metropolis scans on 4^4 and 6^4 lattices, which are small
    enough that the measured slopes are well below the prediction, and SU(3)
    has no simulation at all.
    """
    L = lab()
    ell = linear_factor()
    rows = []
    if L is None:
        return rows
    comp = L['on_comparison']
    reference = {r['model'].split(',')[0]: r for r in comp['factor_two']}
    lab_rows = {'O(3)': ('spin', 3), 'O(4)': ('spin', 4),
                'SU(2)': ('gauge', 2), 'SU(3)': ('gauge', 3)}
    for label, (kind, n) in lab_rows.items():
        ref = reference[label]
        r = spin_slope(float(n)) if kind == 'spin' else gauge_slope(float(n))
        slopes = None
        origin = None
        if kind == 'spin':
            slopes = list(comp['on'][n]['measured'])
            origin = 'Monte Carlo of the OpenAI fork'
        elif n == 2:
            slopes = []
            for size in sorted(comp['su']):
                slopes.extend(float(x) for x in comp['su'][size]['measured'])
            origin = 'Metropolis scans, 4^4 and 6^4'
        span = _range(slopes) if slopes is not None else None
        row = {'model': label, 'kind': kind, 'slope': r,
               'reference': ref['model'].split(', ')[1].replace('beta=', ''),
               'lab_slope': ref['slope'], 'origin': origin, 'measured': span,
               'steps': {}}
        for tag, s in (('two', FACTOR_TWO), ('spectre', ell)):
            lead = block_shift(kind, r, s)
            predicted = math.log(s) / ref['slope']
            meas = None
            if span is not None:
                meas = (math.log(s) / span[1], math.log(s) / span[0])
            row['steps'][tag] = {'factor': s, 'leading': lead,
                                 'predicted': predicted, 'measured': meas}
        rows.append(row)
    return rows


def e8_index_rows():
    """The index sum rule for E8 > E6 x SU(3), read two ways.

    The adjoint of E8 restricts to the adjoint of E6 and of SU(3) and to the
    27 of E6 with the 3 of SU(3), and the conjugate of both.  When the
    subalgebra sits with index one, the Dynkin indices of the pieces add up to
    the index of the adjoint, which is the dual Coxeter number: looked at from
    E6 the 27 appears three times and its conjugate three times, and looked at
    from SU(3) the 3 appears 27 times and its conjugate 27.  The multiplicities
    are the repository's, read off its roots; the indices of the 27 and of the 3
    are the audit's positive controls; the dual Coxeter numbers are the
    library's, as roots over rank.

    Returns None without the chirality repository.
    """
    ns = CH.load()
    data = audit()
    if ns is None or data is None:
        return None
    from fractions import Fraction
    branching = CH.e8_branching(ns[0])
    controls = data['normalization']['positive_controls']
    t27 = Fraction(controls['E6_27'])
    t3 = Fraction(controls['A2_fundamental'])
    h_e8 = dual_coxeter(branching['roots'] + branching['rank_e8'],
                        branching['rank_e8'])
    h_e6 = dual_coxeter(branching['e6_roots'] + branching['rank_e6'],
                        branching['rank_e6'])
    h_su3 = dual_coxeter(branching['su3_roots'] + branching['rank_su3'],
                         branching['rank_su3'])
    copies27 = branching['weights_of_3']          # the 3 of SU(3), seen from E6
    copies3 = branching['per_weight'][0]          # the 27 of E6, seen from SU(3)
    from_e6 = [('adjoint of $E_6$', 1, Fraction(h_e6).limit_denominator()),
               (r'$\mathbf{27}$', copies27, t27),
               (r'$\overline{\mathbf{27}}$', copies27, t27)]
    from_su3 = [('adjoint of $SU(3)$', 1, Fraction(h_su3).limit_denominator()),
                (r'$\mathbf{3}$', copies3, t3),
                (r'$\overline{\mathbf{3}}$', copies3, t3)]
    rows = []
    for view, pieces in (('$E_6$', from_e6), ('$SU(3)$', from_su3)):
        total = sum(m * i for _n, m, i in pieces)
        rows.append({'view': view, 'pieces': pieces, 'total': total,
                     'h_e8': Fraction(h_e8).limit_denominator()})
    return rows


# ------------------------------------------------------------------ reports

def ours():
    return [_entry(name) for name in ENTRIES]


def _report():
    print('rosettagauge: the gauge-group entries of rosettaphys.py')
    print()
    print('exponent family (slope r; mass falls as exp(-r coupling))')
    for row in exponent_family():
        print('  %-14s r = %-8.4f per 1/g^2 = %-8s step(ell) = %.4f  '
              'step(2) = %.4f'
              % (row['system'], row['slope'],
                 '-' if row['per_inverse'] is None
                 else '%.4f' % row['per_inverse'],
                 row['step'], row['step_two']))
    print()
    print('block step (positive = how far the coupling is lowered)')
    for row in block_table():
        meas = row['measured']
        print('  %-6s r = %.4f, laboratory slope %.3f at beta = %s; measured '
              'slope %s'
              % (row['model'], row['slope'], row['lab_slope'], row['reference'],
                 '-' if meas is None else '%.2f to %.2f' % meas))
        for tag in ('two', 'spectre'):
            s = row['steps'][tag]
            m = ('-' if s['measured'] is None
                 else '%.3f to %.3f' % s['measured'])
            print('         s = %.4f  leading %.4f  predicted %.4f  measured %s'
                  % (s['factor'], s['leading'], s['predicted'], m))
    print()
    print('exceptional algebras where roots over rank is not the dual Coxeter '
          'number (the limit the entry states):')
    for name, quotient, h in not_simply_laced():
        print('  %-3s R / r = %.3f, dual Coxeter number %d' % (name, quotient, h))
    print()
    missing = not_compared()
    print('  not put through anything: %s' % (', '.join(missing) or 'none'))


def selftest():
    failures = []

    def check(label, ok):
        print('  %-72s %s' % (label, 'ok' if ok else 'FAIL'))
        if not ok:
            failures.append(label)

    print('the library side')
    check('eight entries, all in the library',
          len(ENTRIES) == 8 and all(P.GRAPH.find(n, 'equation') for n in ENTRIES))
    check('none of them cites a repository (they are textbook arithmetic)',
          not any(e.get('source') for e in ours()))
    check('every one has a reading for every letter the algebra can see',
          all(n in P.READINGS for n in ENTRIES))
    for c in _check_library():
        check('%s: %s' % (c.equation, c.what), c.ok)
    print()
    print('the repositories')
    for label, group in (('the chirality audit', _check_audit()),
                         ('the CICY repository', _check_cicy()),
                         ('the nariai repository', _check_nariai()),
                         ('the laboratory', _check_lab())):
        if not group:
            print('  %-30s skipped: not importable' % label)
            continue
        for c in group:
            check('%s: %s' % (c.equation, c.what), c.ok)
    print()
    if audit() is not None:
        print('the limit the dual Coxeter entry states')
        for name, quotient, h in not_simply_laced():
            check('%s: roots over rank (%.3f) is not the dual Coxeter number (%d)'
                  % (name, quotient, h), abs(quotient - h) > 0.5)
        print()
    print('the gauge-group display')
    members = P.grand_gauge_members()
    check('it has six rows and thirteen equations',
          len(members) == 6 and sum(len(m) for m in members) == 13)
    reads = {}
    for chain in members:
        for step in chain.steps:
            for symbol, quantity in P.READINGS.get(
                    step.equation['name'], {}).items():
                reads.setdefault(symbol, set()).add(quantity)
    check('no letter in it is read two ways, since the proposition binds each once',
          not {s: q for s, q in reads.items() if len(q) > 1})
    check('the gauge block step is an arrow and not a row: its coupling is not '
          'the spin model\'s',
          all(s.equation['name'] != 'Gauge block coupling'
              for chain in members for s in chain.steps)
          and any(b['name'] == 'Gauge block coupling'
                  for _a, _k, b, _n in P.gauge_arrows()))
    print()
    print('the tables')
    rows = exponent_family()
    check('the exponent family has O(3), O(4), SU(2), SU(3), E6, E7 and E8',
          [r['system'] for r in rows] ==
          ['O(3) model', 'O(4) model', 'SU(2) lattice', 'SU(3) lattice',
           'E6', 'E7', 'E8'])
    o3 = rows[0]
    check('O(3) with one Spectre step: ln(ell) / 2 pi = 0.1642',
          abs(o3['step'] - math.log(linear_factor()) / (2.0 * math.pi)) < 1e-12
          and abs(o3['step'] - 0.1642) < 5e-5)
    check('the slope per 1/g^2 falls with h: a larger group\'s coupling runs faster',
          all(a['per_inverse'] > b['per_inverse']
              for a, b in zip(rows[2:], rows[3:])))
    check('and the step in 1/g^2 grows with h',
          all(a['step_inverse'] < b['step_inverse']
              for a, b in zip(rows[2:], rows[3:]) if a['h'] < b['h']))
    check('the step times the slope is the logarithm of ell in every row',
          all(abs(r['step'] * r['slope'] - math.log(linear_factor())) < 1e-12
              for r in rows))
    if lab() is not None:
        table = block_table()
        check('the block table has the laboratory\'s four lattices',
              [r['model'] for r in table] == ['O(3)', 'O(4)', 'SU(2)', 'SU(3)'])
        check('the laboratory\'s corrected slope is smaller than the leading '
              'one, so its predicted shift is larger',
              all(r['steps']['two']['predicted'] > r['steps']['two']['leading']
                  for r in table))
        check('and what was measured is larger again, wherever it was measured',
              all(r['steps']['two']['measured'][0]
                  > r['steps']['two']['predicted']
                  for r in table if r['measured'] is not None))
        check('SU(3) has no simulation to compare with',
              table[3]['measured'] is None)
    if failures:
        print('%d failure(s): %s' % (len(failures), '; '.join(failures)))
    else:
        print('rosettagauge: %d checks, all agree.' % len(checks()))
    return len(failures)


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    _report()
