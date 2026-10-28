#!/usr/bin/env python3
r"""rosettacicy.py -- the bridge from RosettaPhys to CICY.

The 'Gauge unification' group in rosettaphys.py is drawn from CICY
(brentharts/CICY, the Python package `pyCICY`, originally by Robin Schneider
and extended in this fork).  Nine entries carry a `source` naming the CICY
function they describe.  This module makes that claim testable: the library's
own algebra reads and evaluates each entry, and the same numbers go through the
CICY function.

CICY is explicit about what it cannot do -- no physical couplings, no masses,
no moduli -- and so is this bridge: it checks arithmetic against arithmetic and
claims nothing about whether a compactification describes the world.

    python3 rosettacicy.py             what was checked, and what was not
    python3 rosettacicy.py --selftest  the bridge, end to end

CICY is found in $CICY_DIR, or in a CICY directory beside this one; it needs
numpy, scipy, sympy and texttable.  Without it the library side still runs and
the CICY side reports that plainly.
"""

import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rosettaphys as P

REFERENCE = 'cicy2026'
FIELD = 'Gauge unification'
MSSM = (33 / 5, 1.0, -3.0)
SM = (41 / 10, -19 / 6, -7.0)


def locate():
    for path in (os.environ.get('CICY_DIR'), os.path.join(HERE, '..', 'CICY'),
                 os.path.join(HERE, 'CICY'), os.path.expanduser('~/CICY')):
        if path and os.path.exists(os.path.join(path, 'pyCICY', 'theories',
                                                'running.py')):
            return os.path.abspath(path)
    return None


_CACHE = {}


def load():
    """(running, couplings, breaking) from CICY, or None."""
    if 'ns' in _CACHE:
        return _CACHE['ns']
    root = locate()
    ns = None
    if root is not None:
        sys.dont_write_bytecode = True
        if root not in sys.path:
            sys.path.insert(0, root)
        try:
            from pyCICY.theories import couplings, running
            from pyCICY import breaking
            ns = (running, couplings, breaking)
        except Exception as error:  # a missing dependency, say
            _CACHE['error'] = '%s: %s' % (type(error).__name__, error)
    _CACHE['ns'] = ns
    return ns


def available():
    return load() is not None


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
        if self.reference == 0.0:
            return abs(self.library)
        return abs(self.library - self.reference) / abs(self.reference)

    @property
    def ok(self):
        return self.error <= self.tolerance


# ---------------------------------------------------- library-only checks

def _check_closed_forms():
    """Entries against the formula they state, evaluated independently."""
    out = []
    a1, a2 = 59.0, 29.57
    for label, b in (('MSSM', MSSM), ('Standard Model', SM)):
        w1 = (b[2] - b[1]) / (b[0] - b[1])
        w2 = (b[0] - b[2]) / (b[0] - b[1])
        inv = predicts('Unification prediction',
                       {'alpha_1': 1.0 / a1, 'alpha_2': 1.0 / a2, 'b_1': b[0],
                        'b_2': b[1], 'b_3': b[2]})
        out.append(Check('Unification prediction',
                         '1/alpha_3 from %s b, with 1/alpha_i as the inputs'
                         % label, inv, w1 * a1 + w2 * a2, 1e-12))
    out.append(Check('One-loop coefficient (QCD)', 'N = 3, n_f = 6 gives -7',
                     predicts('One-loop coefficient (QCD)',
                              {'N': 3.0, 'n_f': 6.0}), -7.0, 1e-12))
    out.append(Check('One-loop coefficient (SUSY)', 'N = 3, n_f = 6 gives -3',
                     predicts('One-loop coefficient (SUSY)',
                              {'N': 3.0, 'n_f': 6.0}), -3.0, 1e-12))
    out.append(Check('Generation count', 'I = -9, G = 3 gives three',
                     predicts('Generation count', {'I': -9.0, 'G': 3.0}),
                     3.0, 1e-12))
    return out


# --------------------------------------------------------- CICY checks

def checks():
    ns = load()
    if ns is None:
        return []
    running, couplings, breaking = ns
    out = []
    for label, b in (('MSSM', MSSM), ('Standard Model', SM)):
        _, inv = couplings.predict_alpha3(*b)
        lib = predicts('Unification prediction',
                       {'alpha_1': 1.0 / couplings.ALPHA1_INV_MZ,
                        'alpha_2': 1.0 / couplings.ALPHA2_INV_MZ,
                        'b_1': b[0], 'b_2': b[1], 'b_3': b[2]})
        out.append(Check('Unification prediction',
                         '1/alpha_3(M_Z), %s spectrum' % label, lib, inv, 1e-12))
    for ng in (3, 4, 5):
        b3 = float(running.beta_coefficients(ng, 1)[2])
        out.append(Check('One-loop coefficient (SUSY)',
                         'b_3 for %d generations (N = 3, n_f = 2 n_g)' % ng,
                         predicts('One-loop coefficient (SUSY)',
                                  {'N': 3.0, 'n_f': 2.0 * ng}), b3, 1e-12))
    # the running entry against unification_point(): alpha_1 and alpha_2 at M_Z
    point = couplings.unification_point(*MSSM)
    for i, inv_mz in ((0, couplings.ALPHA1_INV_MZ), (1, couplings.ALPHA2_INV_MZ)):
        # the right-hand side is 1/alpha_G + b/(2 pi) ln(M_G / mu)
        rhs = predicts('One-loop running',
                       {'alpha_G': 1.0 / point['alpha_gut_inv'],
                        'b_i': MSSM[i], 'pi': math.pi,
                        'M_G': point['m_gut'], 'mu': couplings.M_Z})
        out.append(Check('One-loop running',
                         '1/alpha_%d(M_Z) from the unification point of MSSM b'
                         % (i + 1), rhs, inv_mz, 1e-9))
    lam = running.lambda_qcd(1 / 25.0, 5e17, 3)['lambda_qcd']
    out.append(Check('Dimensional transmutation',
                     'Lambda for alpha = 1/25, M = 5e17, three generations',
                     predicts('Dimensional transmutation',
                              {'M': 5e17, 'b_3': -3.0, 'alpha': 1 / 25.0,
                               'pi': math.pi}), lam, 1e-12))
    out.append(Check('Electromagnetic coupling at the Z',
                     '1/alpha_em(M_Z) from 1/alpha_1 and 1/alpha_2',
                     predicts('Electromagnetic coupling at the Z',
                              {'alpha_2': 1.0 / couplings.ALPHA2_INV_MZ,
                               'alpha_1': 1.0 / couplings.ALPHA1_INV_MZ}),
                     couplings.alpha_em_inverse_mz(), 1e-12))
    out.append(Check('Thomson limit', '1/alpha(0) from 1/alpha(M_Z) and the shift',
                     predicts('Thomson limit',
                              {'alpha_em': 1.0 / couplings.ALPHA_EM_INV_MZ,
                               'epsilon': couplings.DELTA_ALPHA}),
                     couplings.alpha_em_inverse_zero(), 1e-12))
    out.append(Check('Generation count', 'ind(V) = -12 on a Gamma of order 4',
                     predicts('Generation count', {'I': -12.0, 'G': 4.0}),
                     float(breaking.generations_downstairs(-12, 4)), 1e-12))
    return out


def blind_spot():
    """The generation-independence of the unification prediction, as numbers.

    Returns {n_generations: 1/alpha_3} from CICY's b_i, which should be
    identical for every n_g: a complete generation adds the same to every b.
    """
    ns = load()
    if ns is None:
        return None
    running, couplings, _ = ns
    return {ng: couplings.predict_alpha3(*running.beta_coefficients(ng, 1))[1]
            for ng in (3, 4, 5, 6)}


def ours():
    """The entries of this bridge's group that cite CICY.  The tilings group
    cites CICY too (pyCICY.monotile); it is not this bridge's business."""
    return [e for e in P.cited(REFERENCE) if e['field'] == FIELD]


def unchecked():
    names = []
    for entry in ours():
        try:
            P.read_relation(entry['latex'])
        except Exception:
            names.append(entry['name'])
    return names


def not_compared():
    """Entries the algebra reads but that this bridge does not put through CICY."""
    compared = {c.equation for c in checks()}
    return sorted(e['name'] for e in ours() if e['name'] not in compared)


def _report():
    print('rosettacicy: CICY, as seen from RosettaPhys')
    print('  %s' % P.cite_text(REFERENCE))
    print('  %d entries cite it: %d in the gauge unification group, the rest '
          'in the tilings group' % (len(P.cited(REFERENCE)), len(ours())))
    root = locate()
    print('  CICY found at %s' % (root or 'nowhere (set CICY_DIR)'))
    if root and not available():
        print('  but it did not import: %s' % _CACHE.get('error'))
    print()
    for c in _check_closed_forms() + checks():
        print('  %-4s %-36s %s' % ('ok' if c.ok else 'FAIL', c.equation, c.what))
    spot = blind_spot()
    if spot:
        print()
        print('  1/alpha_3 by generation count (identical, because only '
              'differences of b enter):')
        print('    ' + ', '.join('n_g=%d: %.6f' % kv for kv in sorted(spot.items())))
    print()
    print('  not put through CICY: %s' % (', '.join(not_compared()) or 'none'))


def selftest():
    failures = []

    def check(label, ok):
        print('  %-62s %s' % (label, 'ok' if ok else 'FAIL'))
        if not ok:
            failures.append(label)

    print('the library side')
    cited = ours()
    check('CICY is a reference', REFERENCE in P.REFERENCES)
    check('nine gauge unification entries cite it', len(cited) == 9)
    check('the tilings group cites it too, through pyCICY.monotile',
          len(P.cited(REFERENCE)) - len(cited) == 4
          and all(e['field'] == 'Tilings' for e in P.cited(REFERENCE)
                  if e not in cited))
    check('each names the CICY function it describes',
          all('pyCICY' in e['source'] for e in cited))
    check('the one-loop coefficient joins the lattice coupling on N',
          (P.join('One-loop coefficient (QCD)', 'Lattice coupling') or
           type('x', (), {'pivot': None})).pivot == 'N')
    check('alpha and the lattice inverse coupling never join',
          P.join('One-loop running', 'Lattice coupling') is None
          and P.join('Unification prediction', 'Lattice coupling') is None)
    for c in _check_closed_forms():
        check('%s: %s' % (c.equation, c.what), c.ok)
    print()
    if not available():
        print('CICY')
        print('  skipped: not importable (CICY_DIR; needs texttable)')
        print()
        print('rosettacicy: library side only, %d failure(s).' % len(failures))
        return len(failures)
    print('CICY')
    results = checks()
    for c in results:
        check('%s: %s' % (c.equation, c.what), c.ok)
    spot = blind_spot()
    check('1/alpha_3 is identical for three to six generations',
          max(spot.values()) - min(spot.values()) < 1e-12)
    check('the anomaly entry and the non-SUSY coefficient are left uncompared',
          not_compared() == ['Heterotic anomaly condition',
                             'One-loop coefficient (QCD)'])
    print()
    if failures:
        print('%d failure(s): %s' % (len(failures), '; '.join(failures)))
    else:
        print('rosettacicy: %d checks against CICY, all agree.' % len(results))
    return len(failures)


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    _report()
