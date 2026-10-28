#!/usr/bin/env python3
r"""rosettaspectre.py -- the bridge from RosettaPhys to the spectre repository.

Eight entries in the 'Tilings' group of rosettaphys.py are drawn from
brentharts/spectre: the inflation quadratic and factor of the Spectre, its
reciprocal pair, the triplet frequency and the frequency ratio, the
count recurrence, and the two tile areas.  This module makes the claim that
they describe that repository testable: the library's own algebra reads and
evaluates each entry, and the same numbers are pulled out of the repository's
substitution matrix and tile geometry.

It also does two things the other bridges do not.

* It reads the repository's *evidence ledger* and compares the grade the
  library records for each entry (rosettaphys.EVIDENCE) with the grade the
  repository gives the underlying fact.  The grade is the repository's; the
  bridge only checks that the library copied it correctly.
* It puts the Hat constant through three independent routes: the library's
  closed form, CICY's exact arithmetic in Q(sqrt5), and the spectre
  repository's own fact for it.

The Spectre tile and its substitution are the work of Smith, Myers, Kaplan and
Goodman-Strauss; the computations on them are this repository's.  The bridge
checks arithmetic against arithmetic and claims nothing about physics.

    python3 rosettaspectre.py             what was checked, and what was not
    python3 rosettaspectre.py --selftest  the bridge, end to end

The repository is found in $SPECTRE_DIR or in a spectre directory beside this
one; it needs numpy, sympy and matplotlib.  CICY ($CICY_DIR, or beside this
directory) is optional and only the three-way Hat check needs it.  Without
either, the library side still runs and the missing side is reported.
"""

import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rosettaphys as P

REFERENCE = 'spectre2026'
MU = 4 + math.sqrt(15)
GAMMA_SMALL = 4 - math.sqrt(15)
PHI = (1 + math.sqrt(5)) / 2


def locate():
    for path in (os.environ.get('SPECTRE_DIR'),
                 os.path.join(HERE, '..', 'spectre'),
                 os.path.join(HERE, 'spectre'), os.path.expanduser('~/spectre')):
        if path and os.path.exists(os.path.join(path, 'chirality_e8.py')):
            return os.path.abspath(path)
    return None


_CACHE = {}


def load():
    """(chirality_e8, spectre, spectrefacts, spectre_ledger) or None."""
    if 'ns' in _CACHE:
        return _CACHE['ns']
    root = locate()
    ns = None
    if root is not None:
        sys.dont_write_bytecode = True
        os.environ.setdefault('MPLBACKEND', 'Agg')
        if root not in sys.path:
            sys.path.insert(0, root)
        try:
            import chirality_e8
            import spectre
            import spectrefacts
            import spectre_ledger
            ns = (chirality_e8, spectre, spectrefacts, spectre_ledger)
        except Exception as error:  # a missing dependency, say
            _CACHE['error'] = '%s: %s' % (type(error).__name__, error)
    _CACHE['ns'] = ns
    return ns


def available():
    return load() is not None


def load_cicy():
    """CICY's monotile module, or None."""
    if 'cicy' in _CACHE:
        return _CACHE['cicy']
    mod = None
    for path in (os.environ.get('CICY_DIR'), os.path.join(HERE, '..', 'CICY'),
                 os.path.join(HERE, 'CICY'), os.path.expanduser('~/CICY')):
        if path and os.path.exists(os.path.join(path, 'pyCICY', 'monotile.py')):
            sys.dont_write_bytecode = True
            root = os.path.abspath(path)
            if root not in sys.path:
                sys.path.insert(0, root)
            try:
                from pyCICY import monotile as mod
            except Exception as error:
                _CACHE['cicy_error'] = '%s: %s' % (type(error).__name__, error)
            break
    _CACHE['cicy'] = mod
    return mod


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
    out.append(Check('Spectre inflation factor', 'mu = 4 + sqrt(15)',
                     predicts('Spectre inflation factor', {}), MU, 1e-12))
    out.append(Check('Spectre inflation quadratic', 'mu^2 = 8 mu - 1 at the root',
                     predicts('Spectre inflation quadratic', {'mu': MU}),
                     MU * MU, 1e-12))
    out.append(Check('Spectre triplet frequency', 'g = 4 - sqrt(15)',
                     predicts('Spectre triplet frequency', {}), GAMMA_SMALL,
                     1e-12))
    out.append(Check('Spectre frequency ratio', 'v_Theta = v_Gamma / mu',
                     predicts('Spectre frequency ratio',
                              {'mu': MU, 'v_Gamma': 1.0}), 1.0 / MU, 1e-12))
    out.append(Check('Spectre count recurrence', "N'' = 8 N' - N: 63 from 8, 1",
                     predicts('Spectre count recurrence',
                              {'N': 1.0, 'N_prime': 8.0}), 63.0, 1e-12))
    out.append(Check('Spectre tile area', 'the Hat, (a, b) = (1, sqrt 3)',
                     predicts('Spectre tile area',
                              {'a': 1.0, 'b': math.sqrt(3)}),
                     8 * math.sqrt(3), 1e-12))
    out.append(Check('Spectre tile area', 'the equal-edge spectre, (1, 1)',
                     predicts('Spectre tile area', {'a': 1.0, 'b': 1.0}),
                     3 + 3 * math.sqrt(3), 1e-12))
    out.append(Check('Spectre tile area', 'the turtle, (sqrt 3, 1)',
                     predicts('Spectre tile area',
                              {'a': math.sqrt(3), 'b': 1.0}),
                     10 * math.sqrt(3), 1e-12))
    out.append(Check('Hat tile area', 'A_H = 8 sqrt(3)',
                     predicts('Hat tile area', {}), 8 * math.sqrt(3), 1e-12))
    out.append(Check('Hat inflation factor', 'kappa = (7 + 3 sqrt 5)/2',
                     predicts('Hat inflation factor', {}), PHI ** 4, 1e-12))
    out.append(Check('Hat constant as a golden power', 'kappa = phi^4',
                     predicts('Hat constant as a golden power', {'phi': PHI}),
                     (7 + 3 * math.sqrt(5)) / 2, 1e-12))
    return out


# ------------------------------------------------------ repository checks

def _matrix_powers(M, n):
    """Exact integer powers of the substitution matrix, as Python ints."""
    size = len(M)
    base = [[int(round(M[i][j])) for j in range(size)] for i in range(size)]
    power = [[int(i == j) for j in range(size)] for i in range(size)]
    out = [power]
    for _ in range(n):
        power = [[sum(power[i][k] * base[k][j] for k in range(size))
                  for j in range(size)] for i in range(size)]
        out.append(power)
    return out


TRANSIENT = 2


def recurrence_residuals(generations=10, skip=TRANSIENT):
    """Which species obey N'' = 8 N' - N from each starting tile.

    Returns {species: {start: largest |N_{n+2} - 8 N_{n+1} + N_n|}} over
    n >= skip.  The characteristic polynomial of the matrix has a factor of
    lambda to the fifth, a transient, so the first generations are exempt;
    the library's claim is that six species give zero for every start from
    the third generation on, and that the other three do not.
    """
    ns = load()
    if ns is None:
        return None
    chirality = ns[0]
    names = list(chirality.TILE_NAMES)
    powers = _matrix_powers(chirality.substitution_matrix().tolist(),
                            generations + 2)
    out = {}
    for i, species in enumerate(names):
        out[species] = {}
        for j, start in enumerate(names):
            counts = [powers[n][i][j] for n in range(generations + 3)]
            out[species][start] = max(
                abs(counts[n + 2] - 8 * counts[n + 1] + counts[n])
                for n in range(skip, generations + 1))
    return out


def homogeneous_species():
    res = recurrence_residuals()
    if res is None:
        return None
    return [s for s, row in res.items() if all(v == 0 for v in row.values())]


def _shoelace(points):
    n = len(points)
    return abs(sum(points[i][0] * points[(i + 1) % n][1]
                   - points[(i + 1) % n][0] * points[i][1]
                   for i in range(n))) / 2.0


def checks():
    ns = load()
    if ns is None:
        return []
    chirality, spectre, facts, _ = ns
    import numpy as np
    out = []
    M = chirality.substitution_matrix()
    evals = np.sort(np.linalg.eigvals(M).real)
    perron, lam_tiles = chirality.tile_frequencies()
    names = list(chirality.TILE_NAMES)
    freq = dict(zip(names, lam_tiles))

    out.append(Check('Spectre inflation factor',
                     'the Perron eigenvalue of the nine-species matrix',
                     predicts('Spectre inflation factor', {}), perron, 1e-12))
    out.append(Check('Spectre inflation quadratic',
                     'mu^2 against the Perron eigenvalue squared',
                     predicts('Spectre inflation quadratic', {'mu': perron}),
                     perron ** 2, 1e-12))
    nearest = min(evals, key=lambda e: abs(e - GAMMA_SMALL))
    out.append(Check('Spectre triplet frequency',
                     'the small root of the quadratic is a matrix eigenvalue',
                     predicts('Spectre triplet frequency', {}), nearest, 1e-9))
    out.append(Check('Spectre reciprocal pair', 'g times mu is one',
                     predicts('Spectre triplet frequency', {})
                     * predicts('Spectre inflation factor', {}), 1.0, 1e-12))
    # the three species that every supertile contains once
    triple = sorted(s for s, v in freq.items()
                    if abs(v - GAMMA_SMALL) < 1e-9)
    for s in triple:
        out.append(Check('Spectre triplet frequency',
                         'frequency of %s in the Perron vector' % s,
                         predicts('Spectre triplet frequency', {}),
                         freq[s], 1e-9))
    out.append(Check('Spectre triplet frequency',
                     'exactly three species have that frequency',
                     float(len(triple)), 3.0, 0.0))
    out.append(Check('Spectre frequency ratio',
                     'v_Theta from v_Gamma, against the Perron vector',
                     predicts('Spectre frequency ratio',
                              {'mu': perron, 'v_Gamma': freq['Gamma']}),
                     freq['Theta'], 1e-9))
    homogeneous = homogeneous_species()
    out.append(Check('Spectre count recurrence',
                     'six species obey it exactly from every start, after two generations',
                     float(len(homogeneous)), 6.0, 0.0))
    out.append(Check('Spectre count recurrence',
                     'the six are Gamma, Delta, Theta, Lambda, Sigma, Phi',
                     float(sorted(homogeneous) == sorted(
                         ['Gamma', 'Delta', 'Theta', 'Lambda', 'Sigma', 'Phi'])),
                     1.0, 0.0))
    # area against the tile geometry, by the shoelace formula
    for label, (a, b) in (('Hat (1, sqrt 3)', (1.0, math.sqrt(3))),
                          ('spectre (1, 1)', (1.0, 1.0)),
                          ('turtle (sqrt 3, 1)', (math.sqrt(3), 1.0)),
                          ('generic (1.3, 0.7)', (1.3, 0.7))):
        out.append(Check('Spectre tile area',
                         'shoelace area of get_spectre_points, %s' % label,
                         predicts('Spectre tile area', {'a': a, 'b': b}),
                         _shoelace(spectre.get_spectre_points(a, b)), 1e-9))
    out.append(Check('Hat tile area', 'shoelace area at (1, sqrt 3)',
                     predicts('Hat tile area', {}),
                     _shoelace(spectre.get_spectre_points(1.0, math.sqrt(3))),
                     1e-9))
    return out


def hat_three_ways():
    """kappa from the library, from CICY's exact arithmetic, from spectre.

    Returns a dict of floats, with None for a side that is not available.
    The CICY value is a Quad over sqrt 5 verified as a root exactly; the
    spectre value is a sympy expression in its fact table.
    """
    out = {'library': predicts('Hat inflation factor', {}),
           'cicy': None, 'spectre': None, 'cicy_exact_root': None}
    mono = load_cicy()
    if mono is not None:
        info = mono.inflation_factor()
        out['cicy_exact_root'] = bool(info['is_root'] and info['is_phi4'])
        v = info['value']
        out['cicy'] = float(v) if hasattr(v, '__float__') else None
        if out['cicy'] is None:
            for a, b in (('a', 'b'), ('x', 'y'), ('rational', 'surd')):
                if hasattr(v, a) and hasattr(v, b):
                    out['cicy'] = float(getattr(v, a)) + float(getattr(v, b)) * math.sqrt(5)
                    break
    ns = load()
    if ns is not None:
        import sympy as sp
        out['spectre'] = float(sp.N(ns[2].get('hat_perron').value, 15))
    return out


# --------------------------------------------------------- evidence grades

def evidence_comparison():
    """The library's recorded grade against the repository's ledger.

    Returns a list of (entry, library_kinds, ledger_kinds, library_lean,
    ledger_lean, fact_present) for every graded entry.
    """
    ns = load()
    if ns is None:
        return None
    facts, ledger = ns[2], ns[3]
    rows = {r['key']: r for r in ledger.ledger()}
    out = []
    for name, (key, kinds, lean) in sorted(P.EVIDENCE.items()):
        row = rows.get(key)
        out.append((name, set(kinds), row['kinds'] if row else None, lean,
                    row['lean'] if row else None, row is not None))
    return out


def ours():
    return list(P.cited(REFERENCE))


def unchecked():
    names = []
    for entry in ours():
        try:
            P.read_relation(entry['latex'])
        except Exception:
            names.append(entry['name'])
    return names


def not_compared():
    compared = {c.equation for c in _check_closed_forms() + checks()}
    return sorted(e['name'] for e in ours() if e['name'] not in compared)


def _report():
    print('rosettaspectre: the spectre repository, as seen from RosettaPhys')
    print('  %s' % P.cite_text(REFERENCE))
    print('  %d entries cite it' % len(ours()))
    root = locate()
    print('  spectre found at %s' % (root or 'nowhere (set SPECTRE_DIR)'))
    if root and not available():
        print('  but it did not import: %s' % _CACHE.get('error'))
    print()
    for c in _check_closed_forms() + checks():
        print('  %-4s %-30s %s' % ('ok' if c.ok else 'FAIL', c.equation, c.what))
    res = recurrence_residuals()
    if res:
        print()
        print('  count recurrence, largest residual over ten generations, by '
              'species and start:')
        for species, row in res.items():
            print('    %-7s %s' % (species, ' '.join('%4d' % row[s] for s in row)))
        print('    (columns: %s)' % ' '.join(res))
    three = hat_three_ways()
    print()
    print('  Hat kappa: library %.12f, CICY %s, spectre %s' % (
        three['library'],
        '%.12f (root verified exactly: %s)' % (three['cicy'],
                                              three['cicy_exact_root'])
        if three['cicy'] is not None else 'not available',
        '%.12f' % three['spectre'] if three['spectre'] is not None
        else 'not available'))
    cmp_ = evidence_comparison()
    if cmp_:
        print()
        print('  the library\'s evidence grades against the repository\'s ledger:')
        for name, mine, theirs, lm, tm, present in cmp_:
            same = present and mine == theirs and lm == tm
            print('    %-4s %-30s %s%s' % (
                'ok' if same else 'FAIL', name, ''.join(sorted(mine)),
                ' + Lean %s' % lm if lm else ''))
    print()
    print('  not put through the repository: %s'
          % (', '.join(not_compared()) or 'none'))


def selftest():
    failures = []

    def check(label, ok):
        print('  %-66s %s' % (label, 'ok' if ok else 'FAIL'))
        if not ok:
            failures.append(label)

    print('the library side')
    cited = ours()
    check('the spectre repository is a reference', REFERENCE in P.REFERENCES)
    check('eight entries cite it', len(cited) == 8)
    check('all eight are in the tilings group',
          all(e['field'] == 'Tilings' for e in cited))
    check('each names a spectre file or function',
          all('brentharts/spectre:' in e['source'] for e in cited))
    check('every entry is read by the algebra', not unchecked())
    check('every cited entry carries a grade from the ledger',
          all(P.evidence_for(e) is not None for e in cited))
    check('the Lean-checked entries are the four the ledger names',
          sorted(e['name'] for e in cited
                 if (P.evidence_for(e) or {}).get('lean'))
          == ['Spectre frequency ratio', 'Spectre inflation factor',
              'Spectre reciprocal pair', 'Spectre triplet frequency'])
    check('the count-recurrence blurb says it fails for three species',
          'three' in _entry('Spectre count recurrence')['blurb']
          and 'Xi, Pi and Psi' in _entry('Spectre count recurrence')['blurb'])
    for c in _check_closed_forms():
        check('%s: %s' % (c.equation, c.what), c.ok)
    print()
    if not available():
        print('the spectre repository')
        print('  skipped: not importable (SPECTRE_DIR; needs numpy, sympy, '
              'matplotlib)')
        print()
        print('rosettaspectre: library side only, %d failure(s).' % len(failures))
        return len(failures)
    print('the spectre repository')
    results = checks()
    for c in results:
        check('%s: %s' % (c.equation, c.what), c.ok)
    res = recurrence_residuals()
    check('Xi, Pi and Psi break the recurrence from at least one start',
          all(any(v != 0 for v in res[s].values()) for s in ('Xi', 'Pi', 'Psi')))
    print()
    print('Hat constant, three routes')
    three = hat_three_ways()
    check('library: kappa = phi^4', abs(three['library'] - PHI ** 4) < 1e-12)
    check('spectre: hat_perron agrees with the library',
          three['spectre'] is not None
          and abs(three['spectre'] - three['library']) < 1e-12)
    if three['cicy'] is None:
        print('  CICY: skipped (not importable)')
    else:
        check('CICY: exact Q(sqrt5) value agrees with the library',
              abs(three['cicy'] - three['library']) < 1e-12)
        check('CICY: kappa verified a root of the quadratic exactly, as phi^4',
              three['cicy_exact_root'] is True)
    print()
    print('evidence grades')
    for name, mine, theirs, lm, tm, present in evidence_comparison():
        check('%s: library grade %s%s matches the ledger' % (
            name, ''.join(sorted(mine)), '+Lean' if lm else ''),
            present and mine == theirs and lm == tm)
    print()
    if failures:
        print('%d failure(s): %s' % (len(failures), '; '.join(failures)))
    else:
        print('rosettaspectre: %d checks against the repository, all agree.'
              % len(results))
    return len(failures)


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    _report()
