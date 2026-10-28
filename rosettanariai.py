#!/usr/bin/env python3
r"""rosettanariai.py -- the bridge from RosettaPhys to the nariai repository.

Five entries in the 'Tilings' group of rosettaphys.py are drawn from
brentharts/nariai: the linear inflation factor, its relation to the area
factor, the quartic it satisfies, the gap-label recurrence and the tile-count
growth rate.  The source is `nariai_constants.py`, which derives every value
from the substitution matrix at import time.  This module makes the claim that
the entries describe it testable: the library's own algebra reads and
evaluates each entry, and the same numbers come out of that module.

It also puts the repository's substitution matrix next to the spectre
repository's.  The two agree exactly -- but they agree because both transcribe
the published metatile rules of Smith, Myers, Kaplan and Goodman-Strauss, not
because two derivations met.  What the check establishes is that neither
transcription has a typo, and that both give four plus root fifteen; it does
not establish more, and the bridge does not say more.

The nariai README records a retraction: an earlier inflation factor, 2.5348,
was not the spectre's.  The library never carried it, and the bridge checks
that the linear factor it does carry is nowhere near it.  The physical
predictions the repository builds on this algebra -- a gravitational-wave
polarisation, an SLE exponent, a spectral dimension -- are not in the library,
and the README itself lists open findings against them.

    python3 rosettanariai.py             what was checked, and what was not
    python3 rosettanariai.py --selftest  the bridge, end to end

nariai is found in $NARIAI_DIR or in a nariai directory beside this one; it
needs only numpy.  The spectre repository ($SPECTRE_DIR, via rosettaspectre)
is optional and only the matrix comparison needs it.
"""

import importlib.util
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rosettaphys as P

REFERENCE = 'nariai2026'
MU = 4 + math.sqrt(15)
ELL = (math.sqrt(6) + math.sqrt(10)) / 2


def locate():
    for path in (os.environ.get('NARIAI_DIR'), os.path.join(HERE, '..', 'nariai'),
                 os.path.join(HERE, 'nariai'), os.path.expanduser('~/nariai')):
        if path and os.path.exists(os.path.join(path, 'nariai_constants.py')):
            return os.path.abspath(path)
    return None


_CACHE = {}


def load():
    """The nariai_constants module, or None.

    Loaded by file path under its own name, because the repository also holds
    a spectre.py and putting its directory on sys.path would shadow the spectre
    repository's module of that name.
    """
    if 'mod' in _CACHE:
        return _CACHE['mod']
    root = locate()
    mod = None
    if root is not None:
        sys.dont_write_bytecode = True
        try:
            spec = importlib.util.spec_from_file_location(
                'nariai_constants', os.path.join(root, 'nariai_constants.py'))
            mod = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(mod)
        except Exception as error:
            mod = None
            _CACHE['error'] = '%s: %s' % (type(error).__name__, error)
    _CACHE['mod'] = mod
    return mod


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
    out = []
    ell = predicts('Spectre linear inflation', {})
    out.append(Check('Spectre linear inflation', '(sqrt6 + sqrt10)/2', ell,
                     ELL, 1e-12))
    out.append(Check('Spectre linear-area relation', 'mu = ell^2',
                     predicts('Spectre linear-area relation', {'ell': ell}),
                     MU, 1e-12))
    # the quartic: both sides at the root
    out.append(Check('Spectre linear quartic', 'ell^4 against 8 ell^2 - 1',
                     predicts('Spectre linear quartic', {'ell': ell}),
                     ell ** 4, 1e-12))
    # the recurrence on powers of the reciprocal root
    g = [MU ** (-k) for k in range(8)]
    out.append(Check('Spectre gap-label recurrence',
                     "G'' = 8 G' - G on powers of 1/mu",
                     predicts('Spectre gap-label recurrence',
                              {'G': g[3], 'G_prime': g[4]}), g[5], 1e-12))
    out.append(Check('Spectre growth rate', 'ln mu = 2.0634...',
                     predicts('Spectre growth rate', {'mu': MU}),
                     2.0634370688955608, 1e-12))
    out.append(Check('Spectre growth rate',
                     'twice the logarithm of the linear factor',
                     predicts('Spectre growth rate', {'mu': MU}),
                     2 * math.log(ELL), 1e-12))
    return out


# ------------------------------------------------------ repository checks

def checks():
    mod = load()
    if mod is None:
        return []
    out = []
    ell = predicts('Spectre linear inflation', {})
    out.append(Check('Spectre linear inflation',
                     'LINEAR (from the square root of the Perron eigenvalue)',
                     ell, mod.LINEAR, 1e-12))
    out.append(Check('Spectre linear inflation', 'LINEAR_CLOSED', ell,
                     mod.LINEAR_CLOSED, 1e-12))
    out.append(Check('Spectre linear-area relation',
                     'AREA from LINEAR, and the Perron eigenvalue of M',
                     predicts('Spectre linear-area relation',
                              {'ell': mod.LINEAR}), mod.PERRON, 1e-9))
    out.append(Check('Spectre linear quartic',
                     'residual of x^4 - 8x^2 + 1 at LINEAR',
                     abs(predicts('Spectre linear quartic',
                                  {'ell': mod.LINEAR}) - mod.LINEAR ** 4),
                     0.0, 1e-12))
    # the repository's own residual, and the entry evaluated on its labels
    g = [mod.gap_label([0] * k + [1]) for k in range(8)]
    out.append(Check('Spectre gap-label recurrence',
                     "G'' from G, G' on the repository's gap labels",
                     predicts('Spectre gap-label recurrence',
                              {'G': g[3], 'G_prime': g[4]}), g[5], 1e-12))
    out.append(Check('Spectre gap-label recurrence',
                     'the repository\'s own recurrence residual is zero',
                     mod.gap_recurrence_residual(), 0.0, 1e-15))
    out.append(Check('Spectre growth rate', 'GROWTH_RATE',
                     predicts('Spectre growth rate', {'mu': mod.AREA}),
                     mod.GROWTH_RATE, 1e-12))
    out.append(Check('Spectre growth rate',
                     'GROWTH_RATE is 2 LOG_LINEAR, not the same number',
                     predicts('Spectre growth rate', {'mu': mod.AREA}),
                     2 * mod.LOG_LINEAR, 1e-12))
    # the number the repository withdrew
    out.append(Check('Spectre linear inflation',
                     'far from the withdrawn 2.5348 (distance, not error)',
                     float(abs(ell - mod.WRONG_LAM) > 0.25), 1.0, 0.0))
    return out


def matrix_comparison():
    """The two repositories' substitution matrices, species by species.

    Returns None if either is missing, else a dict.  Both transcribe the same
    published rules, so agreement is a check on transcription.
    """
    mod = load()
    if mod is None:
        return None
    try:
        import rosettaspectre
    except Exception:
        return None
    ns = rosettaspectre.load()
    if ns is None:
        return None
    import numpy as np
    chirality = ns[0]
    names_equal = tuple(mod.SPECIES) == tuple(chirality.TILE_NAMES)
    perm = [list(chirality.TILE_NAMES).index(s) for s in mod.SPECIES]
    theirs = chirality.substitution_matrix()[np.ix_(perm, perm)]
    differing = [k for k in mod.RULES
                 if sorted(map(str, mod.RULES[k]))
                 != sorted(map(str, chirality.SUBS[k]))]
    import sympy as sp
    x = sp.symbols('x')
    ours_poly = sp.factor(sp.Matrix(mod.M.astype(int).tolist())
                          .charpoly(x).as_expr())
    theirs_poly = sp.factor(sp.Matrix(theirs.astype(int).tolist())
                            .charpoly(x).as_expr())
    return {'same_species_order': names_equal,
            'same_matrix': bool(np.array_equal(mod.M, theirs)),
            'rules_differing': differing,
            'charpoly': ours_poly, 'same_charpoly': ours_poly == theirs_poly,
            'column_sums': [int(v) for v in mod.M.sum(axis=0)],
            'perron': (float(mod.PERRON),
                       float(max(np.linalg.eigvals(theirs).real)))}


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
    print('rosettanariai: the nariai repository, as seen from RosettaPhys')
    print('  %s' % P.cite_text(REFERENCE))
    print('  %d entries cite it' % len(ours()))
    root = locate()
    print('  nariai found at %s' % (root or 'nowhere (set NARIAI_DIR)'))
    if root and not available():
        print('  but it did not import: %s' % _CACHE.get('error'))
    print()
    for c in _check_closed_forms() + checks():
        print('  %-4s %-30s %s' % ('ok' if c.ok else 'FAIL', c.equation, c.what))
    cmp_ = matrix_comparison()
    print()
    if cmp_ is None:
        print('  matrix comparison with spectre: not available')
    else:
        print('  substitution matrix against the spectre repository\'s:')
        print('    same species order      %s' % cmp_['same_species_order'])
        print('    same 9x9 matrix         %s' % cmp_['same_matrix'])
        print('    rules that differ       %s' % (cmp_['rules_differing'] or 'none'))
        print('    same characteristic polynomial  %s' % cmp_['same_charpoly'])
        print('      %s' % cmp_['charpoly'])
        print('    column sums             %s' % cmp_['column_sums'])
        print('    (both transcribe the published rules: agreement checks the '
              'transcription, not a second derivation)')
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
    check('the nariai repository is a reference', REFERENCE in P.REFERENCES)
    check('five entries cite it', len(cited) == 5)
    check('all five are in the tilings group',
          all(e['field'] == 'Tilings' for e in cited))
    check('each names nariai_constants',
          all('brentharts/nariai: nariai_constants.py' in e['source']
              for e in cited))
    check('every entry is read by the algebra', not unchecked())
    check('the reference note mentions the withdrawn factor',
          '2.5348' in P.REFERENCES[REFERENCE]['note'])
    check('the growth-rate entry says it is not an entropy',
          'not an entropy' in _entry('Spectre growth rate')['blurb'])
    check('the area relation joins the spectre factor on mu',
          (P.join('Spectre linear-area relation', 'Spectre inflation factor')
           or type('x', (), {'pivot': None})).pivot == 'mu')
    check('the growth rate joins the area relation on mu',
          (P.join('Spectre growth rate', 'Spectre linear-area relation')
           or type('x', (), {'pivot': None})).pivot == 'mu')
    check('a gap label never joins a tile count',
          P.join('Spectre gap-label recurrence', 'Spectre count recurrence')
          is None)
    for c in _check_closed_forms():
        check('%s: %s' % (c.equation, c.what), c.ok)
    print()
    if not available():
        print('the nariai repository')
        print('  skipped: not importable (NARIAI_DIR; needs numpy)')
        print()
        print('rosettanariai: library side only, %d failure(s).' % len(failures))
        return len(failures)
    print('the nariai repository')
    results = checks()
    for c in results:
        check('%s: %s' % (c.equation, c.what), c.ok)
    print()
    cmp_ = matrix_comparison()
    print('against the spectre repository')
    if cmp_ is None:
        print('  skipped: the spectre repository is not importable')
    else:
        check('same species, same order', cmp_['same_species_order'])
        check('identical 9x9 substitution matrix', cmp_['same_matrix'])
        check('no metatile rule differs', not cmp_['rules_differing'])
        check('same characteristic polynomial', cmp_['same_charpoly'])
        check('column sums are 7 for Gamma and 8 for the rest',
              cmp_['column_sums'] == [7] + [8] * 8)
        check('both give the Perron eigenvalue 4 + sqrt(15)',
              all(abs(v - MU) < 1e-9 for v in cmp_['perron']))
    print()
    if failures:
        print('%d failure(s): %s' % (len(failures), '; '.join(failures)))
    else:
        print('rosettanariai: %d checks against the repository, all agree.'
              % len(results))
    return len(failures)


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    _report()
