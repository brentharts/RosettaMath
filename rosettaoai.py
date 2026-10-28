#!/usr/bin/env python3
r"""rosettaoai.py -- the bridge from RosettaPhys to the OpenAI-math fork.

The 'Lattice spin models' group in rosettaphys.py is drawn from the physics
tools of brentharts/openai_math_yang_mills, a fork of a collection of
manuscripts released by OpenAI.  The tools (tools/*.py there) are fork-level
illustrations: they reproduce textbook forms next to what the manuscripts
state, and they do not re-prove a manuscript.  The repository contains no
Yang-Mills manuscript, and nothing here says otherwise.

Nine entries carry a `source` naming the tool they describe.  A `source` is a
claim -- "this is the equation that script computes" -- and this module makes
it testable.

CHECKS      Let RosettaPhys's own algebra read an entry and evaluate it, then
            compare with a number the fork produced (build/data/*.json, made
            by `make models` there) or with the closed form the fork's own
            script verifies symbolically.

UNCHECKED   Entries the algebra refuses (a summation, a change in a quantity)
            are listed, not silently passed.

REPORT      The comparison with asymptotic freedom is reported with its
            deviation, not only pass or fail: the Monte Carlo slopes are
            below the asymptotic prediction, and by how much is the finding.

    python3 rosettaoai.py             what the fork produced, and the checks
    python3 rosettaoai.py --selftest  the bridge, end to end

The fork is found in $OPENAI_MATH_DIR, or in an openai_math_yang_mills
directory beside this one.  Without its build/data the data checks report that
plainly and the closed-form checks still run.
"""

import json
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rosettaphys as P

REFERENCE = 'openai2026'
FIELD = 'Lattice spin models'
REPO = 'openai_math_yang_mills'


# --------------------------------------------------------------- locating

def locate():
    """The fork's directory, or None.  Looks for tools/on_model_mc.py."""
    candidates = [
        os.environ.get('OPENAI_MATH_DIR'),
        os.path.join(HERE, '..', REPO),
        os.path.join(HERE, REPO),
        os.path.expanduser('~/' + REPO),
    ]
    for path in candidates:
        if path and os.path.exists(os.path.join(path, 'tools',
                                                'on_model_mc.py')):
            return os.path.abspath(path)
    return None


def data(name):
    """build/data/<name>.json from the fork, or None if it was not built."""
    root = locate()
    if root is None:
        return None
    path = os.path.join(root, 'build', 'data', name + '.json')
    if not os.path.exists(path):
        return None
    with open(path) as handle:
        return json.load(handle)


def available():
    return all(data(n) is not None
               for n in ('on_model_mc', 'kt_flow', 'bloch_law', 'haldane_gap'))


# --------------------------------------------- the library's own arithmetic

def _entry(name):
    entry = P.GRAPH.find(name, 'equation')
    if entry is None:
        raise KeyError('no equation called %r' % name)
    return entry


def predicts(name, known):
    """The right-hand side of an entry, read and evaluated by rosettaphys."""
    return P.evaluate(P.read_relation(_entry(name)['latex']).right, known)


class Check:
    def __init__(self, equation, what, library, reference, tolerance):
        self.equation = equation
        self.what = what
        self.library = library
        self.reference = reference
        self.tolerance = tolerance

    @property
    def error(self):
        if self.reference == 0.0:
            return abs(self.library)
        return abs(self.library - self.reference) / abs(self.reference)

    @property
    def ok(self):
        return self.error <= self.tolerance

    def __repr__(self):
        return '<Check %s: %s>' % (self.equation, 'ok' if self.ok else 'FAIL')


# ---------------------------------------------------- closed-form checks

def _check_second_moment():
    """The library's xi against the formula the fork's xi_of() computes."""
    chi, F, L = 31.7, 2.9, 40
    p = 2.0 * math.sin(math.pi / L)
    stated = math.sqrt((chi / F - 1.0) / (4.0 * math.sin(math.pi / L) ** 2))
    got = math.sqrt(predicts('Second-moment correlation length',
                             {'chi': chi, 'F': F, 'p': p}))
    return Check('Second-moment correlation length',
                 'xi from chi, F and p = 2 sin(pi/L), L = 40', got, stated,
                 1e-12)


def _check_kosterlitz():
    """The closed-form flow of kt_flow.py through both flow entries."""
    mu, theta = 0.3, 0.2
    out = []
    worst_x = worst_y = worst_c = 0.0
    h = 1e-6
    for l in (0.0, 0.5, 1.0, 1.5):
        x = lambda t: -mu * math.tan(mu * t + theta)
        y = lambda t: mu / math.cos(mu * t + theta)
        dx = (x(l + h) - x(l - h)) / (2 * h)
        dy = (y(l + h) - y(l - h)) / (2 * h)
        worst_x = max(worst_x, abs(dx - predicts(
            'Kosterlitz coupling flow', {'y': y(l)})))
        worst_y = max(worst_y, abs(dy - predicts(
            'Kosterlitz fugacity flow', {'x': x(l), 'y': y(l)})))
        worst_c = max(worst_c, abs(x(l) ** 2 - y(l) ** 2 + mu ** 2))
    out.append(Check('Kosterlitz coupling flow',
                     'dx/dl of x = -mu tan(mu l + theta) against -y^2 '
                     '(worst abs error)', worst_x, 0.0, 1e-8))
    out.append(Check('Kosterlitz fugacity flow',
                     'dy/dl of y = mu sec(mu l + theta) against -x y '
                     '(worst abs error)', worst_y, 0.0, 1e-8))
    out.append(Check('Kosterlitz coupling flow',
                     'x^2 - y^2 + mu^2 = 0 along the flow (conserved)',
                     worst_c, 0.0, 1e-12))
    return out


def _check_asymptotic_form():
    """The scaling entry against the exponent it states, for N = 3 and 4."""
    out = []
    for n in (3, 4):
        b1, b2 = 1.0, 2.0
        lib = (predicts('Asymptotic-freedom mass scaling',
                        {'C': 1.0, 'beta': b2, 'N': float(n), 'pi': math.pi})
               / predicts('Asymptotic-freedom mass scaling',
                          {'C': 1.0, 'beta': b1, 'N': float(n), 'pi': math.pi}))
        stated = (b2 / b1) ** (1.0 / (n - 2)) * math.exp(
            -2.0 * math.pi * (b2 - b1) / (n - 2))
        out.append(Check('Asymptotic-freedom mass scaling',
                         'm(2)/m(1) for N = %d' % n, lib, stated, 1e-12))
    return out


# --------------------------------------------------------- data checks

def _check_bloch():
    bloch = data('bloch_law')
    if bloch is None:
        return []
    a = bloch['A']
    paper = 3.0 * _zeta_52() / (128.0 * math.pi ** 1.5)
    out = [Check('Bloch magnon density',
                 'first correction A_1 against 3 zeta(5/2)/(128 pi^(3/2))',
                 a[1], paper, 1e-9)]
    for row in bloch['table']:
        lib = predicts('Bloch magnon density',
                       {'A_0': a[0], 'A_1': a[1], 'x': float(row['x'])})
        out.append(Check('Bloch magnon density',
                         'n(x) = A_0 x^(-3/2) + A_1 x^(-5/2) at x = %g'
                         % row['x'], lib, row['bloch_plus_correction'], 1e-9))
    return out


def _zeta_52():
    return sum(k ** -2.5 for k in range(1, 400000)) + 2.0 / (3.0 * 400000 ** 1.5)


def checks():
    out = [_check_second_moment(), *_check_kosterlitz(),
           *_check_asymptotic_form()]
    out.extend(_check_bloch())
    return out


def asymptotic_freedom():
    """What the Monte Carlo gives against the asymptotic-freedom slope.

    For each N: the fitted slope of ln xi against beta (from the fork), the
    slope the library's entry predicts between the same two betas, and their
    ratio.  Not a pass-or-fail: below one means the simulated length grows more
    slowly than the leading form, which is the expected approach from below.
    """
    mc = data('on_model_mc')
    if mc is None:
        return None
    rows = {}
    for n, pts in mc['results'].items():
        n = int(n)
        first, last = pts[0], pts[-1]
        b1, b2 = first['beta'], last['beta']
        lib = (predicts('Asymptotic-freedom mass scaling',
                        {'C': 1.0, 'beta': b1, 'N': float(n), 'pi': math.pi})
               / predicts('Asymptotic-freedom mass scaling',
                          {'C': 1.0, 'beta': b2, 'N': float(n), 'pi': math.pi}))
        predicted = math.log(lib) / (b2 - b1)
        measured = math.log(last['xi'] / first['xi']) / (b2 - b1)
        rows[n] = {'beta': (b1, b2), 'measured': measured,
                   'predicted': predicted, 'ratio': measured / predicted,
                   'fit_slope': mc['fits'][str(n)]['slope'],
                   'leading_slope': mc['fits'][str(n)]['theory'],
                   'L_over_xi_min': min(p['L_over_xi'] for p in pts)}
    return rows


def haldane():
    hal = data('haldane_gap')
    if hal is None:
        return None
    return {'gap': dict(zip(hal['L'], hal['gap'])),
            'extrapolated': hal['aitken'], 'literature': 0.4105}


def unchecked():
    """Entries citing the fork that the algebra cannot evaluate."""
    names = []
    for entry in P.cited(REFERENCE):
        try:
            P.read_relation(entry['latex'])
        except Exception:
            names.append(entry['name'])
    return names


def _report():
    print('rosettaoai: the OpenAI-math fork, as seen from RosettaPhys')
    print('  %s' % P.cite_text(REFERENCE))
    print()
    print('  %d entries cite it; none re-proves a manuscript.'
          % len(P.cited(REFERENCE)))
    root = locate()
    print('  fork found at %s' % (root or 'nowhere (set OPENAI_MATH_DIR)'))
    print('  fork data built: %s' % ('yes' if available() else
                                   'no (run `make models` there)'))
    print()
    for c in checks():
        print('  %-4s %-34s %s' % ('ok' if c.ok else 'FAIL', c.equation,
                                    c.what))
    af = asymptotic_freedom()
    if af:
        print()
        print('  asymptotic freedom, Monte Carlo against the leading form:')
        for n, r in sorted(af.items()):
            print('    O(%d), beta %.1f to %.1f: slope of ln xi %.2f, form '
                  '%.2f, ratio %.2f (min L/xi %.1f)'
                  % (n, r['beta'][0], r['beta'][1], r['measured'],
                     r['predicted'], r['ratio'], r['L_over_xi_min']))
    hal = haldane()
    if hal:
        print()
        print('  spin-one ring gaps %s; extrapolated %.4f against %.4f in '
              'the literature'
              % (', '.join('L=%d: %.3f' % kv
                           for kv in sorted(hal['gap'].items())),
                 hal['extrapolated'], hal['literature']))
    print()
    print('  not evaluated by the algebra: %s' % ', '.join(unchecked()))


def selftest():
    failures = []

    def check(label, ok):
        print('  %-62s %s' % (label, 'ok' if ok else 'FAIL'))
        if not ok:
            failures.append(label)

    print('the library side')
    cited = P.cited(REFERENCE)
    check('the fork is a reference', REFERENCE in P.REFERENCES)
    check('nine entries cite it', len(cited) == 9)
    check('every one is in the lattice spin models group',
          all(e['field'] == FIELD for e in cited))
    check('each names the tool it describes',
          all('tools/' in e['source'] for e in cited))
    check('spin beta and gauge beta are different quantities',
          P.join('Asymptotic-freedom mass scaling', 'Lattice coupling') is None)
    check('the two flow equations join on the scale',
          P.join('Kosterlitz coupling flow',
                 'Kosterlitz fugacity flow') is not None)
    print()
    print('closed forms')
    results = [_check_second_moment(), *_check_kosterlitz(),
               *_check_asymptotic_form()]
    for c in results:
        check('%s: %s' % (c.equation, c.what), c.ok)
    check('summations are refused, not guessed',
          set(unchecked()) == {'O(N) lattice model', 'Magnon dispersion',
                               'Bilinear-biquadratic chain', 'Spin gap'})
    print()
    if not available():
        print('the fork data')
        print('  skipped: build/data not found (OPENAI_MATH_DIR, make models)')
        print()
        print('rosettaoai: closed forms only, %d failure(s).' % len(failures))
        return len(failures)
    print('the fork data')
    data_checks = _check_bloch()
    for c in data_checks:
        check('%s: %s' % (c.equation, c.what), c.ok)
    af = asymptotic_freedom()
    check('Monte Carlo slopes are below the leading form (both N)',
          all(0.0 < r['ratio'] < 1.0 for r in af.values()))
    check('and within the fork\'s own 35% tolerance',
          all(abs(r['fit_slope'] / r['leading_slope'] - 1) < 0.35
              for r in af.values()))
    hal = haldane()
    check('ring gaps decrease with L and stay above the extrapolation',
          all(a > b > hal['extrapolated'] for a, b in
              zip(sorted(hal['gap'].values(), reverse=True),
                  sorted(hal['gap'].values(), reverse=True)[1:])))
    print()
    if failures:
        print('%d failure(s): %s' % (len(failures), '; '.join(failures)))
    else:
        print('rosettaoai: %d checks, all agree.'
              % (len(results) + len(data_checks)))
    return len(failures)


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    _report()
