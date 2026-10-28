#!/usr/bin/env python3
r"""rosettaym.py -- the bridge from RosettaPhys to the Yang-Mills laboratory.

The 'Lattice gauge theory' group in rosettaphys.py is drawn from Michael
Elsbernd's yang-mills-mass-gap-lab (the Python package `ymlab`).  Eleven of
its entries carry a `source` naming the ymlab function they describe.  A
`source` is a claim -- "this equation is what that function computes" -- and
this module is what makes the claim testable instead of decorative.

It does three things, and keeps them apart.

CHECKS      Take an equation from the library, let RosettaPhys's own algebra
            (read_relation, solve, evaluate) work out what it predicts for
            some numbers, and put the same numbers through the ymlab function.
            If they differ the entry is wrong or the code is, and either way
            somebody should be told.  The checks that use published data read
            the committed campaign; the ones that run code are small and fast.

PUBLISHED   Read the committed overrelaxation campaign out of ymlab's
            results/ directory: the summary table, the configuration, and the
            provenance of the run it came from.  Nothing is transcribed.  When
            two runs of the same configuration are on disk, say which one was
            used and why.

REPRODUCE   Optional and slow: thermalise one starting configuration and run
            two schedules again here, then say what reproduced and what did
            not.  Autocorrelation times are deterministic given the seed;
            effective samples per second are not, because the runtime is a
            property of the machine.  The comparison says that in numbers.

Nothing here claims anything about the Yang-Mills mass-gap problem.  The
laboratory is a finite-lattice study and says so; so does this.

    python3 rosettaym.py               what was found, and the checks
    python3 rosettaym.py --selftest    the bridge, end to end
    python3 rosettaym.py --reproduce   rerun one chain pair here (about 15 s)

ymlab is found in $YMLAB_DIR, or in a yang-mills-mass-gap-lab directory beside
this one.  Without it everything here reports that plainly and does nothing.
"""

import csv
import glob
import json
import math
import os
import sys
import types

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import rosettaphys as P

REFERENCE = 'elsbernd2026'
CAMPAIGN_PREFIX = 'final-overrelaxation-efficiency-campaign-'
FIELD = 'Lattice gauge theory'


# --------------------------------------------------------------- locating

def locate():
    """Where ymlab lives, or None.  Looks for src/ymlab, not for a name."""
    candidates = [
        os.environ.get('YMLAB_DIR'),
        os.path.join(HERE, '..', 'yang-mills-mass-gap-lab'),
        os.path.join(HERE, 'yang-mills-mass-gap-lab'),
        os.path.expanduser('~/yang-mills-mass-gap-lab'),
    ]
    for path in candidates:
        if path and os.path.exists(os.path.join(path, 'src', 'ymlab',
                                                '__init__.py')):
            return os.path.abspath(path)
    return None


_MODULES = {}


def load():
    """The ymlab modules this bridge uses, as a namespace, or None.

    Bytecode is not written: importing a package must not leave a
    __pycache__ inside somebody else's repository.
    """
    if 'ns' in _MODULES:
        return _MODULES['ns']
    root = locate()
    if root is None:
        _MODULES['ns'] = None
        return None
    sys.dont_write_bytecode = True
    src = os.path.join(root, 'src')
    if src not in sys.path:
        sys.path.insert(0, src)
    import importlib
    ns = types.SimpleNamespace(root=root)
    for name in ('diagnostics', 'creutz', 'mass_gap', 'lattice', 'plaquette',
                 'wilson_action', 'gauge_transformations',
                 'research_campaign'):
        setattr(ns, name, importlib.import_module('ymlab.' + name))
    _MODULES['ns'] = ns
    return ns


def available():
    return load() is not None


# --------------------------------------------- the library's own arithmetic

def _entry(name):
    entry = P.GRAPH.find(name, 'equation')
    if entry is None:
        raise KeyError('no equation called %r' % name)
    return entry


def predicts(name, known):
    """What an equation of the form  x = <expression>  says x is.

    The right-hand side is read and evaluated by rosettaphys, so a misprint in
    the library's LaTeX shows up here as a wrong number and not as a pass.
    """
    return P.evaluate(P.read_relation(_entry(name)['latex']).right, known)


def solved(name, quantity, known):
    """What an equation says `quantity` is, after rosettaphys rearranges it."""
    found = P.solve(_entry(name), quantity)
    if found is None:
        raise ValueError('%s cannot be solved for %s' % (name, quantity))
    return P.evaluate(found.term, known)


# -------------------------------------------------------------- published

def _number(text):
    try:
        return float(text)
    except ValueError:
        return text


def _rows(path):
    with open(path, newline='') as handle:
        return [{k: _number(v) for k, v in row.items()}
                for row in csv.DictReader(handle)]


def published_runs():
    """Every complete committed campaign run, newest first."""
    ns = load()
    if ns is None:
        return []
    out = []
    pattern = os.path.join(ns.root, 'results', 'runs', CAMPAIGN_PREFIX + '*')
    for path in glob.glob(pattern):
        try:
            with open(os.path.join(path, 'manifest.json')) as handle:
                manifest = json.load(handle)
            summary = _rows(os.path.join(path, 'campaign_summary.csv'))
            records = _rows(os.path.join(path, 'campaign_records.csv'))
        except (OSError, ValueError):
            continue
        if manifest.get('status') != 'completed':
            continue
        out.append({
            'name': os.path.basename(path),
            'created': manifest.get('created_at_utc', ''),
            'config': manifest.get('configuration', {}),
            'config_hash': manifest.get('configuration_hash', ''),
            'environment': manifest.get('environment', {}),
            'git': manifest.get('git', {}),
            'runtime': manifest.get('runtime_seconds'),
            'summary': summary,
            'records': records,
        })
    out.sort(key=lambda run: run['created'], reverse=True)
    return out


def published_campaign():
    """The run the paper quotes, or None.

    A run made from a clean checkout is preferred to one made from a dirty
    tree, because a dirty tree means the code that produced the numbers is not
    the code at the commit the manifest names.  Among clean runs the newest
    wins.  Two runs of one configuration are on disk in the laboratory, and
    the one from the uncommitted tree gives a different headline ratio; which
    is why this rule exists.
    """
    runs = published_runs()
    if not runs:
        return None
    clean = [r for r in runs if not r['git'].get('dirty', True)]
    return (clean or runs)[0]


def determinism(runs=None):
    """How much two runs of one configuration agree, and about what.

    Autocorrelation times come from the Markov chain and the seed, so they
    should be identical.  Effective samples per second divide by a measured
    runtime, so they should not be.  This reports both, so the sentence in the
    paper that says so is a measurement.
    """
    runs = runs if runs is not None else published_runs()
    groups = {}
    for run in runs:
        groups.setdefault(run['config_hash'], []).append(run)
    pairs = [g for g in groups.values() if len(g) >= 2]
    if not pairs:
        return None
    group = pairs[0]
    base = group[0]
    key = lambda r: (r['beta'], r['seed'], r['overrelaxation_sweeps'])
    tau = ess = 0.0
    for other in group[1:]:
        theirs = {key(r): r for r in other['records']}
        for r in base['records']:
            t = theirs[key(r)]
            for field in ('plaquette_tau_int', 'scalar_tau_int'):
                tau = max(tau, abs(r[field] - t[field]))
            for field in ('plaquette_ess_per_second',
                          'scalar_ess_per_second'):
                ess = max(ess, abs(r[field] - t[field]) / r[field])
    return {'runs': len(group), 'chains': len(base['records']),
            'max_tau_difference': tau, 'max_ess_per_second_relative': ess,
            'config_hash': base['config_hash']}


def headline(run=None):
    """The measured table, keyed by (beta, schedule label)."""
    run = run or published_campaign()
    if run is None:
        return None
    return {(row['beta'], row['schedule_label']): row
            for row in run['summary']}


def best_schedules(run=None):
    """For each beta, the schedule with the highest mean ESS/s, per observable.

    Recomputed from the table rather than read from the laboratory's own
    conclusion file, so the paper's sentence about which schedule won is a
    function of the numbers it prints next to it.
    """
    run = run or published_campaign()
    if run is None:
        return None
    out = {}
    for beta in sorted({row['beta'] for row in run['summary']}):
        rows = [r for r in run['summary'] if r['beta'] == beta]
        out[beta] = {
            'plaquette': max(rows, key=lambda r: r['mean_plaquette_ess_per_second']),
            'scalar': max(rows, key=lambda r: r['mean_scalar_ess_per_second']),
        }
    return out


def aggregation(beta=2.5, schedule='M+1OR', kind='scalar', run=None):
    """One headline cell, aggregated two ways.

    The laboratory's paired ratio is the mean over seeds of per-seed ratios,
    each taken against the Metropolis chain from the same starting
    configuration.  The other obvious summary divides the schedule's mean
    efficiency by Metropolis's mean efficiency.  Both are defensible and they
    answer slightly different questions; they are not the same number, and a
    reader quoting one should know the other.  Nothing here says which is
    right.
    """
    run = run or published_campaign()
    if run is None:
        return None
    rows = {r['schedule_label']: r for r in run['summary'] if r['beta'] == beta}
    if schedule not in rows or 'M' not in rows:
        return None
    paired = rows[schedule]['mean_%s_efficiency_ratio_vs_metropolis' % kind]
    means = (rows[schedule]['mean_%s_ess_per_second' % kind]
             / rows['M']['mean_%s_ess_per_second' % kind])
    return {'beta': beta, 'schedule': schedule, 'observable': kind,
            'mean_of_paired_ratios': paired, 'ratio_of_mean_efficiencies': means,
            'seeds': len(run['config'].get('seeds', ()))}


# ----------------------------------------------------------------- checks

class Check:
    """One equation, one number from the library, one from the laboratory."""

    def __init__(self, equation, what, library, laboratory, tolerance):
        self.equation = equation
        self.what = what
        self.library = library
        self.laboratory = laboratory
        self.tolerance = tolerance

    @property
    def error(self):
        """Relative to the laboratory's number; absolute when that is zero,
        which is how the worst-case checks below say 'no error at all'."""
        if self.laboratory == 0.0:
            return abs(self.library)
        return abs(self.library - self.laboratory) / abs(self.laboratory)

    @property
    def ok(self):
        return self.error <= self.tolerance

    def __repr__(self):
        return '<Check %s: %s>' % (self.equation, 'ok' if self.ok else 'FAIL')


def _check_effective_sample_size(ns):
    n, tau = 180, 6.146944114310537
    return Check('Effective sample size', 'N / (2 tau), N = 180',
                 predicts('Effective sample size', {'N': n, 'tau': tau}),
                 ns.diagnostics.effective_sample_size(n, tau), 1e-12)


def _check_autocorrelation_time(ns):
    import numpy as np
    phi, cutoff = 0.6, 20
    rho = np.array([phi ** t for t in range(cutoff + 2)])
    stated = 0.5 + sum(phi ** t for t in range(1, cutoff + 1))
    return Check('Integrated autocorrelation time',
                 '1/2 + sum of rho_t, rho_t = 0.6^t, cutoff 20', stated,
                 ns.diagnostics.integrated_autocorrelation_time(
                     rho, cutoff=cutoff), 1e-12)


def _check_area_law_and_creutz(ns):
    """An exact area law, pushed through three entries and the ymlab routine."""
    sigma, width, height = 0.35, 3, 3
    area = lambda r, t: float(r * t)
    w = {}
    for tag, (r, t) in {'W_RT': (width, height),
                        'W_R1T1': (width - 1, height - 1),
                        'W_RT1': (width, height - 1),
                        'W_R1T': (width - 1, height)}.items():
        w[tag] = predicts('Area law', {'sigma': sigma, 'A': area(r, t)})
    library = predicts('Creutz ratio', w)
    laboratory = ns.creutz.creutz_ratio_from_values(
        w['W_RT'], w['W_R1T1'], w['W_RT1'], w['W_R1T'], width, height).value
    recovered = solved('Creutz string tension', 'sigma',
                       {'chi': library, 'a': 1.0})
    return [
        Check('Creutz ratio', 'four exact-area-law loops, 3 x 3', library,
              laboratory, 1e-12),
        Check('Creutz string tension',
              'chi = sigma a^2 recovers sigma = 0.35 (a = 1)', recovered,
              sigma, 1e-12),
        Check('Area law', 'sigma = -ln W / A, rearranged by rosettaphys',
              solved('Area law', 'sigma',
                     {'W': w['W_RT'], 'A': area(width, height)}),
              sigma, 1e-12),
    ]


def _check_effective_mass(ns):
    import numpy as np
    amplitude, mass = 2.0, 0.4
    c = [predicts('Euclidean correlator decay',
                  {'A_0': amplitude, 'm_L': mass, 't': float(t)})
         for t in range(10)]
    lab = ns.mass_gap.effective_mass(np.array(c)).effective_masses
    lib = [predicts('Lattice effective mass', {'C_t': c[t], 'C_t1': c[t + 1]})
           for t in range(len(lab))]
    fit = ns.mass_gap.fit_exponential_mass(np.array(c)).mass
    return [
        Check('Lattice effective mass',
              'log ratio of a pure exponential, every slice, m = 0.4',
              max(lib), max(lab), 1e-12),
        Check('Euclidean correlator decay',
              'least-squares fit of a pure exponential recovers m = 0.4',
              mass, fit, 1e-6),
    ]


def _check_wilson_action_and_gauge(ns):
    import numpy as np
    beta = 2.0
    lattice = ns.lattice.Lattice(shape=(3, 3), cold_start=False, seed=11)
    # the action written out as the library states it, from the plaquette
    # matrices, without going through ymlab's own action routine
    direct = 0.0
    for site in lattice.sites():
        for mu in range(lattice.dim):
            for nu in range(mu + 1, lattice.dim):
                u = ns.plaquette.plaquette(lattice, site, mu, nu)
                direct += 1.0 - (1.0 / 2) * float(np.real(np.trace(u)))
    direct *= beta
    action = ns.wilson_action.wilson_action(lattice, beta)
    field = ns.gauge_transformations.random_gauge_field(lattice, seed=5)
    moved = ns.gauge_transformations.gauge_transform_lattice(lattice, field)
    after = ns.wilson_action.wilson_action(moved, beta)
    return [
        Check('Wilson plaquette action',
              'beta sum (1 - Re Tr U / N), N = 2, random 3 x 3 lattice',
              direct, action, 1e-12),
        Check('Link gauge transformation',
              'the action before and after a random gauge transformation',
              after, action, 1e-9),
    ]


def _check_published(run):
    """The efficiency entries against every chain in the committed campaign."""
    n = float(run['config']['measurement_updates'])
    worst_eta = worst_ratio = 0.0
    for r in run['records']:
        for kind in ('plaquette', 'scalar'):
            ess = predicts('Effective sample size',
                           {'N': n, 'tau': r[kind + '_tau_int']})
            eta = predicts('Sampling efficiency',
                           {'N_eff': ess, 't_wall': r['runtime_seconds']})
            lab = r[kind + '_ess_per_second']
            worst_eta = max(worst_eta, abs(eta - lab) / lab)
    index = {(r['beta'], r['seed'], r['overrelaxation_sweeps']): r
             for r in run['records']}
    seeds = sorted({k[1] for k in index})
    for row in run['summary']:
        if row['overrelaxation_sweeps'] == 0:
            continue
        for kind in ('plaquette', 'scalar'):
            ratios = []
            for seed in seeds:
                hybrid = index[(row['beta'], seed, row['overrelaxation_sweeps'])]
                base = index[(row['beta'], seed, 0)]
                ratios.append(predicts('Efficiency ratio', {
                    'eta_OR': hybrid[kind + '_ess_per_second'],
                    'eta_M': base[kind + '_ess_per_second']}))
            mean = sum(ratios) / len(ratios)
            lab = row['mean_%s_efficiency_ratio_vs_metropolis' % kind]
            worst_ratio = max(worst_ratio, abs(mean - lab) / lab)
    count = len(run['records'])
    return [
        Check('Sampling efficiency',
              'N_eff / t_wall against all %d published chains, both '
              'observables (worst case)' % count, worst_eta, 0.0, 1e-9),
        Check('Efficiency ratio',
              'paired eta ratios, averaged over seeds, against every '
              'published mean ratio (worst case)', worst_ratio, 0.0, 1e-9),
    ]


def checks():
    """Every check there is, or [] when ymlab is not here to be checked."""
    ns = load()
    if ns is None:
        return []
    out = [_check_effective_sample_size(ns), _check_autocorrelation_time(ns)]
    out += _check_area_law_and_creutz(ns)
    out += _check_effective_mass(ns)
    out += _check_wilson_action_and_gauge(ns)
    run = published_campaign()
    if run is not None:
        out += _check_published(run)
    return out


def unchecked():
    """Entries that cite ymlab and have no check here: an honest gap list."""
    covered = {c.equation for c in checks()}
    return [eq['name'] for eq in P.cited(REFERENCE)
            if eq['name'] not in covered]


# -------------------------------------------------------------- reproduce

def reproduce(beta=2.5, seed=2026, schedules=(0, 1)):
    """Run chains again, here, and compare them with the published ones.

    Thermalises one starting configuration and runs each schedule from a copy,
    exactly as the campaign does, then compares with the published records for
    the same beta, seed and schedule.
    """
    ns = load()
    run = published_campaign()
    if ns is None or run is None:
        return None
    cfg = run['config']
    rc = ns.research_campaign
    start = rc.thermalize_starting_configuration(
        shape=tuple(cfg['shape']), beta=beta, epsilon=cfg['epsilon'],
        thermalization_sweeps=cfg['thermalization_sweeps'], seed=seed)
    rows = []
    for schedule in schedules:
        mine = rc.run_schedule_chain(
            starting_lattice=start, beta=beta, epsilon=cfg['epsilon'],
            overrelaxation_sweeps=schedule,
            measurement_updates=cfg['measurement_updates'],
            time_direction=cfg['time_direction'], seed=seed)
        theirs = next(r for r in run['records']
                      if r['beta'] == beta and r['seed'] == seed
                      and r['overrelaxation_sweeps'] == schedule)
        rows.append({
            'schedule': mine.schedule_label,
            'plaquette_tau_here': mine.plaquette_tau_int,
            'plaquette_tau_published': theirs['plaquette_tau_int'],
            'scalar_tau_here': mine.scalar_tau_int,
            'scalar_tau_published': theirs['scalar_tau_int'],
            'ess_per_second_here': mine.scalar_ess_per_second,
            'ess_per_second_published': theirs['scalar_ess_per_second'],
            'runtime_here': mine.runtime_seconds,
            'runtime_published': theirs['runtime_seconds'],
        })
    return {'beta': beta, 'seed': seed, 'rows': rows,
            'published_on': run['environment']}


# ----------------------------------------------------------------- report

def _fmt(x):
    return '%.6g' % x


def _report():
    root = locate()
    print(__doc__.strip().split('\n')[0])
    print()
    if root is None:
        print('  ymlab not found.  Set YMLAB_DIR, or put '
              'yang-mills-mass-gap-lab beside this directory.')
        return
    print('  ymlab at   %s' % root)
    print('  reference  %s' % P.cite_text(REFERENCE))
    print('  entries    %d citing it, filed under %r'
          % (len(P.cited(REFERENCE)), FIELD))
    run = published_campaign()
    if run is not None:
        env = run['environment']
        print()
        print('  published campaign   %s' % run['name'])
        print('    made on %s %s, python %s, numpy %s; tree %s'
              % (env.get('platform_system', '?'),
                 env.get('platform_machine', '?'),
                 env.get('python_version', '?'), env.get('numpy_version', '?'),
                 'dirty' if run['git'].get('dirty') else 'clean'))
        print('    %s   beta %s   seeds %s   %s measured updates'
              % ('x'.join(str(e) for e in run['config']['shape']),
                 run['config']['betas'], run['config']['seeds'],
                 run['config']['measurement_updates']))
        print()
        print('    beta  best plaquette   best scalar      scalar ratio vs M')
        for beta, best in best_schedules(run).items():
            print('    %-5s %-15s %-16s %s' % (
                beta, best['plaquette']['schedule_label'],
                best['scalar']['schedule_label'],
                _fmt(best['scalar']['mean_scalar_efficiency_ratio_vs_metropolis'])))
        same = determinism()
        if same:
            print()
            print('    %d runs of this configuration are on disk: largest '
                  'difference in tau_int %s, in ESS/s %.1f%%'
                  % (same['runs'], _fmt(same['max_tau_difference']),
                     100 * same['max_ess_per_second_relative']))
    print()
    print('  checks (library prediction vs laboratory):')
    results = checks()
    for c in results:
        print('    %-4s %-32s %s' % ('ok' if c.ok else 'FAIL', c.equation,
                                      c.what))
    gap = unchecked()
    print()
    print('  %d of %d citing entries checked here%s'
          % (len(P.cited(REFERENCE)) - len(gap), len(P.cited(REFERENCE)),
             '; not checked: ' + ', '.join(gap) if gap else ''))


def selftest():
    failures = []

    def check(label, ok):
        print('  %-62s %s' % (label, 'ok' if ok else 'FAIL'))
        if not ok:
            failures.append(label)

    print('the library side')
    cited = P.cited(REFERENCE)
    check('the laboratory is a reference', REFERENCE in P.REFERENCES)
    check('eleven entries cite it', len(cited) == 11)
    check('every one is in the lattice gauge theory group',
          all(e['field'] == FIELD for e in cited))
    check('predicts() reads a statement and evaluates it',
          abs(predicts('Effective sample size', {'N': 10, 'tau': 1}) - 5) < 1e-12)
    check('solved() rearranges before it evaluates',
          abs(solved('Area law', 'sigma', {'W': math.exp(-6), 'A': 2}) - 3)
          < 1e-12)
    print()
    if not available():
        print('the laboratory side')
        print('  skipped: ymlab was not found (set YMLAB_DIR)')
        print()
        print('rosettaym: library side only, %d failure(s).' % len(failures))
        return len(failures)

    print('the laboratory side')
    results = checks()
    for c in results:
        check('%s: %s' % (c.equation, c.what), c.ok)
    check('the published campaign is found', published_campaign() is not None)
    run = published_campaign()
    check('it is a clean run, not the dirty one',
          run is not None and not run['git'].get('dirty', True))
    table = best_schedules(run) if run else {}
    check('plaquette: Metropolis wins at every beta',
          bool(table) and all(b['plaquette']['schedule_label'] == 'M'
                              for b in table.values()))
    check('scalar: Metropolis wins at the two smaller betas, one OR sweep at '
          'the largest',
          bool(table) and [b['scalar']['schedule_label']
                           for _, b in sorted(table.items())]
          == ['M', 'M', 'M+1OR'])
    same = determinism()
    check('tau_int is identical across runs of one configuration',
          same is None or same['max_tau_difference'] == 0.0)
    check('ESS per second is not: the runtime belongs to the machine',
          same is None or same['max_ess_per_second_relative'] > 0.0)
    cell = aggregation(run=run)
    check('the headline cell is aggregated two ways, and they differ',
          cell is not None and cell['mean_of_paired_ratios']
          != cell['ratio_of_mean_efficiencies'])
    check('the headline paired ratio is the published 1.250488',
          cell is not None
          and abs(cell['mean_of_paired_ratios'] - 1.250488) < 5e-7)
    check('every entry citing the laboratory is checked or listed as not',
          len(unchecked()) == len(set(unchecked())))
    print()
    if failures:
        print('%d failure(s): %s' % (len(failures), '; '.join(failures)))
    else:
        print('rosettaym: %d checks against ymlab, all agree.' % len(results))
    return len(failures)


def _reproduction_report():
    got = reproduce()
    if got is None:
        print('ymlab or its published campaign was not found.')
        return 1
    env = got['published_on']
    print('beta %s, seed %s; published on %s %s, numpy %s'
          % (got['beta'], got['seed'], env.get('platform_system', '?'),
             env.get('platform_machine', '?'), env.get('numpy_version', '?')))
    print('here: numpy %s on %s'
          % (__import__('numpy').__version__, sys.platform))
    print()
    print('%-7s %-22s %-22s %s' % ('', 'tau_int here', 'published', 'scalar ESS/s here / published'))
    for r in got['rows']:
        print('%-7s %-22s %-22s %s / %s' % (
            r['schedule'], r['scalar_tau_here'], r['scalar_tau_published'],
            _fmt(r['ess_per_second_here']), _fmt(r['ess_per_second_published'])))
    return 0


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    if '--reproduce' in sys.argv:
        sys.exit(_reproduction_report())
    _report()
