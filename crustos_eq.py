#!/usr/bin/env python3
r"""crustos_eq.py -- one equation, four readings, all of them generated.

Equation (1) of `leanproof.tex` is the conjunction of two theorems about the
crustos model.  This script rebuilds that model from nothing but the prelude,
proves both theorems, states their conjunction as one kernel proposition, and
then writes the same proposition out four ways for `crustos_eq.tex`:

  1. as the kernel's own LaTeX, via `type2latex`, each fragment checked to
     read back as the term it came from (`latex2type(type2latex(t)) == t`);
  2. as Lean 4 source, via `leanexport`, which Lean 4 itself then checks --
     a second kernel, written by other people, in another language;
  3. as the Python the terms were compiled from, verbatim;
  4. as that Python in RosettaMath's pseudocode, via `rosettamath.py2tex`.

Nothing in the supplement's numbers is typed by hand: every count, time and
verdict is a macro in gen/facts.tex, written by the run that measured it.

    python3 crustos_eq.py            # writes gen/ and CrustOS.lean
    python3 crustos_eq.py --no-lean  # skip the second kernel
"""

import ast
import inspect
import os
import re
import shutil
import subprocess
import sys
import textwrap
import threading
import time

import lean4 as L
import hoare as H
import rosettamath as R
import leanexport as X
from lean4 import (App, Lambda, Pi, Var, latex2type, type2latex, readable,
                   type_check, definitionally_equal)
from hoare import (app, procedure, state_invariant, preserves_by_cases,
                   pass_by_cases, preserves_by_loop, compose, by_cases,
                   by_bool, unfold, discharge, progress_by_loop,
                   invariant_at_exit, prove, NAT, BYTES, STRS, PROP)

HERE = os.path.dirname(os.path.abspath(__file__))
GEN = os.path.join(HERE, 'gen')

# Python sources, kept as text as well as run, so the paper quotes exactly what
# was compiled.  `procedure` reads them back with inspect, as it always does.
SOURCES = {}


def remember(func):
    SOURCES[func.__name__] = textwrap.dedent(inspect.getsource(func))
    return func


# ----------------------------------------------------------- the model

def build():
    """The crustos model, from the prelude up, with every proof checked."""
    t0 = time.time()
    env = H.prelude()
    facts = {}

    # -- the state layer (leanproof.tex, section 7) --------------------------
    state_invariant(env, 'Context', 'c.current <= c.nthreads')

    @remember
    @procedure(env=env, preserves='Context', verbose=False,
               ensures=['result.ticks == add(c.ticks, 1)'])
    def tick(c: 'Context') -> 'Context':
        c.ticks = c.ticks + 1
        return c

    @remember
    @procedure(env=env, preserves='Context', verbose=False,
               ensures=['result.current == result.nthreads'])
    def sched(c: 'Context') -> 'Context':
        while c.current < c.nthreads:
            assert invariant(c.current <= c.nthreads)
            assert variant(c.nthreads - c.current)
            c.current = c.current + 1
            c.ticks = c.ticks + 1
        return c

    tick_pf = preserves_by_cases(env, 'Context', tick.lean_procedure,
                                 verbose=False)
    one_pass = pass_by_cases(env, 'Context', sched.lean_procedure,
                             verbose=False)
    sched_pf = preserves_by_loop(env, 'Context', sched.lean_procedure,
                                 one_pass, verbose=False)
    _, run_goal, run_pf = compose(env, 'run',
                                  [(tick.lean_procedure, tick_pf),
                                   (sched.lean_procedure, sched_pf),
                                   (tick.lean_procedure, tick_pf)])

    # termination of sched, for every context
    goals = dict(sched.lean_procedure.loop_obligations)
    entry = by_cases(env, 'Context', goals['invariant holds on entry'],
                     what='entry')
    kept = by_cases(env, 'Context', goals['invariant is preserved'],
                    what='preservation')
    down = by_cases(env, 'Context', goals['variant decreases'],
                    what='the variant',
                    using=lambda f, h, g: app('sub_lt', f['nthreads'],
                                              f['current'], h[1]))
    sched_done = progress_by_loop(env, sched.lean_procedure, entry, kept,
                                  down, verbose=False)

    # -- the routing layer (leanproof.tex, section 8) ------------------------
    @remember
    @procedure(env=env, ensures=['result <= len(names)'], verbose=False)
    def scheme_of(names: 'Strs', url: 'Bytes') -> 'Nat':
        idx = find(url, 58)                  # ord(':')
        head = take(url, idx)
        i = 0
        found = len(names)                   # stands in for SCHEME_NONE
        while i < len(names):
            assert invariant(i <= len(names))
            assert variant(len(names) - i)
            if eqs(names[i], head) and found == len(names):
                found = i
            i = i + 1
        return found

    @remember
    @procedure(env=env, verbose=False,
               ensures=['len(result) <= len(split(urls, 44))'])
    def accepted(names: 'Strs', urls: 'Bytes') -> 'Array':
        parts = split(urls, 44)
        out: 'Array' = []
        i = 0
        while i < len(parts):
            assert invariant(len(out) <= i and i <= len(parts))
            assert variant(len(parts) - i)
            if scheme_of(names, parts[i]) < len(names):
                out = snoc(out, i)
            i = i + 1
        return out

    proc = accepted.lean_procedure
    acc_goals = dict(proc.loop_obligations)
    acc_entry = discharge(acc_goals['invariant holds on entry'], env,
                          verbose=False)
    batch_len = app('len', BYTES, app('split', Var('urls'), L.numeral(44)))
    plus = lambda t: App(Var('succ'), t)
    count = lambda t: app('len', NAT, t)

    def keeps_it(f, h, claim):
        conjunction = unfold(L.spine(claim)[1][-1], env,
                             {'accepted.inv1', 'accepted.pass1'})
        first, second = L.spine(conjunction)[1]
        so_far = app('andb_left', app('leb', count(f['out']), f['i']),
                     app('leb', f['i'], batch_len), h[0])
        return app('andb_both', first, second,
                   by_bool(env, App(Var('Holds'), first), None,
                           app('snoc_le', NAT, f['out'], f['i'], f['i'],
                               so_far),
                           app('leb_trans', count(f['out']), f['i'],
                               plus(f['i']), so_far,
                               app('leb_succ', f['i']))),
                   h[1])

    acc_kept = by_cases(env, None, acc_goals['invariant is preserved'],
                        what='preservation', names=['out', 'i'],
                        using=keeps_it)
    acc_down = by_cases(env, None, acc_goals['variant decreases'],
                        what='the variant', names=['out', 'i'],
                        using=lambda f, h, g: app('sub_lt', batch_len,
                                                  f['i'], h[1]))
    acc_done = progress_by_loop(env, proc, acc_entry, acc_kept, acc_down,
                                verbose=False)
    at_exit = invariant_at_exit(env, proc, acc_entry, acc_kept)
    ending = proc.shapes[0]['result']
    final_out = app('fst', BYTES, NAT, ending)
    final_i = app('snd', BYTES, NAT, ending)
    held = app(at_exit, Var('names'), Var('urls'))
    left = app('leb', count(final_out), final_i)
    right = app('leb', final_i, batch_len)
    post = Lambda('names', STRS, Lambda('urls', BYTES, app(
        'leb_trans', count(final_out), final_i, batch_len,
        app('andb_left', left, right, held),
        app('andb_right', left, right, held))))
    acc_pf = prove(proc.obligation, post, env, verbose=False)

    # -- name every proof, so each is a declaration both kernels can see ----
    named = [
        ('tick_preserves', tick.lean_procedure.preservation, tick_pf),
        ('sched_preserves', sched.lean_procedure.preservation, sched_pf),
        ('run_preserves', run_goal, run_pf),
        ('sched_terminates', goals['progress'], sched_done),
        ('accepted_terminates', acc_goals['progress'], acc_done),
        ('accepted_bounded', proc.obligation, acc_pf),
    ]
    for name, goal, proof in named:
        L.define(env, name, goal, proof)

    # -- the equation: one proposition, the conjunction ----------------------
    # And is one more inductive family, in Prop, with one constructor; it is
    # declared here because the prelude never needed a conjunction of Props.
    L.inductive(env, 'And', [('conj', [Var('P'), Var('Q')])],
                params=[('P', PROP), ('Q', PROP)], level=0)
    statement = app('And', run_goal, proc.obligation)
    proof = app('conj', run_goal, proc.obligation,
                Var('run_preserves'), Var('accepted_bounded'))
    L.define(env, 'crustos', statement, proof)
    facts['build_seconds'] = time.time() - t0

    # the same statement with `run` unfolded, which is how (1) writes it
    unfolded = app('And', Pi('c', Var('Context'), L.arrow(
        App(Var('Holds'), App(Var('Context.invariant'), Var('c'))),
        App(Var('Holds'), App(Var('Context.invariant'),
            App(Var('tick'), App(Var('sched'), App(Var('tick'), Var('c')))))))),
        proc.obligation)
    facts['unfolded_agrees'] = definitionally_equal(statement, unfolded, env)

    return env, facts, {'tick': tick, 'sched': sched, 'accepted': accepted,
                        'scheme_of': scheme_of, 'statement': statement,
                        'unfolded': unfolded}


# ------------------------------------------------------------- writing

def write(name, text):
    path = os.path.join(GEN, name)
    with open(path, 'w') as fh:
        fh.write(text if text.endswith('\n') else text + '\n')
    return path


def macro(name, value):
    return f'\\newcommand{{\\{name}}}{{{value}}}\n'


def typeset(text):
    r"""The same string, for math mode: each space made visible.

    To the reader a space is application, so `\text{leb} x` means leb applied
    to x; to TeX in math mode a space is nothing, and it would print `lebx`.
    The only change is that each space becomes a visible, breakable one.
    """
    return text.replace(' ', '\\ \\allowbreak ')


def roundtrips(term):
    return latex2type(type2latex(term)) == term


def kernel_latex(env, facts, parts):
    r"""Every fragment of (1) as `type2latex` prints it, and the check."""
    names = ['Holds', 'Context.invariant', 'Context.current',
             'Context.nthreads', 'tick', 'run', 'sched', 'sched.loop1',
             'sched.cond1', 'sched.pass1', 'sched.rank1', 'accepted',
             'accepted.loop1', 'accepted.cond1', 'accepted.pass1',
             'accepted.inv1', 'accepted.rank1', 'split']
    checked, failed = 0, []
    for name in names:
        for kind, term in (('type', L.type_of(env, name)),
                           ('value', H.L.value_of(env, name))):
            if term is None:
                continue
            text = type2latex(term)
            ok = latex2type(text) == term
            checked += 1
            if not ok:
                failed.append(f'{kind} of {name}')
            slug = name.replace('.', '-').replace('_', '')
            write(f'kl-{slug}-{kind}.tex', text)
            write(f'kt-{slug}-{kind}.tex', typeset(text))
    for name in ('run_preserves', 'accepted_bounded', 'crustos',
                 'sched_terminates', 'accepted_terminates',
                 'tick_preserves', 'sched_preserves'):
        text = type2latex(L.type_of(env, name))
        checked += 1
        if latex2type(text) != L.type_of(env, name):
            failed.append(f'type of {name}')
        write(f'kl-{name.replace("_", "")}-type.tex', text)
        write(f'kt-{name.replace("_", "")}-type.tex', typeset(text))
    write('kl-unfolded.tex', type2latex(parts['unfolded']))
    write('kt-unfolded.tex', typeset(type2latex(parts['unfolded'])))
    checked += 1
    if not roundtrips(parts['unfolded']):
        failed.append('the unfolded statement')

    # And every type and value in the whole environment, which is the
    # claim leanproof.tex makes for its 141 terms, made again here.
    total, whole_failed = 0, []
    for name in env:
        decl = L.as_decl(name, env[name])
        for term in (decl.type, decl.value):
            if term is None:
                continue
            total += 1
            try:
                if not roundtrips(term):
                    whole_failed.append(name)
            except L.KernelError:
                whole_failed.append(name)
    facts['rt_fragments'] = checked
    facts['rt_failed'] = failed
    facts['rt_env_terms'] = total
    facts['rt_env_failed'] = sorted(set(whole_failed))
    facts['env_decls'] = len(env)
    kinds = {}
    for name in env:
        k = L.as_decl(name, env[name]).kind
        kinds[k] = kinds.get(k, 0) + 1
    facts['env_kinds'] = kinds


def lean_side(env, facts, run_lean=True):
    """Lean 4 source for the equation's closure, and Lean's verdict on it."""
    slow = H.prelude(fast=False)
    values = {n: L.value_of(slow, n) for n in H.ACCELERATED}
    checks = ['#print axioms crustos', '#print axioms sched_terminates',
              '#print axioms accepted_terminates']
    src, order = X.export(env, ['crustos', 'sched_terminates',
                                'accepted_terminates'], values, checks)
    lean_path = os.path.join(HERE, 'CrustOS.lean')
    with open(lean_path, 'w') as fh:
        fh.write(src)
    facts['lean_decls'] = len(order)
    facts['lean_lines'] = len(src.splitlines())
    facts['lean_chars'] = len(src)
    cat = X.Catalogue(env, values)
    facts['lean_accelerated'] = sorted(n for n in order if n in values)

    # quotable pieces, one per file
    for name in ('Bool', 'Nat', 'Eq', 'List', 'Prod', 'Context', 'And',
                 'Holds', 'Context.invariant', 'Context.current', 'tick',
                 'sched.cond1', 'sched.pass1', 'sched.rank1', 'sched.loop1',
                 'sched', 'run', 'leb', 'ite', 'accepted', 'len', 'snoc',
                 'accepted.loop1', 'accepted.cond1', 'accepted.pass1',
                 'accepted.inv1', 'accepted.rank1', 'Context.with_ticks'):
        write(f'lean-{name.replace(".", "-").replace("_", "")}.lean',
              X.declaration(cat, name))
    for name in ('run_preserves', 'accepted_bounded', 'crustos',
                 'tick_preserves', 'sched_terminates', 'loop_preserves',
                 'fold_terminates'):
        text = X.declaration(cat, name)
        statement, _, proof = text.partition(' :=\n')
        write(f'lean-{name.replace("_", "")}-statement.lean', statement)
        facts[f'proofchars_{name}'] = len(proof.strip())
        if len(proof) < 1200:
            write(f'lean-{name.replace("_", "")}-full.lean', text)

    facts['lean_ran'] = False
    lean = shutil.which('lean') or next(
        (p for p in (os.path.expanduser('~/lean-4.20.0-linux/bin/lean'),
                     '/home/claude/lean-4.20.0-linux/bin/lean')
         if os.path.exists(p)), None)
    if run_lean and lean:
        version = subprocess.run([lean, '--version'], capture_output=True,
                                 text=True).stdout.strip()
        # three runs, and the median: one core, and a stray process can
        # make any single timing a factor of ten out
        times = []
        for _ in range(3):
            t0 = time.time()
            res = subprocess.run([lean, '-Dlinter.unusedVariables=false',
                                  lean_path], capture_output=True, text=True)
            times.append(time.time() - t0)
        facts['lean_seconds'] = sorted(times)[1]
        facts['lean_ran'] = True
        facts['lean_version'] = re.search(r'version ([0-9.]+)',
                                          version).group(1)
        out = res.stdout + res.stderr
        errors = [l for l in out.splitlines() if 'error' in l]
        facts['lean_ok'] = res.returncode == 0 and not errors
        facts['lean_errors'] = errors[:5]
        reports = [l.strip() for l in out.splitlines() if 'axiom' in l]
        facts['lean_axioms'] = reports[0] if reports else '(no report)'
        facts['lean_axiom_free'] = sum('does not depend on any axioms' in l
                                       for l in reports)
        write('lean-output.txt', out.strip() or '(no output)')

        # not only the equation's closure: every declaration the environment
        # holds that has a definition, which is everything but `Real`
        everything = [n for n in env
                      if L.as_decl(n, env[n]).kind in ('inductive',
                                                        'definition')]
        whole, whole_order = X.export(env, everything, values)
        whole_path = os.path.join('/tmp', 'CrustOS_all.lean')
        with open(whole_path, 'w') as fh:
            fh.write(whole)
        res_all = subprocess.run([lean, '-Dlinter.unusedVariables=false',
                                  whole_path], capture_output=True, text=True)
        facts['lean_all_decls'] = len(whole_order)
        facts['lean_all_ok'] = res_all.returncode == 0 and \
            'error' not in res_all.stdout + res_all.stderr
        facts['lean_all_skipped'] = [n for n in env if n not in whole_order
                                     and L.as_decl(n, env[n]).kind
                                     not in ('constructor', 'recursor')]

        # the check is only worth something if it can fail: break one thing
        # and ask again.  `ltb` for `leb` in the state invariant makes it
        # `current < nthreads`, which the scheduler's exit state violates.
        tampered = src.replace(
            'fun (c : Context) => leb (Context.current c)',
            'fun (c : Context) => ltb (Context.current c)', 1)
        facts['tamper_applied'] = tampered != src
        bad = os.path.join('/tmp', 'CrustOS_tampered.lean')
        with open(bad, 'w') as fh:
            fh.write(tampered)
        res2 = subprocess.run([lean, '-Dlinter.unusedVariables=false', bad],
                              capture_output=True, text=True)
        lines = (res2.stdout + res2.stderr).splitlines()
        facts['tamper_refused'] = res2.returncode != 0
        errs = [i for i, l in enumerate(lines) if ': error' in l]
        facts['tamper_errors'] = len(errs)
        # which declaration each error sits in: the last one opened above it
        body = tampered.splitlines()
        where = []
        for i in errs:
            line_no = int(re.search(r':(\d+):', lines[i]).group(1))
            opened = re.findall(r'^(?:theorem|noncomputable def) (\S+)',
                                '\n'.join(body[:line_no]), re.M)
            where.append(opened[-1] if opened else '?')
        facts['tamper_where'] = where
        facts['tamper_first'] = where[0] if where else '?'
        facts['tamper_axioms'] = next(
            (l.strip() for l in lines if 'axiom' in l), '(no report)')
        excerpt = []
        if errs:
            stop = errs[1] if len(errs) > 1 else len(lines)
            excerpt = lines[errs[0]:stop]
        write('lean-tampered.txt',
              '\n'.join(textwrap.shorten(l, 110, placeholder=' ...')
                        if i == 0 else l for i, l in enumerate(excerpt))
              .replace('/tmp/', ''))
    return src


def python_side(facts):
    """The sources, raw and through py2tex, and the return journey."""
    for name in ('tick', 'sched', 'scheme_of', 'accepted'):
        src = SOURCES[name]
        # drop the bookkeeping decorator that only exists in this script
        src = '\n'.join(l for l in src.splitlines() if l.strip() != '@remember')
        write(f'py-{name.replace("_", "")}.py', src)
        warnings = []
        tex = R.py2tex(src, warnings=warnings)
        write(f'py2tex-{name.replace("_", "")}.tex', tex)
        facts[f'py2tex_warn_{name}'] = warnings
        # the return journey: py2tex, then tex2py, then compare the bodies
        back = R.tex2py(tex)
        try:
            original = ast.parse(src).body[0]
            restored = ast.parse(back).body[0]
            same = (ast.dump(ast.Module(original.body, []))
                    == ast.dump(ast.Module(restored.body, [])))
        except SyntaxError:
            same = None
        facts[f'py_roundtrip_{name}'] = same
        write(f'tex2py-{name.replace("_", "")}.py', back)
        # and would the imperative fragment still take it?
        fn = '\n'.join(l for l in back.splitlines()
                       if not l.lstrip().startswith('#'))
        try:
            H.read_procedure(fn, H.prelude(), ensures=['true'])
            facts[f'py_hoare_{name}'] = None
        except (H.ContractError, L.KernelError) as exc:
            facts[f'py_hoare_{name}'] = str(exc)


def driver_excerpt():
    """The part of this file that builds the proofs, for the appendix."""
    src = inspect.getsource(build)
    start = src.index('    proc = accepted.lean_procedure')
    end = src.index('    # -- name every proof')
    write('driver-accepted.py', textwrap.dedent(src[start:end]).rstrip())
    start = src.index('    tick_pf = ')
    end = src.index('    # termination of sched')
    write('driver-state.py', textwrap.dedent(src[start:end]).rstrip())
    start = src.index('    # -- the equation')
    end = src.index("    facts['build_seconds']")
    write('driver-equation.py', textwrap.dedent(src[start:end]).rstrip())


def facts_tex(facts):
    yes = lambda b: 'yes' if b else 'no'
    out = ['% generated by crustos_eq.py -- do not edit\n']
    out.append(macro('envDecls', facts['env_decls']))
    for k, v in facts['env_kinds'].items():
        out.append(macro('envKind' + k.capitalize(), v))
    out.append(macro('rtFragments', facts['rt_fragments']))
    out.append(macro('rtFailed', len(facts['rt_failed'])))
    out.append(macro('rtEnvTerms', facts['rt_env_terms']))
    out.append(macro('rtEnvFailed', len(facts['rt_env_failed'])))
    out.append(macro('buildSeconds', f"{facts['build_seconds']:.1f}"))
    out.append(macro('unfoldedAgrees', yes(facts['unfolded_agrees'])))
    out.append(macro('leanDecls', facts['lean_decls']))
    out.append(macro('leanLines', facts['lean_lines']))
    out.append(macro('leanChars', f"{facts['lean_chars']:,}".replace(',', '{,}')))
    out.append(macro('leanAccelerated', ', '.join(
        f'\\code{{{n}}}' for n in facts['lean_accelerated'])))
    out.append(macro('leanAcceleratedCount', len(facts['lean_accelerated'])))
    for k, v in facts.items():
        if k.startswith('proofchars_'):
            name = k[len('proofchars_'):].replace('_', '')
            out.append(macro('proofChars' + name.capitalize().replace('Sched', 'Sched'),
                             f"{v:,}".replace(',', '{,}')))
    out.append(macro('leanRan', yes(facts['lean_ran'])))
    if facts['lean_ran']:
        out.append(macro('leanVersion', facts['lean_version']))
        out.append(macro('leanSeconds', f"{facts['lean_seconds']:.1f}"))
        out.append(macro('leanOk', yes(facts['lean_ok'])))
        out.append(macro('leanAxioms', facts['lean_axioms']
                         .replace("'", '').replace('_', '\\_')))
        out.append(macro('leanAxiomFree', facts['lean_axiom_free']))
        out.append(macro('leanAllDecls', facts['lean_all_decls']))
        out.append(macro('leanAllOk', yes(facts['lean_all_ok'])))
        out.append(macro('leanAllSkipped', ', '.join(
            '\\code{' + n + '}' for n in facts['lean_all_skipped'])))
        out.append(macro('tamperRefused', yes(facts['tamper_refused'])))
        out.append(macro('tamperErrors', facts['tamper_errors']))
        out.append(macro('tamperFirst', facts['tamper_first']
                         .replace('_', '\\_')))
        out.append(macro('tamperWhere', ', '.join(
            '\\code{' + w.replace('_', '\\_') + '}'
            for w in facts['tamper_where'])))
        out.append(macro('tamperAxioms', facts['tamper_axioms']
                         .replace("'", '').replace('_', '\\_')))
    for name in ('tick', 'sched', 'scheme_of', 'accepted'):
        rt = facts[f'py_roundtrip_{name}']
        out.append(macro('pyRoundtrip' + name.replace('_', '').capitalize(),
                         {True: 'identical', False: 'changed',
                          None: 'unreadable'}[rt]))
        why = facts[f'py_hoare_{name}'] or 'accepted'
        write(f'hoare-{name.replace("_", "")}.txt', why)
        out.append(macro('pyWarn' + name.replace('_', '').capitalize(),
                         len(facts[f'py2tex_warn_{name}'])))
    write('facts.tex', ''.join(out))


def main(run_lean=True):
    os.makedirs(GEN, exist_ok=True)
    env, facts, parts = build()
    print(f"built the model: {len(env)} declarations "
          f"in {facts['build_seconds']:.1f}s")
    kernel_latex(env, facts, parts)
    print(f"type2latex: {facts['rt_fragments']} fragments, "
          f"{len(facts['rt_failed'])} failed to read back; whole environment "
          f"{facts['rt_env_terms']} terms, {len(facts['rt_env_failed'])} failed")
    lean_side(env, facts, run_lean)
    if facts['lean_ran']:
        print(f"Lean {facts['lean_version']}: {facts['lean_decls']} "
              f"declarations, {facts['lean_lines']} lines, "
              f"{'accepted' if facts['lean_ok'] else 'REFUSED'} in "
              f"{facts['lean_seconds']:.1f}s; {facts['lean_axioms']}")
        if not facts['lean_ok']:
            print('\n'.join(facts['lean_errors']))
        print(f"whole environment in Lean: {facts['lean_all_decls']} "
              f"declarations, ok={facts['lean_all_ok']}, "
              f"skipped {facts['lean_all_skipped']}")
        print(f"tampered copy refused: {facts['tamper_refused']} "
              f"(first error in {facts['tamper_first']})")
    python_side(facts)
    for name in ('tick', 'sched', 'scheme_of', 'accepted'):
        print(f"py2tex {name}: {len(facts[f'py2tex_warn_{name}'])} warnings; "
              f"return journey {facts[f'py_roundtrip_{name}']}; hoare: "
              f"{facts[f'py_hoare_{name}']}")
    driver_excerpt()
    facts_tex(facts)
    ok = (not facts['rt_failed'] and not facts['rt_env_failed']
          and facts['unfolded_agrees']
          and (not facts['lean_ran'] or
               (facts['lean_ok'] and facts['tamper_refused']
                and facts['lean_axiom_free'] == 3)))
    print('all consistent' if ok else 'SOMETHING DISAGREES')
    return ok


if __name__ == '__main__':
    sys.setrecursionlimit(300000)
    threading.stack_size(512 * 1024 * 1024)
    result = []
    thread = threading.Thread(
        target=lambda: result.append(main('--no-lean' not in sys.argv)))
    thread.start()
    thread.join()
    sys.exit(0 if result and result[0] else 1)
