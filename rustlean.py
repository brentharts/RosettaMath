#!/usr/bin/env python3
r"""rustlean.py -- every Rust theorem lean4.py accepts, put to Lean 4 as well.

`crust/tools/rustprove.py` proves what `shivyc/rustproof.py` lifts, and keeps
each settled obligation as a certificate: the statement, the term the
micro-kernel accepted for it, and the environment both live in.  This writes
each certificate as a Lean 4 file of its own -- through `leanexport.py`, the
same translation "A Second Kernel Agrees" used -- ending in `#print axioms`,
and runs `lean` on it.  A theorem counts as agreed only if Lean accepts the
file *and* reports that it depends on no axioms.

One file per certificate, because each obligation is proved in an
environment of its own: the callees, records and `__pre` definitions a
function needs, and nothing else.  Sharing a file would mean merging
environments that may define the same name differently.

    python3 rustlean.py ../crust/leanos/alloc.rs ../crust/leanos/regs.rs
    python3 rustlean.py --out gen/lean_rust FILE.rs ...

Nothing here is trusted.  If the translation is wrong, Lean refuses the file
and the theorem is reported as not agreed.
"""
import concurrent.futures
import os
import shutil
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CRUST = os.environ.get('CRUST_DIR') or os.path.join(HERE, '..', 'crust')


def find_lean():
    return shutil.which('lean') or next(
        (p for p in (os.path.expanduser('~/.local/lean/bin/lean'),
                     os.path.expanduser('~/.elan/bin/lean'))
         if os.path.exists(p)), None)


class Verdict:
    """What Lean said about one certificate."""

    def __init__(self, cert, path, accepted, axiom_free, seconds, output):
        self.name = cert.name
        self.function = cert.function
        self.label = cert.label
        self.path = path
        self.accepted = accepted          # lean exited 0
        self.axiom_free = axiom_free      # and #print axioms said none
        self.seconds = seconds
        self.output = output

    @property
    def agreed(self):
        return self.accepted and self.axiom_free

    def __repr__(self):
        return 'Verdict(%s: %s)' % (self.name,
                                    'agreed' if self.agreed else 'NOT agreed')


_VALUES = None


def slow_values():
    """The definitions the micro-kernel accelerates, as they are written.

    Lean is given the definitions and never the accelerators: Python
    arithmetic is part of lean4.py's trusted base, not Lean's."""
    global _VALUES
    if _VALUES is None:
        import hoare as H
        import lean4 as L
        slow = H.prelude(fast=False)
        _VALUES = {n: L.value_of(slow, n) for n in H.ACCELERATED}
    return _VALUES


def lean_source(cert):
    """Lean 4 source declaring `cert`'s theorem and all it depends on."""
    import lean4 as L
    import leanexport as X
    if cert.name not in cert.env:
        L.define(cert.env, cert.name, cert.statement, cert.proof)
    src, _ = X.export(cert.env, [cert.name], slow_values(),
                      ['#print axioms %s' % cert.name])
    return src


def write_all(certs, out_dir):
    """Write one .lean file per certificate; returns [(cert, path)]."""
    import lean4 as L
    os.makedirs(out_dir, exist_ok=True)
    written = []
    for cert in certs:
        path = os.path.join(out_dir, cert.name + '.lean')
        # The kernel recurses deeply on large terms, as it does when proving.
        old = sys.getrecursionlimit()
        sys.setrecursionlimit(max(old, 300000))
        try:
            src = lean_source(cert)
        except L.KernelError as exc:
            src = None
            print('%s: not exportable -- %s' % (cert.name, exc),
                  file=sys.stderr)
        if src is not None:
            with open(path, 'w') as fh:
                fh.write(src)
        written.append((cert, path if src is not None else None))
    return written


def run_lean(lean, cert, path, timeout=900):
    if path is None:
        return Verdict(cert, None, False, False, 0.0, 'not exportable')
    t0 = time.time()
    try:
        run = subprocess.run([lean, path], capture_output=True, text=True,
                             timeout=timeout)
    except subprocess.TimeoutExpired:
        return Verdict(cert, path, False, False, time.time() - t0,
                       'timed out after %ds' % timeout)
    output = run.stdout + run.stderr
    axiom_free = any(cert.name in line and
                     'does not depend on any axioms' in line
                     for line in run.stdout.splitlines())
    accepted = run.returncode == 0 and 'sorry' not in output
    return Verdict(cert, path, accepted, axiom_free, time.time() - t0, output)


def check(certs, out_dir, lean=None, jobs=None):
    """Export every certificate and have Lean check it.  [Verdict]."""
    lean = lean or find_lean()
    if lean is None:
        raise RuntimeError('lean not found; run "make install_lean"')
    written = write_all(certs, out_dir)
    jobs = jobs or min(8, os.cpu_count() or 1)
    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        return list(pool.map(lambda cp: run_lean(lean, *cp), written))


def prove_everything(prover):
    """Ask `prover` for every contract and every panic obligation, so that
    each one it settles leaves a certificate.  Returns the open ones."""
    open_ = []
    for name in sorted(prover.lifted):
        fn = prover.lifted[name]
        if fn.ensures and not prover.contract(name):
            open_.append((name, 'ensures ' + ' and '.join(fn.ensures)))
        for label, ok in prover.safety(name):
            if not ok:
                open_.append((name, label))
    return open_


def main(argv):
    out_dir = os.path.join(HERE, 'gen', 'lean_rust')
    if '--out' in argv:
        i = argv.index('--out')
        out_dir = argv[i + 1]
        del argv[i:i + 2]
    sys.path.insert(0, CRUST)
    sys.path.insert(0, os.path.join(CRUST, 'tools'))
    sys.path.insert(0, HERE)
    import rustprove
    total_agreed = total = 0
    for path in argv:
        with open(path) as fh:
            prover = rustprove.Prover(fh.read())
        open_ = prove_everything(prover)
        verdicts = rustprove.in_big_stack(
            lambda: check(prover.certificates, out_dir))
        print('%s: %d settled by lean4.py, %d open' % (
            path, len(prover.certificates), len(open_)))
        for v in verdicts:
            print('  %-40s %-8s %5.1fs  %s: %s' % (
                v.name, 'agreed' if v.agreed else 'REFUSED', v.seconds,
                v.function, v.label))
            if not v.agreed:
                print('    ' + v.output.strip().replace('\n', '\n    ')[:2000])
        for fn, label in open_:
            print('  %-40s %-8s          %s: %s' % ('', 'open', fn, label))
        total += len(verdicts)
        total_agreed += sum(v.agreed for v in verdicts)
    print('%d of %d theorems agreed by Lean 4' % (total_agreed, total))
    return 0 if total_agreed == total else 1


if __name__ == '__main__':
    import threading
    threading.stack_size(512 * 1024 * 1024)
    rc = []
    t = threading.Thread(target=lambda: rc.append(main(sys.argv[1:])))
    t.start()
    t.join()
    sys.exit(rc[0] if rc else 1)
