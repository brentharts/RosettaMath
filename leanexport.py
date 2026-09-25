#!/usr/bin/env python3
r"""leanexport.py -- lean4.py kernel terms, written out as Lean 4 source.

`type2latex` writes a kernel term in the LaTeX subset the reader takes back.
This writes the same term in the surface syntax of Lean 4, so that a second,
independent kernel -- Lean's own -- can be asked the question `type_check`
already answered.  Nothing here is trusted: if the text is wrong, Lean says so.

Four decisions make the translation faithful rather than approximate.

  Every name lives in `namespace RM`.  `Nat`, `Bool`, `Eq` and `List` are
  re-declared from the kernel's own constructors, in the kernel's order, so
  `Bool.rec` takes its `true` case first here exactly as it does there.

  Every global is applied with `@`.  The kernel term is already fully
  elaborated -- every implicit argument written out -- so Lean is given no
  holes to fill, only a term to check.

  `T.ind` is `T.rec`.  The micro-kernel has no universe polymorphism, so it
  generates two recursors, into Type and into Prop; Lean has one, into
  `Sort u`, and infers `u` from the motive.

  A kernel constructor name is global (`succ`, `mk`, `refl`); a Lean one is
  qualified by its type (`Nat.succ`, `Prod.mk`, `Eq.refl`).

Binder names are chosen as `LatexPrinter` chooses them -- capture-free,
shadowing nothing the body mentions -- with Lean's own lexical rules: no
keyword, no leading underscore, and no name that would turn `sched.loop1`
into a field access on a local called `sched`.
"""

import lean4 as L
from lean4 import App, Bound, Binder, Lambda, Meta, Pi, Universe, Var
from lean4 import free_names, instantiate, occurs, as_numeral

LEAN_KEYWORDS = {
    'at', 'by', 'do', 'else', 'end', 'fun', 'have', 'if', 'in', 'let',
    'match', 'open', 'show', 'then', 'with', 'where', 'from', 'def', 'theorem',
    'forall', 'exists', 'Type', 'Prop', 'Sort', 'instance', 'structure',
    'class', 'namespace', 'section', 'variable', 'universe', 'import', 'for',
    'return', 'mut', 'unless', 'calc', 'suffices', 'obtain', 'this', 'deriving',
    'inductive', 'example', 'abbrev', 'axiom', 'macro', 'syntax', 'notation',
    'local', 'private', 'protected', 'noncomputable', 'partial', 'unsafe',
    'mutual', 'termination_by', 'decreasing_by', 'nomatch', 'nofun', 'try',
    'catch', 'finally', 'break', 'continue', 'rfl', 'sorry', 'at', 'only',
}

P_EXPR, P_ARROW, P_APP, P_ATOM = 0, 1, 2, 3


def _wrap(text, mine, ctx):
    return f'({text})' if mine < ctx else text


class Catalogue:
    """What each global name is, read off the kernel environment."""

    def __init__(self, env, values=None):
        self.env = env
        self.values = values or {}        # name -> value, for accelerated defs
        self.ctor_owner = {}              # 'succ' -> 'Nat'
        self.ctors = {}                   # 'Nat' -> ['zero', 'succ']
        self.nparams = {}                 # 'List' -> 1
        for name, entry in env.items():
            decl = L.as_decl(name, entry)
            if decl.kind == 'inductive':
                self._read_inductive(name)

    def _read_inductive(self, name):
        group = getattr(L.decl_of(self.env, name), 'mutual', None)
        if group:
            return self._read_mutual(name, group)
        rec = L.type_of(self.env, f'{name}.rec')
        params = 0
        body = rec
        while isinstance(body, Pi) and body.var_name != 'C':
            params += 1
            body = instantiate(body.body, Var(body.var_name))
        body = instantiate(body.body, Var('C'))          # past the motive
        ctors = []
        # minor premises are the arrows before the indices and the scrutinee;
        # each ends in C .. (cname params args)
        while isinstance(body, Pi):
            premise = body.var_type
            concl = premise
            while isinstance(concl, Pi):
                concl = instantiate(concl.body, Var(concl.var_name))
            head, args = L.spine(concl)
            if not (isinstance(head, Var) and head.name == 'C' and args):
                break
            built, _ = L.spine(args[-1])
            ctors.append(built.name)
            body = instantiate(body.body, Var('_'))
        self.nparams[name] = params
        self.ctors[name] = ctors
        for c in ctors:
            self.ctor_owner[c] = name

    def _read_mutual(self, name, group):
        """A type of a mutual group: its constructors are the cases whose
        conclusion is its own motive, C_(its place in the group)."""
        body = L.type_of(self.env, f'{name}.rec')
        motives = []
        while isinstance(body, Pi) and body.var_name.startswith('C_'):
            motives.append(body.var_name)
            body = instantiate(body.body, Var(body.var_name))
        mine = motives[list(group).index(name)]
        ctors = []
        while isinstance(body, Pi):
            concl = body.var_type
            while isinstance(concl, Pi):
                concl = instantiate(concl.body, Var(concl.var_name))
            head, args = L.spine(concl)
            if not (isinstance(head, Var) and head.name in motives and args):
                break
            if head.name == mine:
                built, _ = L.spine(args[-1])
                ctors.append(built.name)
            body = instantiate(body.body, Var('_'))
        self.nparams[name] = 0
        self.ctors[name] = ctors
        for c in ctors:
            self.ctor_owner[c] = name
        self.groups = getattr(self, 'groups', {})
        self.groups[name] = tuple(group)

    def kind(self, name):
        return L.as_decl(name, self.env[name]).kind

    def value(self, name):
        v = L.value_of(self.env, name)
        return self.values.get(name) if v is None else v

    def lean_name(self, name):
        """The name as Lean spells it."""
        if name in self.ctor_owner:
            owner = self.ctor_owner[name]
            short = name[len(owner) + 1:] if name.startswith(owner + '.') \
                else name
            return f'{owner}.{short}'
        for suffix in ('.rec', '.ind'):
            if name.endswith(suffix) and name[:-4] in self.ctors:
                return name[:-4] + '.rec'
        return name

    def at(self, name):
        """'@' where Lean would otherwise expect to infer an argument.

        Declarations exported here bind everything explicitly, so only what
        Lean generates itself has implicit binders: a recursor's parameters
        and motive, and a constructor's parameters.  Those are the names that
        need `@` for a fully elaborated kernel term to be read verbatim.
        """
        if name in self.ctor_owner:
            return '@' if self.nparams[self.ctor_owner[name]] else ''
        if self.home(name) != name:                 # a recursor
            return '@'
        return ''

    def home(self, name):
        """The declaration a name comes from: a constructor from its type."""
        if name in self.ctor_owner:
            return self.ctor_owner[name]
        for suffix in ('.rec', '.ind'):
            if name.endswith(suffix) and name[:-4] in self.ctors:
                return name[:-4]
        return name


class LeanPrinter:
    """A kernel term -> Lean 4 surface syntax."""

    def __init__(self, catalogue):
        self.cat = catalogue
        self.scope = []                    # local names, innermost last

    # -- names --------------------------------------------------------------
    def binder_name(self, hint, var_type, body):
        globals_ = free_names(body) | free_names(var_type)
        prefixes = {g.split('.')[0] for g in globals_ if '.' in g}
        taken = set(self.scope) | globals_ | prefixes | LEAN_KEYWORDS
        base = ''.join(ch if (ch.isalnum() or ch in "_'") else '_'
                       for ch in (hint or 'x')).lstrip('_') or 'x'
        if base[0].isdigit():
            base = 'x' + base
        name, n = base, 1
        while name in taken:
            n += 1
            name = f'{base}{n}' if not base[-1].isdigit() else f"{base}'{n}"
        return name

    # -- terms --------------------------------------------------------------
    def write(self, expr, ctx=P_EXPR):
        if isinstance(expr, Universe):
            if expr.level == 0:
                return 'Prop'
            return 'Type' if expr.level == 1 else f'Type {expr.level - 1}'
        if isinstance(expr, Var):
            if expr.name in self.scope:
                return expr.name
            if expr.name == 'zero':
                return '0'
            return self.cat.at(expr.name) + self.cat.lean_name(expr.name)
        if isinstance(expr, L.NatLit):
            return str(expr.value)
        if isinstance(expr, Bound):
            raise L.KernelError(f'loose de Bruijn index #{expr.index}')
        if isinstance(expr, Meta):
            raise L.KernelError('a hole: elaborate before exporting')
        if isinstance(expr, Binder):
            return self.binder(expr, ctx)
        if isinstance(expr, App):
            digits = as_numeral(expr)
            if digits is not None:
                return str(digits)
            head, args = L.spine(expr)
            parts = [self.write(head, P_ATOM)] + \
                    [self.write(a, P_ATOM) for a in args]
            return _wrap(' '.join(parts), P_APP, ctx)
        raise L.KernelError(f'unknown node {type(expr).__name__}')

    def binder(self, expr, ctx):
        pi = isinstance(expr, Pi)
        if pi and not occurs(expr.body, 0):
            dom = self.write(expr.var_type, P_APP)
            body = self.write(instantiate(expr.body, Var('_')), P_ARROW)
            return _wrap(f'{dom} → {body}', P_ARROW, ctx)
        # gather a run of binders of one kind, so `fun a b c =>` reads as one
        names, cur, kind = [], expr, type(expr)
        while isinstance(cur, kind) and not (pi and not occurs(cur.body, 0)):
            dom = self.write(cur.var_type, P_EXPR)
            name = (self.binder_name(cur.var_name, cur.var_type, cur.body)
                    if pi or occurs(cur.body, 0) else '_')
            names.append((name, dom))
            self.scope.append(name)
            cur = instantiate(cur.body, Var(name))
        body = self.write(cur, P_EXPR)
        for _ in names:
            self.scope.pop()
        binders = ' '.join(f'({n} : {d})' for n, d in names)
        text = f'∀ {binders}, {body}' if pi else f'fun {binders} => {body}'
        return _wrap(text, P_EXPR, ctx)


def dependencies(cat, roots):
    """Every declaration the roots mention, transitively, in env order."""
    seen, stack = set(), [cat.home(r) for r in roots]
    while stack:
        name = stack.pop()
        if name in seen or name not in cat.env:
            continue
        seen.add(name)
        terms = [L.type_of(cat.env, name)]
        if cat.kind(name) == 'inductive':
            for c in cat.ctors[name]:
                terms.append(L.type_of(cat.env, c))
            for sibling in getattr(cat, 'groups', {}).get(name, ()):
                stack.append(sibling)          # a mutual group goes whole
        v = cat.value(name)
        if v is not None:
            terms.append(v)
        for t in terms:
            for n in free_names(t):
                stack.append(cat.home(n))
    return [n for n in cat.env if n in seen]


def is_prop(env, type_):
    try:
        return L.type_check(env, type_) == Universe(0)
    except L.KernelError:
        return False


# Declarations given to Lean as its own natural numbers and their arithmetic,
# rather than as written.  The kernel's `Nat` is Lean's `Nat` in shape --
# `zero`, `succ`, a recursor on them -- so it is exported as that type, whose
# literals Lean's kernel holds in binary.  Exported as its own unary type, a
# literal near 2^62 was 2^62 `succ`s the moment Lean unfolded it, and a
# signed 63-bit range is exactly such a literal.  `leb` and `add` go through
# `Nat.ble` and `Nat.add`, which Lean computes on big numbers natively and
# which satisfy the kernel's defining equations *definitionally* (`ble`
# recurses on both arguments as `leb` does; `add` on its second): a proof
# that unfolds `leb (succ a) (succ b)` to `leb a b` still checks.  `sub` keeps
# its own definition: Lean's `Nat.sub` recurses differently, so the unfolding
# a proof relies on would not match.  Nothing here is Python arithmetic: what
# Lean trusts is its own kernel.
NATIVE = {
    'Nat': 'abbrev Nat : Type := _root_.Nat',
    'add': ('noncomputable def add :\n    Nat → Nat → Nat :=\n'
            '  fun (m : Nat) (n : Nat) => _root_.Nat.add m n'),
    'leb': ('noncomputable def leb :\n    Nat → Nat → Bool :=\n'
            '  fun (m : Nat) (n : Nat) => @_root_.Bool.rec (fun _ => Bool) '
            'Bool.false Bool.true (_root_.Nat.ble m n)'),
}


def declaration(cat, name):
    """One declaration of Lean 4 source."""
    env = cat.env
    if name in NATIVE and cat.native:
        return NATIVE[name]
    group = getattr(cat, 'groups', {}).get(name)
    if cat.kind(name) == 'inductive' and group:
        # one `mutual .. end` block, at the group's first member
        if name != group[0]:
            return ''
        blocks = []
        for member in group:
            pr = LeanPrinter(cat)
            lines = [f'  inductive {member} : Type where']
            for c in cat.ctors[member]:
                short = cat.lean_name(c).split('.')[-1]
                lines.append(f'    | {short} : {pr.write(L.type_of(env, c))}')
            blocks.append('\n'.join(lines))
        return 'mutual\n' + '\n'.join(blocks) + '\nend'
    if cat.kind(name) == 'inductive':
        former = L.type_of(env, name)
        pr = LeanPrinter(cat)
        params = []
        for _ in range(cat.nparams[name]):
            n = pr.binder_name(former.var_name, former.var_type, former.body)
            params.append(f'({n} : {pr.write(former.var_type)})')
            pr.scope.append(n)
            former = instantiate(former.body, Var(n))
        head = f'inductive {name}' + (' ' + ' '.join(params) if params else '')
        lines = [f'{head} : {pr.write(former)} where']
        for c in cat.ctors[name]:
            ctype = L.type_of(env, c)
            for pname in pr.scope:
                ctype = instantiate(ctype.body, Var(pname))
            short = cat.lean_name(c).split('.')[-1]
            lines.append(f'  | {short} : {pr.write(ctype)}')
        return '\n'.join(lines)
    type_ = L.type_of(env, name)
    value = cat.value(name)
    if value is None:
        raise L.KernelError(f'{name} is opaque (an axiom or a constant); '
                            f'there is nothing to export but an assumption')
    keyword = 'theorem' if is_prop(env, type_) else 'noncomputable def'
    return (f'{keyword} {name} :\n    {LeanPrinter(cat).write(type_)} :=\n'
            f'  {LeanPrinter(cat).write(value)}')


PREAMBLE = """\
-- Generated by leanexport.py from the lean4.py kernel environment.
-- Every declaration below was first checked by lean4.py's type_check;
-- this file asks Lean 4's kernel the same question.  No axioms, no sorry.
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RM
"""

NUMERALS = """\
-- Kernel numerals are unary; a literal is read through this instance.
def ofNat : _root_.Nat → Nat
  | 0 => Nat.zero
  | n + 1 => Nat.succ (ofNat n)
instance (n : _root_.Nat) : OfNat Nat n := ⟨ofNat n⟩
"""


def export(env, roots, values=None, extra_checks=(), native=True):
    """Lean 4 source declaring the roots and everything they depend on.
    `native` gives Lean its own `Nat` (see NATIVE); False, the unary one."""
    cat = Catalogue(env, values)
    cat.native = native
    order = dependencies(cat, roots)
    chunks = [PREAMBLE]
    for name in order:
        chunks.append(declaration(cat, name))
        if name == 'Nat' and not native:
            chunks.append(NUMERALS)
    chunks.extend(extra_checks)
    chunks.append('end RM\n')
    return '\n\n'.join(chunks), order


def term(env, expr, values=None):
    """One term as Lean 4 text, for quoting in a paper."""
    return LeanPrinter(Catalogue(env, values)).write(expr)
