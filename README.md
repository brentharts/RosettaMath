# RosettaMath

*Bridging the gap between mathematical notation and executable Python.*
- https://ai.vixra.org/abs/2609.0019 "LEAN Proofs Small Enough to Read: Kernel Contracts from LATEX Theorems to Compiler Decisions"
- https://doi.org/10.5281/zenodo.22646969 "RosettaMath: Reading, Running and Proving Mathematics from LATEX"

## Overview

RosettaMath is a tiny, self-hosting translator that converts a minimal subset
of LaTeX into executable Python, with zero external dependencies. Its mission
is educational: helping mathematicians learn Python, and helping developers
read the conventions of maths and physics.

The project is two files:

| File | What it is |
| :--- | :--- |
| `rosettamath.py` | The translator. Self-hosting: written in the LaTeX subset it translates, and bootstrapped to a fixed point. |
| `rosettaui.py` | An interactive PyQt5 explorer for that subset. Plain Python, deliberately not self-hosted. |
| `lean4.py` | A dependent-type micro-kernel that checks proofs about Python code, with the theorem statements written in LaTeX. |
| `hoare.py` | An imperative fragment on top of that kernel: Hoare triples, loop invariants, records, and a kernel-checked model of an seL4-style OS. See [LEAN4.md](LEAN4.md). |
| `crustproof.py` | The bridge to [Crust](https://github.com/brentharts/crust): its contracts, as propositions the kernel settles. |
| `neomath.tex` | The paper. |

---

## Proving Python correct: `lean4.py` and `hoare.py`

Two files, and the second is why the first exists.

`lean4.py` is a Calculus of Constructions micro-kernel — the foundation Lean
and Coq are built on — small enough to read in one sitting. `hoare.py` builds
an imperative language on top of it and uses it to model an seL4-style
operating system kernel, with every claim checked by the micro-kernel rather
than asserted.

```python
@procedure(preserves='Context', ensures=['result.current == result.nthreads'])
def schedule(c: 'Context') -> 'Context':
    while c.current < c.nthreads:
        assert invariant(c.current <= c.nthreads)
        assert variant(c.nthreads - c.current)
        c.current = c.current + 1
        c.ticks = c.ticks + 1
    return c
```

That is ordinary Python. It is also a Hoare triple: the body is compiled to a
term of the calculus of constructions, the loop becomes a fold, and the
contract becomes a proposition the kernel checks. Nothing is assumed — there
are no axioms in the environment, and the proofs that a loop keeps an
invariant and that it finishes are theorems proved from `Nat.ind` and
`Bool.ind`.

**What it does now**

*   **An imperative fragment.** Assignment, `if`, `for i in range(n)`, and
    `while` with an explicit variant. Bodies are compiled by symbolic
    execution into pure kernel terms — assignment is substitution, `if` is
    `ite`, a loop is `Nat.rec`. No state type, no big-step semantics.
*   **Contracts as decidable propositions.** `Holds b := Eq Bool b true`, so
    the proposition is about the same expression a runtime check would
    evaluate — which is what makes a proof able to license deleting one.
*   **Records with named fields**, generated from a field list, so a kernel
    context reads as `c.frames` rather than as a spine of `fst` and `snd`.
*   **A `while` rule with four obligations**, including `progress` — that the
    loop really has finished — so the lowering is checked rather than argued
    for in a comment.
*   **Termination proved, not tested.** `fold_terminates` shows the variant
    bounds the number of passes, from a chain of lemmas (`absurd`,
    `leb_trans`, `sub_lt`, `stuck`) all proved by induction.
*   **A sequence rule and composition.** Statements before and after a loop
    are steps of their own; syscalls chain, and so do their proofs.
*   **A model of [Crust](https://github.com/brentharts/crust)'s `crustos`.**
    All four public functions of `crustos/schemes.py` — URL scheme routing
    over byte strings — are modelled and given contracts. `scheme_of`'s
    index never leaves the scheme table; `accepted`'s result is never longer
    than its input, for **every** input.

The details, the design decisions, and what is deliberately refused are in
**[LEAN4.md](LEAN4.md)**.

*   **Integrated with [Crust](https://github.com/brentharts/crust).**
    `crustproof.py` reads Crust's contracts as propositions. Running it
    against Crust's own two readings found that they disagreed: the pass that
    reports contract violations stopped at the first clause, so
    `assert len(p) >= 4` plus `assert not len(p) % 4` let a seven-byte
    argument through. Crust now has one reading, in `shivyc/proofs.py`, that
    both passes call and the kernel checks. A proof now *changes generated
    code*: a SIMD kernel's scalar remainder loop is dropped only on a
    kernel-checked certificate, and a contract proven at every call site lets
    `--mem-safe` skip the bounds work on a parameter (80% of the checks in a
    small initializer). Withdraw the certificate and both come back.

```sh
python3 hoare.py       # 157 checks
python3 lean4.py       # the micro-kernel's own 153
python3 crustproof.py  # 21, including the differential test against Crust
```

---

## Proofs: `lean4.py`

A Calculus of Constructions micro-kernel — the foundation Lean and Coq are
built on — small enough to read in one sitting. The Xena project rendered Lean
proofs *into* LaTeX; this flips the bridge and uses LaTeX as the *input*
language for stating theorems about Python functions.

```python
@theorem(r'\forall x \in \text{Nat}, x = x')
def reflexivity(x: 'Nat'):
    return refl(x)
```

The function is compiled to a kernel term, type checked, and the LaTeX
statement is read as a type. Both must agree — checking only that the Python is
well typed would prove nothing about what it claims. A theorem that does not
prove its statement raises, so `make proofs` gates CI; `--non-strict` records
the failure and continues.

### Representation

Bound variables are **de Bruijn indices**; free variables and constants keep
their names. That removes two classes of bug by construction rather than
patching them:

*   **Substitution cannot capture.** A name in the substituted term can never
    collide with an index.
*   **Alpha-equivalent terms are the same object.** `∀ x : Nat, Nat` and
    `∀ y : Nat, Nat` compare equal with no renaming machinery — which matters,
    because comparing types is how every decision in a proof checker gets made.

The constructors still take names, so terms read the way they always did:
`Lambda("T", Universe(1), Var("T"))` abstracts the `T` for you, and the printer
renames binders that would shadow a free variable, so the output never claims
a variable is bound when it isn't.

### Implicit arguments

`refl` has type `∀ {A : Type}, ∀ a : A, Eq A a a`. The braces mark `A` as
implicit, so each use contributes a hole and the proof is written `refl(x)` —
the way Lean writes it — rather than `refl(Nat, x)`. The hole is solved by
unifying the expected argument type against the actual one.

The elaborator that does this is **deliberately untrusted**. It fills in the
holes and then hands the completed term to `type_check`, which verifies it from
scratch knowing nothing about implicit arguments. A bug in the elaborator can
therefore cost you a confusing error message, but not a false theorem — the
same separation Lean maintains between its elaborator and its kernel.

Elaboration runs over *opened* terms: entering a binder replaces the bound
variable with a fresh free name, and the binder is closed again on the way out.
That is what lets a hole be solved with a bound variable, as in

```python
@theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, a = a')
def reflexivity_anywhere(A: 'Type', a: 'A'):
    return refl(a)
```

where `A` is itself bound. A raw de Bruijn index would mean something different
at every depth it appeared in; a name does not.

Write `explicit(refl)(Nat, x)` — Lean's `@refl` — to supply an implicit
argument by hand.

### Higher-order holes

An implicit argument in a *dependent* position is only ever seen applied.
`transport` has type `∀ {A} {P : A → Prop} {a b : A}, Eq A a b → P a → P b`, so
working out the motive `P` means solving `?P a = Eq A a c` — a higher-order
question, which first-order decomposition can only answer by demanding `a = c`.

Unification therefore covers **Miller's pattern fragment**: a hole applied to
distinct variables is solved by abstracting those variables out of the other
side. That is enough for

```python
@theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, \forall b \in A, \forall c \in A, '
         r'\text{Eq} A a b \to \text{Eq} A a c \to \text{Eq} A b c')
def transitivity(A: 'Type', a: 'A', b: 'A', c: 'A',
                 h: r'\text{Eq} A a b', p: r'\text{Eq} A a c'):
    return transport(h, p)
```

where the elaborator synthesises the motive `λ z ⇒ Eq A z c` on its own.

Full higher-order unification is undecidable, so outside the fragment — a hole
applied to a repeated variable, or to something that is not a variable — the
elaborator refuses rather than guesses. A guess there is a proof nobody wrote.

### Postponed constraints

Even inside the fragment a constraint can have more than one legal answer.
`?P a = Eq A a a` admits both `λz. Eq A z z` and `λz. Eq A z a` whenever `a` is
in scope where the hole was made — so each hole records the scope it was
created in, and a constraint is only ambiguous when the variable is in it.

Ambiguous constraints are **postponed**, then settled once every constraint on
that hole is known. Each constraint proposes not one solution but the whole
family of them — obtained by abstracting *any subset* of the occurrences, most
abstracted first — and a proposal is accepted only if it satisfies all the
constraints. That is what lets `symm` be written the natural way:

```python
@theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, \forall b \in A, '
         r'\text{Eq} A a b \to \text{Eq} A b a')
def symmetry(A: 'Type', a: 'A', b: 'A', h: r'\text{Eq} A a b'):
    return transport(h, refl(a))
```

`?P a = Eq A a a` proposes `λz. Eq A z z`; `?P b = Eq A b a` proposes
`λz. Eq A z a`. Only the second survives both, and it is the one that means
symmetry. Solved eagerly, the first proposal wins and the theorem fails with
`stated Eq A b a, proved Eq A b b`.

Abstracting *every* occurrence is not always right either. In

```python
@theorem(r'\forall \{A : \text{Type}\}, \forall a \in A, \forall b \in A, '
         r'\text{Eq} A a b \to \text{Eq} A a b')
def rewrite_noop(A: 'Type', a: 'A', b: 'A', h: r'\text{Eq} A a b'):
    return transport(h, h)
```

the motive must be the *constant* `λz. Eq A a b`, abstracting nothing. Full
abstraction from either constraint gives the wrong answer, so the candidate
family includes the partial readings too. With `n` occurrences there are `2ⁿ`
of them, capped at 64 before falling back to the full abstraction alone.

When several readings survive every constraint, the elaborator takes the most
abstracted and says so:

```
Note: the implicit argument ?P was not fully determined; took
(λ a ⇒ Eq A a a), and (λ a' ⇒ Eq A a' a) would also have done
```

The theorem is proved either way — `type_check` runs on the finished term
regardless — but the choice was not forced, and the reader deserves to know.

A hole that no reading can satisfy is reported rather than left tentative, so
postponement can cost an error message, never a false theorem.

Checking is bidirectional: the expected type is pushed inwards through the
lambdas rather than compared at the top. Inside the binders both sides are
open, with ordinary names, which is what puts `?P a` in the pattern fragment at
all; two closed types facing each other would leave de Bruijn indices with no
name to abstract over.

The environment ships the inductive types `Nat`, `Bool`, `List` and `Eq`,
with `refl` as a constructor and `symm`, `trans`, `congrArg` and `transport`
proved from `Eq.ind`.

### Definitions and inductive types

A global name may carry a value as well as a type, so a definition **unfolds**
(delta reduction), and an inductive type may be declared with its constructors,
from which the recursor and its computation rule are generated (iota
reduction). `Nat` is declared rather than assumed:

```python
inductive(env, 'Nat', [('zero', []), ('succ', [REC])])
```

which gives `zero`, `succ`, `Nat.rec` for defining functions and `Nat.ind` for
proving theorems — two recursors because there is no universe polymorphism
here. With `add` defined by recursion on its second argument, `add 2 3`
computes to `5`; `m + 0 = m` holds by computation alone, and `0 + n = n` is
stuck until `n` is a constructor, so it needs induction:

```python
@definition(r'\text{Nat} \to \text{Prop}')
def add_zero_motive(k: 'Nat'):
    return Eq(Nat, add(zero, k), k)

@theorem(r'\forall n \in \text{Nat}, \text{Eq} \text{Nat} (\text{add} \text{zero} n) n')
def add_zero_left(n: 'Nat'):
    return explicit(Nat.ind)(add_zero_motive, refl(zero), add_zero_induction_step, n)
```

`@definition` adds a checked function to the environment, so later proofs can
build on earlier ones instead of standing alone.

### Families: parameters, indices, and equality

A family may take **parameters**, fixed across all constructors, and
**indices**, which vary from one constructor to the next:

```python
inductive(env, 'List', [('nil', []), ('cons', [Var('A'), REC])],
          params=[('A', Universe(1))])

inductive(env, 'Eq', [('refl', [], [Var('a')])],
          params=[('A', Universe(1)), ('a', Var('A'), False)],
          indices=[('b', Var('A'))], level=0)
```

Parameters are implicit in the constructors, so a list is written
`cons(7, cons(8, nil))` and the element type is inferred, never spelled out.
`List.rec` then computes: a `length` defined from it reduces
`length (cons 7 (cons 8 nil))` to `2`.

Indices are what make **equality expressible as an inductive type** rather than
assumed. `Eq A a b` is the family whose one constructor `refl` only ever builds
the case where `b` is `a` — that is the entire content of equality — and its
recursor is the J rule. So `symm`, `trans`, `congrArg` and `transport` are now
*proved* from it:

```
inductive   Eq        : ∀ A : Type 0, (A → (A → Prop))
constructor refl      : ∀ {A : Type 0}, ∀ a : A, Eq A a a
recursor    Eq.ind    : ∀ {A} {a : A} {C : ∀ b : A, Eq A a b → Prop},
                          C a (refl A a) → ∀ b, ∀ t : Eq A a b, C b t
definition  symm      : ∀ {A} {a b : A}, Eq A a b → Eq A b a
definition  trans     : ...
```

That matters because an axiom is something you have to trust and a definition
is not. The trusted base is now the kernel and nothing else.

The restrictions that remain are stated rather than hidden: a definition may
not mention itself, so unfolding always terminates — recursion belongs in the
recursor — and a recursive argument is only allowed in a family without
indices, since the induction hypothesis would otherwise have to name the
indices of that occurrence.

### The statement language

| LaTeX | Kernel |
| :--- | :--- |
| `\text{Nat}`, `\mathbb{N}` | a named type |
| `\text{Prop}`, `\text{Type}` | sorts |
| `A \to B` | function type, right associative |
| `\forall x \in A, B` / `\forall (x : A), B` | dependent function type |
| `\lambda x : A, b` / `\fun x : A, b` | a function |
| `f x` | application, by juxtaposition |
| `\forall \{A : T\}, B` | implicit binder |
| `a = b` | `Eq A a b`, with `A` from the binder, or inferred |
| `0`, `1`, `2` | numerals, as stacks of `succ` over `zero` |

The front end is shared with the rest of the project: `rosettaui.tokenize`
lexes the subset and `rosettamath.unescape` handles `\text{}` content.

### And back again

`type2latex` is that table read right to left, and the property that makes it
worth having is that

```python
latex2type(type2latex(t)) == t
```

for every term the kernel checks. It is therefore written against the parser
rather than against taste: every shape it emits is emitted because the parser
accepts it, and anything the parser could not read back is **refused with the
reason** — a hole, a loose index, `Type 1`, or a name like `N` that the reader
would alias away — rather than approximated.

`pretty` is not that function and cannot become it. It prints `Type 1`, `?A7`,
`λ` and `x'`, none of which the reader takes; its output is for a human to
look at and this one is for the reader to take back.

Two places where the term does not determine the text, and the rule each one
needed:

*   **Binder names.** `key()` ignores a binder's name hint, so a name is free
    to change — but only within what the reader can lex. `tokenize` splits
    `Nat` into `N`, `a`, `t`, and a binder name is taken as one token, so a
    bound name must be a single letter; `fresh`'s `x'` is two tokens and would
    not come back. The letter chosen also avoids the free names of the body,
    or the reader would abstract two different variables into one.
*   **`a = b`.** The parser recovers `Eq`'s carrier from the binder that
    introduced an operand, so `a = b` is written only when that lookup would
    return this very carrier. Otherwise the application is written out as
    `\text{Eq} A a b`, which always reads back.

The lambda is in the table above for this reason. Without it, five of the 91
declarations `hoare.py` builds — `snoc_le`, `stuck`, `fold_preserves`,
`fold_terminates`, `loop_preserves`, which is most of §4.2's list — had types
the statement language could not write down, because an induction motive and
the `Nat.rec` a loop lowers to are both lambdas appearing inside a type.
Normalising removes neither. With it, every type **and every value** in that
environment — 141 terms — round-trips.

```sh
make proofs              # check the theorems
python3 lean4.py --selftest      # 177 kernel, elaborator and front-end checks
python3 lean4.py --non-strict    # report failures instead of raising
```

---

## Install

Nothing but Python 3 is needed for the translator itself. The packages below
are for the interface and for typesetting the paper, and they split into two
groups:

*   **PyQt5** — required for the graphical explorer. Without it `rosettaui.py`
    still runs `--selftest` and `--check-deps`, but there is no window.
*   **A TeX installation and a PDF rasteriser** — optional. Without them the
    explorer runs and every symbol is still clickable; only the *Typeset with
    pdflatex* button goes grey, and `make pdf` cannot build the paper.

On any platform, this reports what you have and what you are missing:

```sh
python3 rosettaui.py --check-deps
```

It names the exact install command for whichever platform it is run on, so it
is the fastest way to find out what is wrong.

### Linux (Ubuntu/Debian)

```sh
make install       # PyQt5, TeX Live, Latin Modern, poppler
make check-deps    # report what is present and what is missing
make ui            # launch the explorer
```

`make install-all` adds the optional extras (scipy, ImageMagick, Ghostscript).
`make help` lists every target.

### macOS

Needs [Homebrew](https://brew.sh). Then:

```sh
make install_apple   # poppler + MacTeX, and a .venv holding PyQt5
make check-deps
make ui
```

Two things differ from Linux, and both are handled for you:

*   **PyQt5 goes into a virtualenv** (`.venv`, created by the target). macOS
    has no system package for PyQt5, and both Apple's Python and Homebrew's
    refuse `pip install` into themselves — that is PEP 668, the
    `externally-managed-environment` error. Every `make` target picks the
    virtualenv up automatically once it exists, so `make ui` just works.
*   **MacTeX installs to `/Library/TeX/texbin`**, which is added to `PATH` by a
    file in `/etc/paths.d` that only *login* shells read. A terminal you had
    open before installing will not see `pdflatex`, and neither will an app
    launched from Finder. `rosettaui.py` looks in that directory itself, so it
    finds TeX either way — but `which pdflatex` may still come up empty until
    you open a new terminal, which is expected rather than a broken install.

`make install_apple-all` adds ImageMagick and Ghostscript.

MacTeX is about a 5 GB download. If that is too much, BasicTeX plus the four
packages this project actually uses is around 100 MB:

```sh
brew install --cask basictex
sudo tlmgr update --self
sudo tlmgr install orcidlink algorithms algorithmicx listings lm lm-math
```

To run without `make`:

```sh
.venv/bin/python rosettaui.py
```

### Windows

There is no `make` on Windows, and none is needed. Open the folder in File
Explorer and double-click, in order:

| File | What it does |
| --- | --- |
| `install_windows.bat` | Installs PyQt5 and scipy, and offers to install MiKTeX |
| `run_windows.bat` | Starts the explorer |

`install_windows.bat` installs everything into your own account, so it never
asks for administrator rights, and it prints a summary of what it found at the
end. If it reports that Python is missing, install it first — either from
[python.org](https://www.python.org/downloads/), **ticking "Add python.exe to
PATH" on the installer's first screen**, or by running `winget install
Python.Python.3.12` in Windows Terminal.

MiKTeX is optional and is a ~200 MB download, so the installer asks before
fetching it. It bundles `pdftoppm` as well as `pdflatex`, so it covers both TeX
requirements at once. MiKTeX also downloads individual LaTeX packages on first
use, so your first typeset may pause and show a progress box — that is normal.

If you would rather use the command line, note that the interpreter is called
`python`, not `python3`, and that arguments need double quotes:

```bat
python rosettaui.py --check-deps
python rosettaui.py
python rosettaui.py --tex "E = mc^2"
```

If `run_windows.bat` flashes and no window appears, run `python rosettaui.py`
from a Command Prompt in this folder — the launcher is deliberately
console-free, so that is where the error message will be.

---

## Key Features

*   **Self-Hosting & Bootstrapped:** The core translator is written in the very
    LaTeX subset it translates. A plain Python script (Stage 0) translates the
    LaTeX version (Stage 1), verifying itself by reaching a fixed point.
*   **Zero Dependencies:** The translator runs on standard Python alone.
*   **Algorithmic Control Flow:** Natively translates `algpseudocode`
    environments, including `\Function`, `\If`, `\Else`, `\For` and `\While`.
*   **Math-Mode Parsing:** Maps `\frac{a}{b}` to `(a)/(b)`, `\geq` to `>=`, and
    juxtaposition to multiplication.
*   **Bidirectional and verified:** `Python2Tex` walks a Python AST back into
    publication ready pseudocode, and a round-trip test checks that the
    function still *behaves* the same after the return journey.
*   **Interactive:** `rosettaui.py` makes every glyph of an equation clickable,
    identifies the equation, and shows the Python it becomes.
*   **Proof-carrying:** `lean4.py` checks proofs about Python with no axioms,
    and `hoare.py` extends that to imperative code — loops, records, state
    invariants — and models an OS kernel with it. See [LEAN4.md](LEAN4.md).

---

## Supported LaTeX Subset

| LaTeX Concept | Translated Python | Example |
| :--- | :--- | :--- |
| **Math Operators** | Standard logical/arithmetic operators | `\land` → `and`, `\gets` → `=` |
| **Equations** | Python Functions | `$f(x) = 2x + 1$` → `def f(x): return 2*x + 1` |
| **Piecewise Functions** | `if`/`elif`/`return` structures | `\begin{cases}` → conditional return paths |
| **Looping** | `for` and `while` loops | `\For{$i = a$ to $b$}` → `for i in range(a, b + 1):` |
| **Implicit Multiplication** | An explicit `*` | `$k_B c^3 A$` → `k_B*c**3*A` |
| **Inferred Parameters** | A real argument list | `$S = k_B \log W$` → `def S(k_B, W):` |

### Implicit multiplication

Juxtaposition means "multiply" to a reader and nothing at all to a parser.
A space between two *atoms* now becomes a `*`, while a space beside an operator
is left alone — so `\land` still translates to `and` rather than being mangled
into a product. The check is deliberately conservative: it leaves the
translator's own LaTeX source byte-for-byte unchanged.

### Inferred parameters

An equation whose left-hand side is a bare symbol names no arguments, so the
free variables of the right-hand side become the parameter list. Names the
caller already supplies stay constants:

```python
latex2py(r'$S = \frac{k_B c^3 A}{4 G \hbar}$')
# def S(k_B, c, A, G, hbar): ...

latex2py(r'$S = \frac{k_B c^3 A}{4 G \hbar}$', {'k_B': k, 'c': c, 'G': G, 'hbar': hbar})
# def S(A): ...
```

That second form is the point of the exercise. Feeding it CODATA values gives
1.449e54 J/K for the entropy of a one-solar-mass black hole, against a
literature value of about 1.5e54.

---

## The interactive explorer

`rosettaui.py` renders an equation glyph by glyph into a `QGraphicsScene`,
where each symbol is a live object:

*   **hover** — a tooltip with the symbol's name, its Greek or Latin origin,
    and what it conventionally denotes in physics and maths
*   **left click** — a full offline description, with a "typeset with pdflatex"
    button for anything the unicode approximation cannot stack
*   **right click** — the relevant Wikipedia article, plus other equations that
    use the same symbol

The whole equation is classified against a library of well known equations by
matching the set of symbols and structures it contains, so the view can report
"this looks like the Klein-Gordon equation" or fall back to "this is a
second-order partial differential equation of the kind that governs fields".

The menu bar doubles as a small offline encyclopedia: equations grouped by
field, concept articles on notation and convention, and every symbol grouped by
category, all cross linked and all with Wikipedia links.

A side panel shows what `rosettamath` makes of the same LaTeX. Symbols that are
physical constants are recognised as such, kept out of the argument list, and
bound with a generated `from scipy.constants import ...` line — so the equation
you read and the code you run are the same artefact.

### Opening a paper

**File → Open .tex file…** (Ctrl+O) scans a LaTeX document and fills a dropdown
with every equation in it. Pick one and it fills the screen exactly as a typed
equation does; **Ctrl+Right** and **Ctrl+Left** step through the paper, which is
the useful motion when presenting.

Entries are labelled with the equation's own number, so `(14)` in the dropdown
is `(14)` in the printed paper, alongside a Unicode preview and either the
`\label` or the enclosing section. The status bar gives the source line.

The scanner is deliberately more permissive than `rosettamath.py`'s subset,
because papers from arXiv are not written in that subset and never will be. It
handles:

*   `equation`, `align`, `gather`, `multline`, `eqnarray`, `flalign`, `alignat`,
    their starred forms, `\[…\]`, `$$…$$`, `\(…\)` and `$…$`
*   `\newcommand`, `\renewcommand`, `\def` and `\DeclareMathOperator`, including
    `#1`-style arguments — authors almost always abbreviate their own notation,
    and without expanding it half the symbols in a paper are unrecognisable
*   shorthand equation wrappers — `\be`…`\ee`, `\beq`…`\eeq`, `\bea`…`\eea`
    and similar. These have to be resolved across the whole document *before*
    anything is scanned, because they are what makes an equation findable in
    the first place: once an author writes `\newcommand{\be}{\begin{equation}}`,
    the words never appear in the source again. They are assumed even when the
    document does not define them, since the pair often lives in a journal
    `.sty` that is not in the tarball — but only when both halves are present,
    and never when the document defines them as something else. They also turn
    up mid-sentence rather than on their own lines, so nothing assumes otherwise
*   `\input` and `\include`, so a paper split across files is scanned whole
*   equation numbering that follows LaTeX's own rule, so starred environments
    and inline maths are not counted
*   multi-row `align` blocks, split into one entry per row — except that a row
    opening with a relation (`&= c`) is joined to the row above, since on its
    own it is a fragment rather than a statement

and it deliberately ignores `verbatim`, `lstlisting`, `minted` and friends,
whose contents routinely include `$`, `%` and `\begin{…}` without any of it
being mathematics.

### Opening a paper straight from arXiv

**File → Open from arXiv…** (Ctrl+Shift+O) takes a link and reads the paper's
LaTeX source, which is better to explore than the PDF because it is the actual
equations rather than a picture of them. All of these work:

```
https://arxiv.org/abs/2510.24491
https://doi.org/10.48550/arXiv.2510.24491
arXiv:2510.24491v2
2510.24491
https://arxiv.org/abs/math/0309136        (pre-2007 identifiers too)
```

The source comes from `https://arxiv.org/src/<id>`, usually a `.tar.gz`. Papers
split across many files are handled: the root file is identified by content
rather than by name, and its `\input` files are pulled in with it. Downloads are
cached under the system temp directory, so a second look at the same paper costs
nothing.

Not every submission has source. Where an author uploaded only a PDF, that is
reported plainly rather than failing obscurely — there are no equations to read
in that case, and the PDF is better opened in a PDF reader.

Archives are extracted defensively. A tar can name paths outside its own
directory, or contain symlinks pointing anywhere on the disk, and papers are
uploaded by strangers, so members that escape the extraction directory are
dropped rather than trusted.

### Reading the PDF alongside (Linux)

**File → Open PDF alongside** (Ctrl+P) opens the paper's PDF in `evince.py`, a
small Evince wrapper. Double-clicking an equation number such as `(7)` in the
PDF selects it, and the explorer jumps to that equation — so you can read the
paper normally and pull any equation over to be taken apart.

This is why `scan_tex` numbers equations the way LaTeX does rather than counting
the entries it happens to produce: the number in the PDF is the key that links
the two windows. Where an author resets the counter or numbers an appendix
`(A.1)`, the two will not line up, and that is reported rather than guessed at.

Papers opened from arXiv bring their PDF with them. A `.tex` opened from disk
gets the viewer if a PDF of the same name sits next to it.

Linux only — it drives Evince through its GObject bindings, which do not exist
on macOS or Windows. Everything else works everywhere. Install with:

```sh
sudo apt install python3-gi gir1.2-evince-3.0
```

`make install-all` includes these, and `make check-deps` reports them.

To check a paper before teaching from it, without opening a window:

```sh
python3 rosettaui.py --scan paper.tex    # list what was found
python3 rosettaui.py --open paper.tex    # launch straight into it
python3 rosettaui.py --arxiv 2510.24491  # fetch from arXiv and launch
```

Matrices are laid out as a grid and stay as clickable as anything else. One
`matrix` node kind covers `pmatrix`, `bmatrix`, `Bmatrix`, `vmatrix`,
`Vmatrix`, `smallmatrix`, `array`, `cases`, `aligned`, `split`, `gathered`,
`substack` and `subarray` — a case distinction is a two-column grid with a
brace down the left, and a `substack` is a one-column grid with no delimiters,
so they all fall out of the same code. `array` reads its column spec, so
`{lcr}` aligns left, centre and right; `aligned` and `split` alternate right
and left, which is what stacks the equals signs of a derivation under one
another.

Delimiters are drawn as paths sized to their contents rather than as
scaled-up glyphs, because a font's `(` blown up to matrix height thickens with
it and reads wrong.

`\underbrace` and `\overbrace` are drawn as braces spanning their contents,
with the attached `_` or `^` label centred beyond the brace rather than set to
its right. They are annotations rather than operations — they group a span and
name it without changing its value — so both carry a glossary entry saying so,
since a reader meeting one needs to be told it is a label and not an operation
they have failed to recognise.

An environment the parser does not recognise is not dropped: its contents come
through as an ordinary row, so a paper using some unfamiliar environment still
renders its symbols. Anything that still comes out approximate can be checked
against *Typeset with pdflatex* on the right-click menu.

```sh
python3 rosettaui.py                    # launch
python3 rosettaui.py --tex '$E=mc^2$'   # launch on a given equation
python3 rosettaui.py --selftest         # headless checks, no display needed
python3 rosettaui.py --check-deps       # what is installed, and how to get the rest
python3 rosettaui.py --render-test      # offscreen render to a PNG in the temp dir
```

On Windows the interpreter is `python` rather than `python3`, and `--tex` takes
double quotes: `python rosettaui.py --tex "E = mc^2"`. On macOS, after
`make install_apple`, use `.venv/bin/python` in place of `python3`.

---

## The reverse direction

`Python2Tex` turns Python back into `algpseudocode`. Getting this right is
harder than it looks, because LaTeX that reads correctly can still mean
something else:

*   **Precedence is made explicit.** A tree knows that `(a + b) * c` groups; a
    flat string does not. Every operand that binds more loosely than its parent
    is parenthesised on the way out.
*   **Keywords leave math mode.** Inside `$...$` a space between two names is
    implicit multiplication, so `x is None` would translate back as
    `x*is*None`. Writing `$x$ is $None$` puts the keyword in a text segment,
    the same trick the hand-written LaTeX uses.
*   **Underscores are escaped.** A bare `_` is a subscript, so `__name__` is a
    double subscript that LaTeX rejects. `OPS` maps `\_` back to `_`.
*   **Nothing is dropped silently.** Constructs outside the subset — `with`,
    `try`, decorators — are reported as a `\Comment` and collected in a
    warnings list.

`roundtrip_test()` checks 21 cases by behaviour rather than by eye: each is
translated to LaTeX, read back with `tex2py`, executed, and compared against
the original. Every function in `rosettamath.py` itself survives that journey,
including `math2py`.

---

## Bootstrapping Process

The project relies on an elegant self-generation architecture:

1.  **Stage 0:** A foundational Python script parses the LaTeX version of the
    translator.
2.  **Stage 1:** The generated Python executes, translating its own LaTeX
    source code once more.
3.  **Fixed Point:** When the byte-for-byte output of Stage 1 matches Stage 0,
    the translation engine is fully self-hosted.

The practical consequence is that every change to the translator must be made
twice — once in the Python of Stage 0 and once in the LaTeX of `NEOMATH_TEX` —
and the fixed point is the proof that the two agree.

---

## Testing

```sh
make test          # both bootstrap stages, the explorer, and the kernel
make render-test   # layout engine, offscreen
make proofs        # the lean4 theorems
python3 hoare.py   # the imperative fragment and the OS model
```

`python3 rosettamath.py` runs the self test against Stage 0 and again against
the LaTeX-born Stage 1, then reports the fixed point. `rosettaui.py --selftest`
covers the parser, the unicode converter, the equation classifier, the
integrity of the knowledge base, and the bridge back to `rosettamath`.
`hoare.py` runs 157 checks of its own: the prelude's arithmetic and string
operations, the shape every construct lowers to, the proofs of the loop
lemmas, the OS model, and — a third of them — the refusals, each pinned to the
reason it gives.

---

## The paper

The paper's prose is `neomath.tex`, an ordinary LaTeX file. What `rosettamath.py`
adds is the appendix: the self-hosted LaTeX source typeset function by function,
and the Python it becomes, spliced in at the `%%APPENDIX%%` marker.

```sh
make pdf      # /tmp/neomath.pdf, 13 pages
make paper    # with the LaTeX source and generated Python as an appendix
```

It covers all three components, the argument for local, open, Python-based
tooling in mathematics education from school to research, and the path from
the micro-kernel toward verified systems software via
[Crust](https://github.com/brentharts/crust).

---

## License

This project is licensed under the MIT License.
