# RosettaMath

*Bridging the gap between mathematical notation and executable Python.*
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
| `neomath.tex` | The paper. |

---

## Install

```sh
make install       # Ubuntu/Debian: PyQt5, TeX Live, Latin Modern, poppler
make check-deps    # report what is present and what is missing
make ui            # launch the explorer
```

`make install-all` adds the optional extras (scipy, ImageMagick, Ghostscript).
`make help` lists every target.

Nothing but Python 3 is needed for the translator itself; the packages are for
the interface and for typesetting the paper.

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

```sh
python3 rosettaui.py                    # launch
python3 rosettaui.py --tex '$E=mc^2$'   # launch on a given equation
python3 rosettaui.py --selftest         # headless checks, no display needed
python3 rosettaui.py --render-test      # offscreen render to /tmp/rosettaui.png
```

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
| `f x` | application, by juxtaposition |
| `\forall \{A : T\}, B` | implicit binder |
| `a = b` | `Eq A a b`, with `A` from the binder, or inferred |
| `0`, `1`, `2` | numerals, as stacks of `succ` over `zero` |

The front end is shared with the rest of the project: `rosettaui.tokenize`
lexes the subset and `rosettamath.unescape` handles `\text{}` content.

```sh
make proofs              # check the theorems
python3 lean4.py --selftest      # 153 kernel, elaborator and front-end checks
python3 lean4.py --non-strict    # report failures instead of raising
```

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
```

`python3 rosettamath.py` runs the self test against Stage 0 and again against
the LaTeX-born Stage 1, then reports the fixed point. `rosettaui.py --selftest`
covers the parser, the unicode converter, the equation classifier, the
integrity of the knowledge base, and the bridge back to `rosettamath`.

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
