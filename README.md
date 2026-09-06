# RosettaMath

*Bridging the gap between mathematical notation and executable Python.*

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
make test          # both bootstrap stages, plus the explorer's checks
make render-test   # layout engine, offscreen
```

`python3 rosettamath.py` runs the self test against Stage 0 and again against
the LaTeX-born Stage 1, then reports the fixed point. `rosettaui.py --selftest`
covers the parser, the unicode converter, the equation classifier, the
integrity of the knowledge base, and the bridge back to `rosettamath`.

---

## The paper

```sh
make pdf      # /tmp/neomath.pdf
make paper    # with the LaTeX source and generated Python as an appendix
```

---

## License

This project is licensed under the MIT License.
