# RosettaMath

*Bridging the gap between mathematical notation and executable Python.*

## Overview
RosettaMath is a tiny, self-hosting translator designed to convert a minimal subset of LaTeX into executable Python. Built with zero external dependencies, its primary mission is educational: helping mathematicians learn Python, and helping developers understand math and physics conventions. 

By translating standard mathematical symbols into self-documenting code (for instance, mapping $\rho$ to `rho_density` or $c$ to `scipy.constants.c`), RosettaMath demystifies complex equations and transforms them into readable, functional software.

---

## Key Features
*   **Self-Hosting & Bootstrapped:** The core translator is written in the very LaTeX subset it translates. A plain Python script (Stage 0) translates the LaTeX version (Stage 1), verifying itself by reaching a fixed point.
*   **Zero Dependencies:** Runs entirely on standard Python with no external libraries required.
*   **Algorithmic Control Flow:** Natively translates `algpseudocode` environments, including `\Function`, `\If`, `\Else`, `\For`, and `\While` loops.
*   **Math-Mode Parsing:** Intelligently maps inline expressions like `\frac{a}{b}` to `(a)/(b)` and `\geq` to `>=`.
*   **Contextual Variable Mapping (Planned):** Future updates will automatically link symbols to `scipy.constants` to build educational, highly readable physics algorithms.

---

## Supported LaTeX Subset
RosettaMath focuses on a strict, minimal subset of LaTeX to maintain a near one-to-one translation with Python.

| LaTeX Concept | Translated Python | Example |
| :--- | :--- | :--- |
| **Math Operators** | Standard logical/arithmetic operators | `\land` $\to$ `and`, `\gets` $\to$ `=` |
| **Equations** | Python Functions | `$f(x) = 2x + 1$` $\to$ `def f(x): return 2*x + 1` |
| **Piecewise Functions** | `if`/`elif`/`return` structures | `\begin{cases}` $\to$ conditional return paths |
| **Looping** | `for` and `while` loops | `\For{$i = a$ to $b$}` $\to$ `for i in range(a, b + 1):` |

---

## Bootstrapping Process
The project relies on an elegant self-generation architecture:
1.  **Stage 0:** A foundational Python script parses the LaTeX version of the translator.
2.  **Stage 1:** The generated Python executes, translating its own LaTeX source code once more.
3.  **Fixed Point:** When the byte-for-byte output of Stage 1 matches Stage 0, the translation engine is fully self-hosted.

---

## License
This project is licensed under the MIT License.
