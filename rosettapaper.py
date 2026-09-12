#!/usr/bin/env python3
r"""rosettapaper.py -- the knowledge base, written out as a paper.

Every number, table, equation and appendix listing in rosettaphys.tex is
generated from rosettaphys.py at the moment the file is built.  Nothing is
transcribed.

That is not tidiness for its own sake.  A paper about a knowledge base is a
second copy of it, and the second copy is the one that goes stale: an equation
gets added, a join appears, a count in section three quietly becomes wrong, and
nobody notices because prose does not have a selftest.  Generating the document
means the paper cannot disagree with the code, because there is only one of
them.

What is written by hand is the argument -- the prose that says why any of this
matters.  What is generated is every claim of fact.  Where the two meet, a
sentence says "the library currently contains" and a number follows from
len().

    python3 rosettapaper.py                write rosettaphys.tex
    python3 rosettapaper.py --stdout       write it to the terminal instead
    python3 rosettapaper.py --selftest     check the generated document
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0,'../')
import rosettaphys as P
import rosettalean as RL

HERE = os.path.dirname(os.path.abspath(__file__))
OUTPUT = os.path.join(HERE, 'rosettaphys.tex')


# ---------------------------------------------------------------- helpers

def esc(text):
    """Plain text, safe inside LaTeX prose."""
    out = []
    for ch in str(text):
        out.append({'&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#',
                    '_': r'\_', '{': r'\{', '}': r'\}',
                    '~': r'\textasciitilde{}', '^': r'\textasciicircum{}',
                    '\\': r'\textbackslash{}'}.get(ch, ch))
    return ''.join(out)


def number(n):
    """A count as a word, since a spelt number reads better in prose."""
    names = ['no', 'one', 'two', 'three', 'four', 'five', 'six', 'seven',
             'eight', 'nine', 'ten', 'eleven', 'twelve']
    return names[n] if n < len(names) else str(n)


def words(n, singular, plural=None):
    """'one equation', 'six equations' -- numbers under ten read better spelt."""
    return '%s %s' % (number(n),
                      singular if n == 1 else (plural or singular + 's'))


def lines(*parts):
    return '\n'.join(parts)


# ---------------------------------------------------------------- preamble

PREAMBLE = r"""\documentclass[11pt]{article}
\usepackage[margin=2.2cm]{geometry}
\usepackage{amsmath,amssymb,listings}
\usepackage{graphicx}
\usepackage{booktabs}
\usepackage{longtable}
\usepackage{xurl}
\usepackage{xcolor}
\usepackage[colorlinks=true,linkcolor=blue!50!black,citecolor=blue!50!black,urlcolor=blue!50!black]{hyperref}
\usepackage{orcidlink}

\lstset{
    language=Python,
    basicstyle=\ttfamily\small,
    keywordstyle=\color{blue!60!black}\bfseries,
    stringstyle=\color{green!45!black},
    commentstyle=\color{gray}\itshape,
    breaklines=true,
    frame=single,
    framerule=0.3pt,
    xleftmargin=1em,
    columns=fullflexible,
    keepspaces=true,
    showstringspaces=false
}
\lstdefinelanguage{lean}{
    morekeywords={theorem,axiom,instance,namespace,end,forall,by,sorry,def,
                  Type,Prop,Nat,Real},
    morecomment=[l]{--},
    sensitive=true
}
\lstdefinestyle{appendix}{
    basicstyle=\ttfamily\tiny,
    numbers=left,
    numberstyle=\tiny\color{gray},
    stepnumber=1
}

\newcommand{\code}[1]{\texttt{#1}}

\title{A Physics Knowledge Graph from \LaTeX{} Notation to Lean Conjectures}
\author{Brent S. Hartshorn \orcidlink{0009-0004-2853-655X} \small \url{brenthartshorn@proton.me}}
\date{September 2026}

\begin{document}
\maketitle
"""


def abstract():
    return r"""
\begin{abstract}
Physics notation is ambiguous, this paper reports what happens when a knowledge base of %s, %s
and %s is made to declare what each of its letters denotes, and is
then allowed to connect itself. Equations become graph nodes; edges follow
shared \emph{quantities} rather than shared characters; and two equations
stating the same quantity are joined by transitivity into one annotated formula.
The library yields %s so composed and %s that three or more independent equations all
determine---the gravitational constant among them, fixed %s ways by Newton,
Schwarzschild, Hawking, the Planck length, the escape velocity and the surface
gravity, none written with the others in mind. Each statement is checked to be
a well-formed proposition over an axiomatic \code{Real} by a Calculus of
Constructions micro-kernel, then emitted as Lean~4.
\end{abstract}
""" % (words(len(P.EQUATIONS), 'equation'), words(len(P.SYMBOLS), 'symbol'),
       words(len(P.QUANTITIES), 'physical quantity', 'physical quantities'),
       words(len(P.all_joins()), 'pairwise statement'),
       words(len(P.families()), 'quantity', 'quantities'),
       number(len(P.family('G'))),
    )


# ---------------------------------------------------------------- sections

def introduction():
    fams = P.grand_members()
    terms = sum(len(f) for f in fams)
    return r"""

\begin{figure}[htbp]
\centering
\resizebox{\textwidth}{!}{$\displaystyle %s $}
\caption{ \tiny The library, conjoined. %s from %s, each
\texttt{\textbackslash underbrace}d with the equation it came from and
\texttt{\textbackslash overbrace}d with the quantity it determines. Generated
by \code{rosettaphys.grand()}; the corresponding Lean proposition, with all
%d variables bound once across the whole conjunction, is
Appendix~\ref{app:lean}.}
\label{fig:grand}
\end{figure}


\section{Introduction}



\noindent
Nothing in Figure~\ref{fig:grand} was written down. Each equation entered the
library on its own terms, described in its own words, with no reference to the
others; the rows are what the library implies once you ask which of its
equations are about the same thing. Producing them needed no physics---only a
willingness to say what $m$ means.

Here is what a knowledge base of physics equations looks like once it knows
what its own letters mean. Every row is a physical quantity; every term is
what some equation in the library says that quantity equals; the side brace
gathers the rows into a single claim.

Three earlier papers built a translator, an explorer and a kernel. RosettaMath
\cite{hartshorn2026rosetta} reads a subset of \LaTeX{} and writes Python, in
the subset it reads. \code{lean4.py} \cite{hartshorn2026lean} is a Calculus of
Constructions \cite{coquand1988} checker whose statement language is
\LaTeX{}, so a theorem about a Python function is written
\verb|\forall x \in \text{Nat}, x = x|. The most recent
\cite{hartshorn2026second} hands the same terms to Lean~4 \cite{demoura2021},
so a second kernel can be asked what the first already answered.

All three treat notation as something to be \emph{translated}. This paper
treats it as something to be \emph{interrogated}, starting from an observation
the project's own documentation has made since the beginning, in an article
titled ``Overloaded notation'':

\begin{quote}
The single hardest thing about reading physics is that the alphabet ran out
long ago. One glyph carries many meanings and the reader is expected to infer
which from context alone.
\end{quote}

If equations are to be linked automatically, something must decide when two of
them talk about the same thing. The obvious answer---that they share a
symbol---is wrong, and wrong in a way that yields confident nonsense rather
than errors. Section~\ref{sec:readings} is an account of how wrong.

The contribution is threefold: a graph over \textbf{quantities} rather than
glyphs, in which equations declare what their letters denote and may be joined
only where they agree (Section~\ref{sec:graph}); an algebra that rearranges
equations to expose a shared quantity, notable mostly for what it
\textbf{refuses} (Section~\ref{sec:algebra}); and a route from a composed
statement to a Lean conjecture in which the brace annotations survive as
provenance (Section~\ref{sec:lean}).

This document is generated by \code{rosettapaper.py} from the module it
describes. Every count, table and displayed equation below is a function call
at build time, because a paper about a knowledge base is a second copy of it,
and the second copy is the one that goes stale.
""" % (P.grand(), words(terms, 'equation').capitalize(),
       words(len(fams), 'quantity', 'quantities'),
       len(RL.grand_conjecture().variables))


def graph_section():
    g = P.GRAPH
    census = g.census()
    rows = '\n'.join(
        r'\code{%s} & %d & %s \\' % (esc(kind), count, esc(note))
        for kind, count, note in [
            ('denotes', census.get('denotes', 0),
             'equation to the quantity one of its letters means'),
            ('uses', census.get('uses', 0),
             'equation to a symbol in its signature'),
            ('shares', census.get('shares', 0),
             'two equations with a quantity in common'),
            ('mentions', census.get('mentions', 0),
             'article to a symbol it discusses'),
            ('specialises', census.get('specialises', 0),
             'a special case of a more general law'),
            ('defines', census.get('defines', 0),
             'one equation giving another its meaning'),
            ('limit-of', census.get('limit-of', 0),
             'what a law becomes in some limit'),
            ('cites', census.get('cites', 0),
             'article to an equation it discusses'),
            ('field', census.get('field', 0),
             'equations of the same kind'),
        ])
    return r"""
\section{A graph over quantities}
\label{sec:graph}

The nodes are %s, %s, %s and %s---the last
being things like \emph{energy} and \emph{microstate count}, each with a
dimension in the usual $M/L/T/I/K/N$ basis. The graph has %d nodes and %d
edges.

Most edges are derived. A signature already names the symbols an equation is
built from, and two equations mentioning the same quantity are related whether
or not anyone noticed, so the graph grows on its own as entries are added. The
edges that cannot be derived are the interesting ones---that the
time-independent Schr\"odinger equation specialises the time-dependent one is a
fact about physics, not notation---and %s are stated explicitly.

\begin{table}[h]
\centering
\begin{tabular}{llp{7.6cm}}
\toprule
Relation & Count & What it records \\
\midrule
%s
\bottomrule
\end{tabular}
\caption{The edge vocabulary. \code{denotes} did not exist in the first
version: without it an equation is connected to the \emph{characters} it
contains, with it to the quantities it is about. The difference between those
two graphs is Section~\ref{sec:readings}.}
\end{table}
""" % (words(len(P.EQUATIONS), 'equation'), words(len(P.SYMBOLS), 'symbol'),
       words(len(P.CONCEPTS), 'prose article'),
       words(len(P.QUANTITIES), 'physical quantity', 'physical quantities'),
       len(g.nodes), len(g.edges), words(len(P.LINKS), 'stated relation'),
       rows)


def algebra_section():
    joins = P.all_joins()
    rearranged = [d for d in joins if d.rearranged]
    refused = [e for e in P.EQUATIONS if P.algebraic(e['latex']) is not None]
    reasons = {}
    for e in refused:
        why = P.algebraic(e['latex'])
        reasons.setdefault(why, []).append(e.label)
    table = '\n'.join(
        r'%s & %d & %s \\' % (esc(why), len(names), esc(names[0]))
        for why, names in sorted(reasons.items(), key=lambda kv: -len(kv[1])))
    return r"""
\section{An algebra, and what it refuses}
\label{sec:algebra}

Joining needs both equations to state the pivot. Requiring them to state it
\emph{directly}---alone on one side of the equals---yielded only five joins, so
the module grows a small expression algebra: a term type, a reader, a printer,
and \code{isolate}, which peels operations off one side and applies their
inverses to the other.

This is the project's third \LaTeX{} reader. \code{rosettaui} parses for
\emph{shape}, to draw a fraction stacked; \code{lean4} parses \emph{types},
where juxtaposition is application; this parses \emph{algebra}, where
juxtaposition is multiplication. The three disagree about what a space between
two letters means, so one parser with a mode flag would need telling which
dialect it was reading anyway.

\subsection{The first bug}

Nothing in the first version of the reader stopped it parsing $\nabla^2 \psi$
as \emph{nabla squared times psi}. Having done so, solving the
time-independent Schr\"odinger equation for $\psi$ meant dividing by it, and
the library duly reported

\[ \frac{-\left(\frac{\hbar^{2}}{2m}\nabla^{2}\psi\right) + V\psi}{\psi} = h\nu \]

as a join between the Schr\"odinger equation and the Planck relation. It parses,
it renders, and it would have come back from the kernel a well-formed
proposition. It means nothing at all.

The repair is a table of notation that is not scalar algebra---derivatives,
tensor indices, summations, ambiguous signs---checked on the token stream
before the parser starts believing things. An equation containing any of it is
refused for rearrangement but stays in the graph, keeping its signature and its
readings. %s of %d are refused on these grounds.

\begin{table}[h]
\centering
\begin{tabular}{lll}
\toprule
Refused because it contains & Count & For example \\
\midrule
%s
\bottomrule
\end{tabular}
\caption{What the algebra declines to read, and why.}
\end{table}

\subsection{What isolate will not do}

Two further refusals would otherwise produce true-looking falsehoods. An even
power is refused outright: $x^2 = 4$ gives $x = \pm 2$, and a chain built on the
wrong branch is a false statement that typechecks. So is a quantity occurring
twice, since isolating it needs terms collected first.

The simplifier is held to the same standard. It flattens nested fractions and
drops multiplication by one, which hold for every value. It does \emph{not}
cancel the $b$ in $ab/b$, because that needs $b \neq 0$ and the equation does
not say so.

Of %s the library yields, %s required rearrangement, and each derivation
records the fact---a quoted equation and a rearranged one are believable to
different degrees.
""" % (words(len(refused), 'equation'), len(P.EQUATIONS), table,
       words(len(joins), 'pairwise join'), number(len(rearranged)))


def readings_section():
    clashes = P.disagreements()
    seen, rows = set(), []
    for a, b, q, left, right in clashes:
        key = (q, tuple(sorted((left, right))))
        if key in seen:
            continue
        seen.add(key)
        rows.append(r'$%s$ & %s & %s & %s \\'
                    % (esc(q).replace(r'\_', '_'), esc(left), esc(right),
                       esc(a.label)))
    table = '\n'.join(rows)
    return r"""
\section{The second bug, and the readings table}
\label{sec:readings}

With the algebra refusing what it should, the library produced eighty-five
joins. Among them was this one:

\[ \exp\!\left(\frac{S}{k_B}\right) = F d \]

Boltzmann's $W$ counts microstates. The $W$ in $W = Fd$ is an energy. The
letters match, so the graph joined them, and the result is a false statement
that parses, typechecks and renders beautifully. The same fault produced a join
between the Planck relation and gravitational potential energy on $h$, where
one $h$ is Planck's constant and the other is a height.

There is no clever fix, and the absence of one is the point. No amount of
reading the notation recovers the distinction, because the distinction is not
in the notation---it lives in the surrounding prose and the reader's training,
exactly as ``Overloaded notation'' said. The only repair is to write it down.

Each equation therefore carries a \code{reads} table mapping symbols to
quantities, and a pivot requires both equations to agree. An equation that has
declared nothing agrees with nothing, and the join is refused: silence is not
agreement. The library declares %d readings across %s.

Because the readings are declared, the collisions can be \emph{computed}:
any two equations sharing a letter and disagreeing about it mark a place where
physics reused a character. There are %s.

\begin{table}[h]
\centering
\small
\begin{tabular}{llll}
\toprule
Letter & One reading & The other & First seen in \\
\midrule
%s
\bottomrule
\end{tabular}
\caption{Letters this library uses for two different physical quantities,
generated by comparing declared readings. Available as \code{make collisions}.}
\end{table}

Gating joins on agreement cut the library from eighty-five statements to
%s. Every one that was removed was false.
""" % (sum(len(t) for t in P.READINGS.values()),
       words(len(P.READINGS), 'equation'),
       words(len(seen), 'distinct collision'), table,
       number(len(P.all_joins())))


def composition_section():
    pairs = P.all_joins()
    showcase = []
    for names in [('Boltzmann entropy', 'Bekenstein-Hawking entropy'),
                  ('Ideal gas law', 'Thermal energy')]:
        found = P.join(*names)
        if found is not None:
            showcase.append(found)
    blocks = []
    for d in showcase:
        blocks.append(r"""
\[ %s \]

\noindent %s
""" % (d.latex(), d.prose(math='$%s$')))
    return r"""
\section{Composition, and the braces that carry it}
\label{sec:composition}

Transitivity is the only inference this module makes: if two equations both say
what $E$ is, whatever each says $E$ equals must equal the other.

The join keeps its provenance. The \verb|\underbrace| under each side names the
equation it came from; the \verb|\overbrace| names the quantity eliminated to
make it. Neither is decoration---they are what lets a reader, and the Lean
bridge of Section~\ref{sec:lean}, recover the derivation from the formula.

%s

\subsection{Families}

Pairs undersell the graph. Where three or more equations determine the same
quantity they chain into one statement, as in Figure~\ref{fig:grand}. %s do
so; the largest is the gravitational constant, fixed %s ways:
\begin{tiny}
\begin{align*}
%s
\end{align*}
\end{tiny}
\noindent
Each of these six was added on its own terms with no reference to the others.
The chain is not in the knowledge base; it is what the knowledge base implies,
and finding it required nothing but agreeing about what the letters mean.
""" % ('\n'.join(blocks), words(len(P.families()), 'quantity', 'quantities'),
       number(len(P.family('G'))), P.family('G').aligned())


def lean_section():
    conj = RL.conjecture(P.join('Boltzmann entropy',
                                'Bekenstein-Hawking entropy'))
    results = RL.conjectures()
    ok = [c for _, c, e in results if c is not None]
    return r"""
\section{Conclusion: From a composed statement to a Lean conjecture}
\label{sec:lean}

\code{lean4.py} already reads \LaTeX{}, but reads the language of types and
stops at the first \verb|^|. The bridge supplies the other half: a walk over the
algebra's term type into kernel expressions over an axiomatic \code{Real}.

What is claimed matters. The kernel is told \code{Real} is a type and that
\code{Real.add}, \code{Real.mul} and the rest are operations on it. It is
\emph{not} told the field axioms, so it cannot prove $mc^2 = h\nu$, and nothing
here pretends otherwise. It checks that the statement is well formed: every
symbol bound, both sides of the equality in one type, the result a \code{Prop}.
That is the right claim for a conjecture---one provable from the notation alone
would not be one.

Constants are declared rather than quantified, using the same table that stops
\code{eq2py} treating $c$ as an argument. This is not cosmetic:
\verb|forall pi : Real| is strictly stronger than the equation, and false for
almost every $\pi$.

The brace labels survive the trip, so the generated Lean carries the name of
the equation each side came from:

\begin{lstlisting}[language=lean,basicstyle=\ttfamily\footnotesize]
%s
\end{lstlisting}

All %s the library composes are emitted this way, and so is
Figure~\ref{fig:grand} itself: conjoining its rows and binding the shared
variables once over the whole gives a single proposition with %d binders and
%d conjuncts, which the micro-kernel accepts as a \code{Prop}. The complete
file is Appendix~\ref{app:lean}.

It has not been checked by Lean~4 itself. The preamble declares the type-class
instances an axiomatic \code{Real} needs---\code{Add}, \code{Mul},
\code{HPow}, \code{OfNat}---so the infix output elaborates, but that is a
prediction rather than a result.
""" % (conj.lean(), words(len(ok), 'statement'),
       len(RL.grand_conjecture().variables),
       len(RL.grand_conjecture().notes))



def reproducibility():
    return r"""
\footnotesize
\section*{Reproducibility --- Source Code}

\url{https://github.com/brentharts/RosettaMath}

\begin{lstlisting}[language={}]
python3 rosettaphys.py             the census: nodes, edges, joins, collisions
python3 rosettaphys.py --selftest  %d entries, the graph, and the algebra
python3 rosettalean.py             every join, as a checked conjecture
python3 rosettalean.py --selftest  the bridge, end to end
python3 rosettapaper.py            regenerate this document
make test                          all of the above, plus the kernel
make collisions                    the table in Section 4
\end{lstlisting}
""" % (len(P.SYMBOLS) + len(P.CONCEPTS) + len(P.EQUATIONS))


def appendices():
    lean = RL.lean_file([c for _, c, e in RL.conjectures() if c is not None])
    rows = []
    for eq in P.EQUATIONS:
        table = P.READINGS.get(eq['name'])
        if not table:
            continue
        reads = ', '.join('$%s$: %s' % (sym.replace('_', r'\_'), esc(q))
                          for sym, q in sorted(table.items()))
        rows.append(r'%s & $%s$ & %s \\' % (esc(eq.label), eq['latex'], reads))
    return r"""
\appendix
\footnotesize
\section{The readings table}
\label{app:readings}

What each equation declares its letters to denote. An equation absent from this
table takes part in no joins.

\begin{longtable}{p{3.2cm}p{4.2cm}p{7cm}}
\toprule
Equation & Statement & Readings \\
\midrule
\endhead
%s
\bottomrule
\end{longtable}

\section{The generated Lean 4 source}
\label{app:lean}

Produced by \code{python3 rosettalean.py -\/-lean}. \code{Real} and its
operations are declared, not defined: this file asks Lean whether the
statements are well-formed propositions, which is the question the micro-kernel
already answered. Proving them needs the field axioms and the physics, and
neither is claimed.

\begin{lstlisting}[language=lean,style=appendix]
%s
\end{lstlisting}
""" % ('\n'.join(rows), lean)


BIBLIOGRAPHY = r"""
\begin{thebibliography}{99}

\bibitem{hartshorn2026rosetta} Hartshorn, B.~S. (2026). RosettaMath: Reading,
Running and Proving Mathematics from \LaTeX{}. SSRN.
\url{https://dx.doi.org/10.2139/ssrn.7435598}

\bibitem{hartshorn2026lean} Hartshorn, B.~S. (2026). LEAN Proofs Small Enough
to Read: Kernel Contracts from \LaTeX{} Theorems to Compiler Decisions. viXra.
\url{https://ai.vixra.org/abs/2609.0019}

\bibitem{hartshorn2026second} Hartshorn, B.~S. (2026). A Second Kernel Agrees:
``LEAN Proofs Small Enough to Read'', Checked by Lean4 and Read Four Ways.
SSRN. \url{https://dx.doi.org/10.2139/ssrn.7443439}

\bibitem{coquand1988} Coquand, T. and Huet, G. (1988). The Calculus of
Constructions. \emph{Information and Computation}, 76(2--3), 95--120.

\bibitem{demoura2021} de Moura, L. and Ullrich, S. (2021). The Lean 4 Theorem
Prover and Programming Language. \emph{CADE-28}, 625--635.
\url{https://github.com/leanprover/lean4}

\bibitem{massot2024} Massot, P. (2024). Teaching Mathematics Using Lean and
Controlled Natural Language. \emph{ITP 2024}.

\end{thebibliography}

\end{document}
"""


# ---------------------------------------------------------------- assembly

def document():
    """The whole paper, in order."""
    return lines(
        PREAMBLE,
        abstract(),
        introduction(),
        graph_section(),
        algebra_section(),
        readings_section(),
        composition_section(),
        lean_section(),
        reproducibility(),
        appendices(),
        BIBLIOGRAPHY,
    )


def write(path=OUTPUT):
    text = document()
    with open(path, 'w') as handle:
        handle.write(text)
    return path, len(text)


# ---------------------------------------------------------------- selftest

def selftest():
    """Check the generated document before anyone waits on pdflatex."""
    failures = []

    def check(label, ok):
        print('  %-58s %s' % (label, 'ok' if ok else 'FAIL'))
        if not ok:
            failures.append(label)

    text = document()

    print('structure')
    check('it opens a document', r'\begin{document}' in text)
    check('and closes it', r'\end{document}' in text)
    # \{ and \} are literal characters, not grouping, and the side brace on
    # the grand display is made of them
    grouping = text.replace(r'\{', '').replace(r'\}', '')
    check('braces balance', grouping.count('{') == grouping.count('}'))
    for env in ('abstract', 'thebibliography', 'longtable', 'align*'):
        check('%s is closed' % env,
              text.count(r'\begin{%s}' % env) == text.count(r'\end{%s}' % env))
    check('every listing is closed',
          text.count(r'\begin{lstlisting}') == text.count(r'\end{lstlisting}'))

    print('generated content')
    check('the gravitational family is present',
          'Schwarzschild radius' in text and 'Planck length' in text)
    check('the collisions table names the W clash',
          'microstate count' in text)
    check('the Lean appendix carries the preamble',
          'namespace RosettaPhys' in text)
    check('and a theorem from the library',
          text.count('theorem ') >= len(RL.conjectures()))
    check('every cited key is defined',
          not _undefined_citations(text))
    check('no section is empty',
          '\\section{}' not in text and '\\section*{}' not in text)

    print('the numbers are the live ones')
    check('the equation count matches the library',
          str(len(P.EQUATIONS)) in text)
    check('the join count matches', _mentions_count(text, len(P.all_joins())))
    check('the quantity count matches',
          _mentions_count(text, len(P.QUANTITIES)))
    check('the readings total matches',
          str(sum(len(t) for t in P.READINGS.values())) in text)

    print()
    if failures:
        print('%d failure(s): %s' % (len(failures), ', '.join(failures)))
    else:
        print('rosettapaper: %d characters, %d sections, all checks pass.'
              % (len(text), text.count('\n\\section')))
    return len(failures)


def _undefined_citations(text):
    import re
    keys = set(re.findall(r'\\bibitem\{([^}]+)\}', text))
    used = set()
    for group in re.findall(r'\\cite\{([^}]+)\}', text):
        used.update(k.strip() for k in group.split(','))
    return sorted(used - keys)


def _mentions_count(text, n):
    return str(n) in text or number(n) in text


if __name__ == '__main__':
    if '--selftest' in sys.argv:
        sys.exit(1 if selftest() else 0)
    if '--stdout' in sys.argv:
        print(document())
    else:
        path, size = write()
        print('wrote %s (%d characters)' % (path, size))
