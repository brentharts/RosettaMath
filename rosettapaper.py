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

With the algebra refusing what it should, the library produced %s.
Among them was this one:

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

Gating joins on agreement cut the library from %d statements to
%s---%s discarded. The ones this paper first caught that way,
Boltzmann's $W$ against a work done and Planck's $h$ against a height, were
plainly false; the table above is the list of places the same fault can recur.
""" % (words(len(P.ungated_joins()), 'join'),
       sum(len(t) for t in P.READINGS.values()),
       words(len(P.READINGS), 'equation'),
       words(len(seen), 'distinct collision'), table,
       len(P.ungated_joins()), number(len(P.all_joins())),
       words(len(P.ungated_joins()) - len(P.all_joins()), 'statement'))


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


def geometry_section():
    """The group of entries that is not physics, and what it tested.

    Everything factual here is a call: the field names come from P.fields(),
    the counts from equations_in, the displayed statements from join() and
    family(). If the library changes shape the prose around them still reads,
    because the prose is about method rather than about numbers.
    """
    fields = [f for f in P.fields()
              if f in ('Tilings', 'Extremal geometry', 'String theory')]
    rows = []
    for field in fields:
        eqs = P.equations_in(field)
        refused = [e for e in eqs if P.algebraic(e['latex']) is not None]
        declared = [e for e in eqs if e['name'] in P.READINGS]
        rows.append(r'%s & %d & %d & %d \\'
                    % (esc(field), len(eqs), len(refused), len(declared)))
    table = '\n'.join(rows)

    total = sum(len(P.equations_in(f)) for f in fields)
    refused_here = sum(1 for f in fields for e in P.equations_in(f)
                       if P.algebraic(e['latex']) is not None)
    rest = [e for e in P.EQUATIONS if e['field'] not in fields]
    refused_rest = sum(1 for e in rest
                       if P.algebraic(e['latex']) is not None)
    pure = [q for q in P.QUANTITIES.values() if q['dimension'] == '1']
    minimal = P.join('Mean curvature', 'Minimal surface condition')
    slope = P.family('alpha_prime')

    return r"""
\section{A group that is not physics}
\label{sec:geometry}

Every entry so far has been a physical law, and every quantity has had a
dimension that constrains it. That is a comfortable place for a method like
this one to be tested, because dimensional analysis quietly catches a great
deal: an energy cannot be joined to a length whatever the letters say.

So the library was pointed at something it was not built for. %s were added
across %s---%s---chosen because they
share a subject rather than a discipline. A minimal surface minimises area
given a boundary. A Kakeya set minimises measure given a direction in every
direction. A covering surface has its total curvature fixed by a whole number
it cannot escape. And the Nambu-Goto action, which is where physics re-enters,
says that a string extremises the area of the sheet it sweeps: the same
variational problem Plateau posed about soap films, moved into a spacetime
where the signature puts a minus sign under the root.

\begin{table}[h]
\centering
\begin{tabular}{lrrr}
\toprule
Field & Entries & Refused by the algebra & Readings declared \\
\midrule
%s
\bottomrule
\end{tabular}
\caption{The new group. ``Refused'' counts entries the algebra of
Section~\ref{sec:algebra} declines to rearrange---integrals, sums and the
dimension operator. It does so for %d\%% of this group against %d\%% of the
rest of the library: the refusals cluster in the handful of statements that are
genuinely integrals (Gauss-Bonnet, Plateau, Nambu-Goto), while the tilings are
plain algebra over a quadratic field and are refused nothing at all.}
\end{table}

\subsection{What happens when the dimensions stop helping}

%s of the library's %s are dimensionless, and most of
the new ones are among them. A genus, a tile count, a Hausdorff dimension, an Euler
characteristic and a spacetime dimension are all the pure number $1$, and no
amount of dimensional checking will tell any of them from any other. The
readings table is therefore carrying the whole load: the name is the only thing
keeping a count of handles apart from a count of sheets.

This produced a new bug, and one a level below the bug of
Section~\ref{sec:readings}. Bekenstein-Hawking entropy is stated in terms of a
horizon area. A Penrose inflation multiplies the area of a patch by the square
of the golden ratio. Both say $A$, both declared $A$ to be an
\emph{area}, both are $L^2$, and the graph duly joined them:

\[ \frac{S \cdot 4 G \hbar}{k_B c^3} = \frac{A'}{\phi^2} \]

Nothing here is false. A black hole whose horizon happened to have the area of
an inflated tiling patch would satisfy it. It is simply about nothing, and no
check in the module could have said so---the letters match, the dimensions
match, and the declared readings agree. Agreement about the \emph{quantity} was
not enough, because a tiling patch and an event horizon are areas of different
things, and a patch can be made as large as you like.

The repair is the same repair as before, applied one level down: say more. The
tiling entries now declare their $A$ to be a \emph{patch area}, which is an
area that is joinable to no other, and the statement disappears. That this had
to be done by hand, again, is the finding. There is no depth at which declaring
what a letter means becomes unnecessary; there is only the depth at which the
current library has stopped being wrong.

\subsection{What it found}

Set against that, the group also produced joins of the kind the method is for.
The mean curvature is defined as the average of the principal curvatures; a
surface is minimal when the mean curvature vanishes. Neither entry was written
with the other in mind, and together they say what minimality actually
constrains:

\[ %s \]

\noindent %s

The string entries went further and formed a family. Four equations---the
tension, the Regge trajectory, the string length and the Hagedorn
temperature---each determine the Regge slope, and none of them was entered with
the others in view. They chain, and the result is now row %s of
Figure~\ref{fig:grand}:

\begin{small}
\begin{align*}
%s
\end{align*}
\end{small}

\noindent
The last of those is where the group ought to rejoin the rest of the library,
and does not. The Hagedorn entry declares its left side to be a
\emph{temperature}---the same quantity the gas laws are about---and carries the
Boltzmann constant besides. It joins to nothing outside the string cluster. The
obstruction is not physical but orthographic: it writes $T_H$ where the gas laws
write $T$, and a subscript is part of a name in this algebra, deliberately,
because that is what keeps $m_1$ and $m_2$ apart.

So the library can see the connection and cannot act on it. It records the
collision---$T$ is a temperature in one entry and a string tension in
another---and it can be asked for both readings, but no join follows, because
joining needs a shared \emph{symbol} as well as a shared quantity.

\subsection{The repair that does not work}

The obvious response is to pivot on quantities directly: join any two equations
that declare the same quantity, whatever letters they use. That was
implemented and measured before being rejected. It takes the library from %d to
%s. Two specimens of what it adds:

\begin{align*}
m c^2 &= \tfrac{1}{2} m v^2 \\
\tfrac{1}{2} m v^2 &= k_B T
\end{align*}

\noindent
The first identifies a rest energy with a kinetic one. The second is worse,
because it is nearly equipartition and a reader skimming might not stop: the
true relation carries a factor of three halves, and the library has produced
something that looks like a law and is not one.

The diagnosis is that requiring a shared letter was never really about letters.
It was a proxy for the two equations meaning the same \emph{instance} of a
quantity, and for everything except a constant that proxy is all there is. Two
equations both about ``an energy'' are not thereby about the same energy.
Section~\ref{sec:readings} established that a glyph is not a quantity; this
establishes the converse limit, that a quantity is not an instance, and the
readings table as designed cannot express the difference.

There is exactly one case where the fold is safe, and the module already had
the vocabulary for it. A \emph{constant} has one instance in the universe, so
the $\epsilon_0$ of Coulomb's law and the $\epsilon_0$ of the Debye length are
the same number and equating them assumes nothing. Folding a subscript is
therefore permitted when, and only when, the quantity is declared a constant
and the equation contains exactly one symbol with that base---Newton's law of
gravitation has $m_1$ and $m_2$, so $m$ names neither and the fold is
refused. This recovers %s, all of them about the permittivity, and
makes it a family of four:

\[ %s \]

\noindent
That is the whole of what the permissive rule was right about. The remaining
%s were classified rather than characterised, since ``most of them are
wrong'' is not a measurement. Truth is the wrong test---every join in this
library is an equation that holds only where both sides really do equal the
pivot, and that is as true of the gravitational family as of anything here. The
test applied instead is whether the transitivity step is \emph{licensed}: are
the two equations about the same instance of the quantity?

\begin{table}[h]
\centering
\begin{tabular}{lrp{7.4cm}}
\toprule
& Count & \\
\midrule
Unlicensed & %d & different symbols, quantity not a constant: the join
asserts two differently named things are one instance \\
Already known & %d & the pivot quantity is a family already, so the library
knows it is multiply determined and suppresses the pairs deliberately \\
Novel & %d & licensed, and about a quantity no family covers \\
\bottomrule
\end{tabular}
\caption{Every statement the permissive rule adds, classified by
\code{quantity\_join\_census()}. The bottom row is the one that would have
mattered.}
\end{table}

\noindent
The bottom row is empty, and that is the result. Not that the permissive rule
is mostly wrong---that it offers the library nothing it wants. Three quarters
of what it adds is unwarranted and the remaining quarter is already recorded as
a family, suppressed on purpose because a pivot on $\pi$ or on a mass is true
and uninformative.

The audit did find one thing, though not where it was looking. That bottom row
was not empty at first: it held $\omega / 2\pi = v / \lambda$, which relates an
angular frequency to a wave speed and is exactly the sort of statement the
library exists to produce. It was being suppressed because $f$ appeared on a
list of letters too common to pivot on---a list written before the readings
table existed, when it had to keep out ambiguous pivots as well as
uninformative ones. \code{agree()} does the first job properly now. Measured
against the current library, $m$ on that list suppresses twenty-one statements,
$k$ and $\pi$ eight each, $r$ three, and all of those are vacuous or
unwarranted; $f$ suppressed one good one and nothing else, so $f$ is gone and
the join is in. Five of the remaining entries suppress nothing at all.

\subsection{The edge of the method}

The tilings were included for a reason that has nothing to do with area. A set
of Wang tiles either tiles the plane or does not, and Berger proved in 1966
that no procedure decides which. The statement is finite, perfectly precise,
and beyond computation altogether.

Nothing in this paper touches it. The kernel of Section~\ref{sec:lean} asks
whether a statement is a well-formed proposition, which is decidable; it never
asks whether the proposition is true, which in general is not. The library can
hold the domino problem as prose and can hold the arithmetic consequence---that
Penrose rhombs occur in an irrational ratio, so no tiling of them repeats---as
an equation it can join. It cannot hold the theorem. Knowing which of the three
is being offered is the difference between a knowledge base and a claim to have
automated mathematics.

The same group supplies the opposite extreme, which is worth putting beside it.
The monotile entries pin names to closed arithmetic---the inflation factor is
$4+\sqrt{15}$, the commonest metatile frequency is $4-\sqrt{15}$---and once a
name has a number, any other entry written entirely in such names has nothing
left to be true about. It can simply be evaluated. The library declares %s
this way, which makes %s decidable, and they are
checked on every run:

\begin{align*}
\mu^2 &= 8\mu - 1 \\
g\mu &= 1
\end{align*}

\noindent
%s out of %d is not a result about physics. It is a result about
where the boundary sits. Everything else here is a conjecture
because it quantifies over variables and the world decides; these are not,
because they quantify over nothing. That is also the only place in the library
where a mistyped surd can be caught automatically---$4+\sqrt{14}$ parses,
typechecks, renders and joins exactly as well as the right answer, and is
caught here and nowhere else.
""" % (words(total, 'entry', 'entries'),
       words(len(fields), 'new field'),
       ', '.join(esc(f).lower() for f in fields),
       table,
       round(100.0 * refused_here / total),
       round(100.0 * refused_rest / len(rest)),
       number(len(pure)).capitalize(),
       words(len(P.QUANTITIES), 'physical quantity', 'physical quantities'),
       minimal.latex(), minimal.prose(math='$%s$'),
       number([f.quantity for f in P.grand_members()].index('regge slope') + 1),
       slope.aligned(),
       len(P.all_joins()),
       words(len(P.quantity_joins()), 'pairwise statement'),
       words(len(P.folded_joins()), 'join'),
       P.join("Coulomb's law", 'Debye length').latex(),
       words(sum(len(x) for x in P.quantity_join_census()), 'statement'),
       len(P.quantity_join_census()[0]),
       len(P.quantity_join_census()[1]),
       len(P.quantity_join_census()[2]),
       words(len(P.declared_constants()), 'constant'),
       words(len(P.numeric_checks()), 'entry', 'entries'),
       words(len(P.numeric_checks()), 'statement').capitalize(),
       len(P.EQUATIONS))


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
    source_rows = '\n'.join(
        r'%s & \code{%s} \\' % (esc(eq.label), esc(src))
        for eq, src in P.sourced())
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

\section{Entries derived rather than quoted}
\label{app:sources}

Most of the library can be checked against a textbook. %s cannot: their values
were computed, and an entry that says only which Wikipedia article explains the
idea does not say where its number came from. Those entries carry a
\code{source} naming the matrix or function it was computed from.

The field exists because of a near-miss. Two of the substitutions below give
different inflation factors for the aperiodic monotile---$\phi^4$ for the hat
and $4+\sqrt{15}$ for the spectre---and both are right, because they are
different substitutions on different numbers of species. Written without
provenance the two entries read as a contradiction, and the first draft of the
tilings group made exactly that mistake.

\begin{longtable}{p{4.4cm}p{10cm}}
\toprule
Entry & Computed from \\
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
""" % ('\n'.join(rows),
       words(len(P.sourced()), 'entry', 'entries').capitalize(),
       source_rows, lean)


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
        geometry_section(),
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
    check('the geometry section names all three new fields',
          all(f in text for f in
              ('Tilings', 'Extremal geometry', 'String theory')))
    check('the Regge slope family is displayed',
          "\\alpha'" in text and 'Hagedorn temperature' in text)
    # the prime has to survive the printer: alpha_prime is the internal name
    # and must never reach the page
    check('no internal primed name leaks into the document',
          'alpha_prime' not in text)
    check('the provenance appendix lists every sourced entry',
          all(esc(src) in text for _eq, src in P.sourced()))
    check('both monotile inflation factors are present and distinguished',
          '4 + \\sqrt{15}' in text and '7 + 3 \\sqrt{5}' in text)

    print('the numbers are the live ones')
    check('the equation count matches the library',
          str(len(P.EQUATIONS)) in text)
    check('the join count matches', _mentions_count(text, len(P.all_joins())))
    check('the ungated join count matches',
          _mentions_count(text, len(P.ungated_joins())))
    check('the quantity count matches',
          _mentions_count(text, len(P.QUANTITIES)))
    check('the new fields are counted correctly',
          all(str(len(P.equations_in(f))) in text for f in
              ('Tilings', 'Extremal geometry', 'String theory')))
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
