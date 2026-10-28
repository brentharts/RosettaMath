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
import rosettaym as Y
import rosettaoai as OAI
import rosettacicy as CI
import rosettaspectre as SP
import rosettanariai as NR

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
Each statement is checked to be a well-formed proposition over an axiomatic \code{Real} by a Calculus of
Constructions micro-kernel, then emitted as Lean~4.
\end{abstract}
""" % (words(len(P.EQUATIONS), 'equation'), words(len(P.SYMBOLS), 'symbol'),
       words(len(P.QUANTITIES), 'physical quantity', 'physical quantities'),
    )


# ---------------------------------------------------------------- sections

def introduction():
    fams = P.grand_members()
    terms = sum(len(f) for f in fams)
    return r"""

\begin{figure}[htbp]
\centering
\resizebox{0.8\textwidth}{!}{$\displaystyle %s $}
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

The library has since taken on work that is not the author's. Its lattice gauge
theory group (Section~\ref{sec:lattice}) is drawn from the Yang--Mills Mass Gap
Laboratory of Elsbernd \cite{elsbernd2026}: %s of its entries name the
function in that code which they describe, and a bridge module puts the same
numbers through the library's algebra and through the code and compares them.

Yang--Mills theory is where those borrowings meet. Section~\ref{sec:ym} gathers
what five repositories say about it---the laboratory, a fork of an OpenAI
mathematics release, CICY, and two on the Spectre monotile---into a second
generated display, Figure~\ref{fig:grandym}, in which a quantity is equated
across repositories only where they all state it, and joined by an arrow where
they state something similar about a different system.

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
       len(RL.grand_conjecture().variables),
       number(len(P.cited(Y.REFERENCE))))


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
\tiny
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
\tiny
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
\tiny
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


FIELD = 'Lattice gauge theory'


def _ratio(x):
    return '%.4f' % x


def _error(x):
    return '0' if x == 0 else '%.1e' % x


def lattice_section():
    """The first group whose provenance is another person's code.

    What is claimed about the laboratory is generated from the laboratory: the
    table of results is read out of its committed campaign, and every
    agreement between it and the library is a number returned by
    rosettaym.checks().  When ymlab is not on the machine building the paper
    the section says so and prints nothing it could not have measured.
    """
    eqs = P.equations_in(FIELD)
    cited = P.cited(Y.REFERENCE)
    refused = [e for e in eqs if P.algebraic(e['latex']) is not None]
    here = set()
    for e in eqs:
        here.update(P.READINGS.get(e['name'], {}).values())
    elsewhere = set()
    for e in P.EQUATIONS:
        if e['field'] != FIELD:
            elsewhere.update(P.READINGS.get(e['name'], {}).values())
    fresh = sorted(here - elsewhere)
    names = {e['name'] for e in eqs}
    joins = [d for d in P.all_joins()
             if any(s.equation['name'] in names for s in d.steps)]
    pure = [d for d in joins
            if all(s.equation['name'] in names for s in d.steps)]
    tension = P.GRAPH.edge_between(P.GRAPH.find('Area law', 'equation'),
                                   P.GRAPH.find('String tension', 'equation'))
    refused_join = (P.join('Area law', 'String tension') is None
                    and P.join('Creutz string tension',
                               'String tension') is None)

    head = r"""
\section{A group whose source is somebody else's code}
\label{sec:lattice}

Everything in the library so far was entered by its author, from a textbook or
from his own earlier work. The last group is different, and the difference is
what is being tested: %s were drawn from the Yang--Mills Mass Gap
Laboratory of Elsbernd \cite{elsbernd2026}, a finite-lattice $SU(2)$ and
$SU(3)$ simulation package with its own test suite, and %s of them carry a
\code{source} naming the function they describe.

That field was introduced for a modest reason---two monotile inflation factors
that looked contradictory until each said which matrix it came from---and it
turns out to be the right place to record a stronger claim. A source of the form
``this equation is what that function computes'' is checkable. The tilings could
only be re-derived; the laboratory can be \emph{run}.

The laboratory is explicit about what it is, and so is this paper. It is a
numerical study of gauge theory on small periodic lattices. It does not
construct the continuum four-dimensional theory, and it does not prove a
positive mass gap, which is what the Clay problem asks. Nothing below is
evidence about that problem. What is described is a smaller thing: a knowledge
base and a body of working code agreeing, to machine precision, about what a
handful of formulas mean.

The group has %d entries and %d readings. Of the quantities it reads, %s are
read by no other entry: %s. %s of the %d are refused by the algebra of
Section~\ref{sec:algebra}, being sums, integrals or hatted operators; the rest
can be rearranged and so can be joined.
""" % (
        words(len(cited), 'entry', 'entries').capitalize(),
        number(len(cited)),
        len(eqs), sum(len(P.READINGS.get(e['name'], {})) for e in eqs),
        number(len(fresh)).capitalize(),
        ', '.join(r'\emph{%s}' % esc(q) for q in fresh),
        words(len(refused), 'entry', 'entries').capitalize(), len(eqs))

    if not Y.available():
        return head + r"""
\subsection{Checks against the code}

The laboratory was not found on the machine that built this document, so no
comparison is printed. Set \code{YMLAB\_DIR} to a checkout of it and rebuild;
\code{python3 rosettaym.py --selftest} runs the same comparisons from the
terminal.
"""

    results = Y.checks()
    check_rows = '\n'.join(
        r'\code{%s} & %s & %s \\' % (esc(c.equation), esc(c.what),
                                      _error(c.error))
        for c in results)
    gap = Y.unchecked()

    run = Y.published_campaign()
    same = Y.determinism()
    table = Y.headline(run)
    cfg = run['config']
    env = run['environment']
    rows = []
    for (beta, label), row in sorted(
            table.items(), key=lambda kv: (kv[0][0],
                                           kv[1]['overrelaxation_sweeps'])):
        rows.append(r'%s & \code{%s} & %.2f & %.2f & %.2f & %.2f & %s \\'
                    % (('%g' % beta) if label == 'M' else '', esc(label),
                       row['mean_plaquette_tau_int'],
                       row['mean_scalar_tau_int'],
                       row['mean_plaquette_ess_per_second'],
                       row['mean_scalar_ess_per_second'],
                       _ratio(row['mean_scalar_efficiency_ratio_vs_metropolis'])))
    best = Y.best_schedules(run)
    plaq_all_m = all(b['plaquette']['schedule_label'] == 'M'
                     for b in best.values())
    wins = [(beta, b['scalar']['schedule_label'])
            for beta, b in sorted(best.items())
            if b['scalar']['schedule_label'] != 'M']
    cell = Y.aggregation(run=run)
    dirty = [r for r in Y.published_runs() if r['git'].get('dirty', True)]
    dirty_cell = Y.aggregation(run=dirty[0]) if dirty else None

    body = r"""
\subsection{Checks against the code}

Each check takes an equation from the library, lets the library's own
algebra---the reader, the rearranger and the evaluator of
Section~\ref{sec:algebra}---work out what it predicts for some numbers, and
puts the same numbers through the laboratory function the entry names. A
misprinted exponent in the library's \LaTeX{} would therefore show up as a
wrong number here and not as a pass. Table~\ref{tab:checks} gives the relative
difference for each; where it reads ``worst case'' the comparison is over every
chain in the laboratory's committed campaign.

\begin{table}[h]
\centering
\scriptsize
\begin{tabular}{p{3.6cm}p{8.2cm}r}
\toprule
Entry & What was compared & Difference \\
\midrule
%s
\bottomrule
\end{tabular}
\caption{The library against the laboratory, from \code{rosettaym.checks()}.
Differences are relative to the laboratory's value; ``0'' is exact agreement.
%s of the %s entries that cite the laboratory are covered%s.}
\label{tab:checks}
\end{table}

\subsection{The published result}

The laboratory's final study compares four update schedules for $SU(2)$:
one Metropolis sweep alone, and one Metropolis sweep followed by one, two or
four microcanonical overrelaxation sweeps. The lattice is $%s$, the bare couplings
are $\beta=%s$, and each condition is run from %s seeds for %s measured updates.
Table~\ref{tab:campaign} is read from the run in the laboratory's repository
that was made from a clean checkout (it was produced on %s %s with numpy~%s);
nothing in it is transcribed.

\begin{table}[h]
\centering
\scriptsize
\begin{tabular}{rlrrrrr}
\toprule
$\beta$ & Schedule & $\tau_{\mathrm{int}}$ plaq. & $\tau_{\mathrm{int}}$ scalar
& ESS/s plaq. & ESS/s scalar & Scalar ratio vs M \\
\midrule
%s
\bottomrule
\end{tabular}
\caption{The overrelaxation campaign of the laboratory \cite{elsbernd2026}:
mean integrated autocorrelation time $\tau_{\mathrm{int}}$ (in updates), mean
effective samples per second, and the paired scalar efficiency ratio against
Metropolis, as defined by the entries \code{Integrated autocorrelation time},
\code{Sampling efficiency} and \code{Efficiency ratio}.}
\label{tab:campaign}
\end{table}

%s%s

The point the study makes is a methodological one and the library can state it
exactly. The autocorrelation time is measured in updates and the efficiency in
seconds, and they are different quantities: the first is a property of the
chain and the seed, the second also of the machine. %s

\subsection{Two ways to summarise one cell}

The laboratory's paired ratio is the mean, over %s seeds, of per-seed ratios,
each taken against the Metropolis chain begun from the same configuration. At
$\beta=%g$ for the scalar observable and the \code{%s} schedule that is
$%s$. The other obvious summary---the schedule's mean efficiency divided by
Metropolis's mean efficiency---is $%s$ for the same cell. Both are defensible,
they answer slightly different questions, and they are not the same number.
Neither is a statement about the continuum, and with %s seeds neither is
precise; the point is only that a reader who quotes one should know the other.%s

\subsection{What the group refused}

The string tension that appears in the area law of a Wilson loop and the string
tension of string theory are both an inverse area, both written $\sigma$ or $T$,
and both called ``the string tension''. A flux tube between static charges is
modelled as a string, and in that model the two are related; whether the model
is exact is a research question and not a notational one. The library therefore
holds them as two quantities, \emph{confining string tension} and \emph{string
tension}, and the graph does not join them: %s The edge between the two entries
says why: ``%s''.

The same repair appears twice more. A horizon is an area and so is a Wilson loop,
which would have joined Bekenstein--Hawking entropy to the area law exactly as
Section~\ref{sec:geometry} found a tiling patch joined to it; the loop area is
declared as its own quantity, as the patch area was. And a Wilson loop is not a
microstate count although both are written $W$. That this had to be done by
hand again is not a surprise, and it is the same finding.

\subsection{What the group joined}

%s of the %s joins that involve the group are within it. Two of them are the
reason it exists:

%s

\subsection{Reproducing a chain}

\code{python3 rosettaym.py -\/-reproduce} thermalises one starting configuration
here and runs two schedules again, then compares with the published records.
It is slow, and its result depends on the machine, so this document does not
include it unless it is built with \code{ROSETTAPAPER\_REPRODUCE=1}.%s
""" % (
        check_rows,
        number(len(cited) - len(gap)).capitalize(), number(len(cited)),
        ('; not covered: ' + ', '.join(esc(g) for g in gap)) if gap else '',
        r'\times'.join(str(e) for e in cfg['shape']),
        ', '.join('%g' % b for b in cfg['betas']),
        number(len(cfg['seeds'])), cfg['measurement_updates'],
        esc(str(env.get('platform_system', '?'))),
        esc(str(env.get('platform_machine', '?'))),
        esc(str(env.get('numpy_version', '?'))),
        '\n'.join(rows),
        ('Plain Metropolis had the highest mean plaquette efficiency at every '
         'coupling. ' if plaq_all_m else
         'Plain Metropolis did not have the highest mean plaquette efficiency '
         'at every coupling. '),
        ('The scalar observable was won by a schedule other than Metropolis '
         'at ' + ', '.join(r'$\beta=%g$ (\code{%s})' % (b, esc(l))
                           for b, l in wins) + '.'
         if wins else
         'Metropolis had the highest mean scalar efficiency at every '
         'coupling.'),
        (('%s runs of this configuration are in the repository. Their '
          'autocorrelation times differ by at most %s and their effective '
          'samples per second by up to %.1f\\%%, which is exactly what the '
          'distinction predicts.')
         % (number(same['runs']).capitalize(),
            '%g' % same['max_tau_difference'],
            100 * same['max_ess_per_second_relative'])) if same else
        'Only one run of this configuration is in the repository.',
        number(cell['seeds']), cell['beta'], esc(cell['schedule']),
        _ratio(cell['mean_of_paired_ratios']),
        _ratio(cell['ratio_of_mean_efficiencies']), number(cell['seeds']),
        ((' A second run of the same configuration, made from an uncommitted '
          'tree, gives %s for the paired ratio; the clean run is the one '
          'quoted here, and the rule that chooses it is in '
          r'\code{rosettaym.published\_campaign()}.')
         % _ratio(dirty_cell['mean_of_paired_ratios'])) if dirty_cell else '',
        ('\\code{join} returns nothing for either pairing.' if refused_join
         else 'the join was not refused, and that is a bug.'),
        esc(tension.note) if tension is not None else '',
        number(len(pure)).capitalize(), number(len(joins)),
        '\n\n'.join(
            r'\[ %s \]' % d.latex() + '\n\n\\noindent ' + d.prose(math='$%s$')
            for d in _showcase_lattice_joins()),
        _reproduction_text())
    return head + body


def _showcase_lattice_joins():
    out = []
    for names in [('Effective sample size', 'Sampling efficiency'),
                  ('Area law', 'Creutz string tension')]:
        found = P.join(*names)
        if found is not None:
            out.append(found)
    return out


def _reproduction_text():
    """The live comparison, only when asked for."""
    if not os.environ.get('ROSETTAPAPER_REPRODUCE'):
        return ''
    got = Y.reproduce()
    if got is None:
        return ''
    lines = []
    for r in got['rows']:
        gap = abs(r['scalar_tau_here'] - r['scalar_tau_published']) \
            / r['scalar_tau_published']
        lines.append(r'The \code{%s} chain at $\beta=%g$, seed %d, gave a '
                     r'scalar $\tau_{\mathrm{int}}$ of %.6f against %.6f '
                     r'published (%s); its runtime was %.1f\,s here and '
                     r'%.1f\,s there.'
                     % (esc(r['schedule']), got['beta'], got['seed'],
                        r['scalar_tau_here'], r['scalar_tau_published'],
                        'identical to rounding' if gap < 1e-9 else
                        'a difference of %.0f\\%%' % (100 * gap),
                        r['runtime_here'], r['runtime_published']))
    return '\n\n' + '\n'.join(lines)


# ------------------------------------------------- Yang--Mills, five repositories

YM_KEYS = ('elsbernd2026', 'openai2026', 'cicy2026', 'spectre2026',
           'nariai2026')

# Figures the section draws from the repositories' own output.  They are
# copied next to the .tex when it is written, never regenerated here: a figure
# in this paper is what that repository's code produced, and says so.
FIGURES = {
    'on_model_mc': ('openai', 'build/figures/on_model_mc.pdf'),
    'kt_flow': ('openai', 'build/figures/kt_flow.pdf'),
    'on_local_slopes': ('ymlab', 'results/figures/findings/on_local_slopes.pdf'),
    'su2_slopes': ('ymlab', 'results/figures/findings/su2_slopes.pdf'),
}


def fill(text, **values):
    """Substitute @name@ tokens.  LaTeX is full of braces and percent signs,
    so the prose is written with tokens instead of format specifiers."""
    for key, value in values.items():
        text = text.replace('@%s@' % key, str(value))
    import re
    left = re.findall(r'@[A-Za-z_0-9]+@', text)
    if left:
        raise ValueError('unfilled tokens in the Yang-Mills section: %s' % left)
    return text


def _figure_root(which):
    return OAI.locate() if which == 'openai' else Y.locate()


def figure_source(name):
    which, rel = FIGURES[name]
    root = _figure_root(which)
    path = os.path.join(root, rel) if root else None
    return path if path and os.path.exists(path) else None


def stage_figures(directory):
    """Copy the available figures to <directory>/figures/; return their names."""
    import shutil
    staged = []
    for name in FIGURES:
        source = figure_source(name)
        if source is None:
            continue
        target = os.path.join(directory, 'figures')
        os.makedirs(target, exist_ok=True)
        shutil.copyfile(source, os.path.join(target, name + '.pdf'))
        staged.append(name)
    return staged


def _graphic(name, width):
    if figure_source(name) is None:
        return ''
    size = width if '=' in width else 'width=' + width
    return r'\includegraphics[%s]{figures/%s.pdf}' % (size, name)


def _entry_tex(name):
    return P.GRAPH.find(name, 'equation')['latex']


def _bridge_rows():
    """One row per repository: what cites it, and what its bridge measured."""
    def closed(module):
        return module._check_closed_forms()

    runners = {
        'elsbernd2026': lambda: Y.checks() if Y.available() else None,
        'openai2026': lambda: OAI.checks(),
        'cicy2026': lambda: (closed(CI) + CI.checks()) if CI.available() else None,
        'spectre2026': lambda: (closed(SP) + SP.checks()) if SP.available() else None,
        'nariai2026': lambda: (closed(NR) + NR.checks()) if NR.available() else None,
    }
    rows = []
    for key in YM_KEYS:
        try:
            results = runners[key]()
        except Exception:
            results = None
        ref = P.REFERENCES[key]
        row = {'key': key, 'tag': ref['tag'], 'repo': ref['repo'],
               'entries': len(P.cited(key)), 'ran': results is not None}
        if results:
            row.update(checks=len(results), ok=all(c.ok for c in results),
                       worst=max(c.error for c in results))
        rows.append(row)
    return rows


_FACTS = {}


def ym_facts():
    """Every number the Yang--Mills section quotes, from the repositories."""
    if _FACTS:
        return _FACTS
    facts = {'bridges': _bridge_rows()}
    try:
        facts['af'] = OAI.asymptotic_freedom()
        facts['kt'] = OAI.data('kt_flow')
        facts['bloch'] = OAI.data('bloch_law')
        facts['haldane'] = OAI.haldane()
    except Exception:
        facts['af'] = facts['kt'] = facts['bloch'] = facts['haldane'] = None
    facts['ymlab'] = None
    if Y.available():
        try:
            import importlib
            findings = importlib.import_module('ymlab.findings')
            facts['ymlab'] = findings.on_comparison()
        except Exception:
            facts['ymlab'] = None
    if CI.available():
        facts['spot'] = CI.blind_spot()
        facts['alpha3'] = {}
        couplings = CI.load()[1]
        for label, b in (('MSSM', CI.MSSM), ('Standard Model', CI.SM)):
            inv = CI.predicts('Unification prediction', {
                'alpha_1': 1.0 / couplings.ALPHA1_INV_MZ,
                'alpha_2': 1.0 / couplings.ALPHA2_INV_MZ,
                'b_1': b[0], 'b_2': b[1], 'b_3': b[2]})
            facts['alpha3'][label] = 1.0 / inv
        facts['alpha3_measured'] = couplings.ALPHA3_MZ
    facts['hat'] = SP.hat_three_ways() if SP.available() or CI.available() else None
    facts['homogeneous'] = SP.homogeneous_species() if SP.available() else None
    facts['matrix'] = NR.matrix_comparison() if NR.available() else None
    _FACTS.update(facts)
    return _FACTS


def _table(header, rows, align):
    return (r'\begin{tabular}{%s}' '\n' r'\toprule' '\n%s \\\\\n' r'\midrule' '\n%s\n'
            r'\bottomrule' '\n' r'\end{tabular}'
            % (align, ' & '.join(header), '\n'.join(' & '.join(r) + r' \\' for r in rows)))


def _ym_overview(f):
    members = P.grand_yang_mills_members()
    links = P.cross_repository_links()
    terms = sum(len(m) for m in members)
    nvars = len(RL.grand_conjecture(P.YM_PIVOTS, name='yang_mills').variables)
    counts = {k: len(P.cited(k)) for k in YM_KEYS}
    ran = [r for r in f['bridges'] if r['ran']]
    return fill(r"""
\clearpage
\section{Yang--Mills across five repositories}
\label{sec:ym}

Yang--Mills theory is a thread that runs through more code than one author's,
and the library now holds entries from five repositories that touch it. The
laboratory of Elsbernd \cite{elsbernd2026} contributes @ymlab@ entries on the
lattice theory itself. A fork of an OpenAI mathematics release
\cite{openai2026} contributes @openai@ entries on the spin models and
renormalisation-group flows that its manuscripts use as toys for gauge theory.
CICY \cite{cicy2026}, a Calabi--Yau toolkit, contributes @cicy@ entries on the
running of the gauge couplings and on the Hat monotile. The last two,
\texttt{spectre} \cite{spectre2026} and \texttt{nariai} \cite{nariai2026}, are
about a tiling, and are here because the arithmetic of the Spectre can be put
beside CICY's arithmetic of the Hat and agrees with it; they are not
Yang--Mills and the section does not pretend otherwise.

\begin{figure}[!htbp]
\centering
\resizebox{0.98\textwidth}{!}{$\displaystyle %s $}
\caption{\tiny Yang--Mills across the repositories, conjoined. The upper rows
are identities: a quantity, \texttt{\textbackslash overbrace}d with what it is,
equal to what each of @terms@ equations from the library says it is, each
\texttt{\textbackslash underbrace}d with the equation and the repository it
came from. The lower rows are correspondences, read from the graph's
@nlinks@ cross-repository links: two equations that say related things about
different systems, joined by an arrow rather than an equals sign. Generated by
\code{rosettaphys.grand\_yang\_mills()}; the identities alone, with their
@nvars@ variables bound once, elaborate to a single proposition through
\code{rosettalean.grand\_conjecture}.}
\label{fig:grandym}
\end{figure}

Figure~\ref{fig:grandym} is to Yang--Mills what Figure~\ref{fig:grand} is to the
whole library, and it is built the same way: nothing in it was written down as a
display. The rows are \emph{chosen} (\code{rosettaphys.YM\_PIVOTS}), because
every family in the library does not fit on a page and because some would
equate things that are only analogous; what each row \emph{says} is whatever the
equations declare. The top row is the thread from the lattice to the running of
the coupling: the lattice coupling $\beta = 2N/g^2$ and the one-loop coefficient
of the ordinary theory both state the number of colours, so each is solved for
$N$ and the two are equated. The one-loop coefficient of the supersymmetric
theory states it too and is left out on purpose, because equating what two
different theories say about $N$ is a claim about neither. The arrows are
where the library declines to equate. The exponent of asymptotic freedom in the
spin model and the exponent of dimensional transmutation in the gauge theory
have the same shape; the laboratory and the spin model both state a lattice
mass; the second-moment length is a mass but not in general the transfer-matrix
gap. Each link carries a note saying in what sense, and Table~\ref{tab:bridges}
lists what each repository's bridge measured.

\begin{table}[!htbp]
\centering
\small
%s
\caption{The bridges. \emph{Entries} cite the repository; \emph{checks} are
comparisons the bridge ran between the library's algebra and the code
(\code{python3 rosetta<repository>.py}); \emph{worst} is the largest relative
error among them. A repository that is not on the machine building the paper is
reported as not run, and nothing is printed for it that could not have been
measured.}
\label{tab:bridges}
\end{table}
""" % (P.grand_yang_mills(), _table(
        ['repository', 'entries', 'checks', 'worst', 'status'],
        [[r'\code{%s}' % esc(r['tag']), str(r['entries']),
          str(r['checks']) if r['ran'] else '--',
          ('%.1e' % r['worst']) if r['ran'] else '--',
          ('all agree' if r['ok'] else 'DISAGREE') if r['ran'] else 'not run']
         for r in f['bridges']], 'lrrrl')),
        ymlab=number(counts['elsbernd2026']), openai=number(counts['openai2026']),
        cicy=number(counts['cicy2026']), terms=terms, nlinks=len(links),
        nvars=nvars)


def _ym_asymptotic(f):
    af = f['af']
    yl = f['ymlab']
    if af is None and yl is None:
        return r"""
\subsection{Asymptotic freedom}

Neither the fork's computations nor the laboratory's findings were found on the
machine that built this document, so no measured slopes are printed here;
\code{python3 rosettaoai.py} prints them.
"""
    text = [fill(r"""
\subsection{From the lattice toward the continuum: asymptotic freedom}
\label{sec:ym:af}

A positive mass gap in the continuum needs the lattice mass, in lattice units,
to go to zero in the right way as the coupling is tuned: $a\,m_{\mathrm{phys}}$
fixed while $a\to 0$. The theory that makes this plausible is asymptotic
freedom, and the library states it twice. For the two-dimensional $O(N)$
models, $N\ge 3$,
\[ @af@ , \]
and for a gauge theory the running of the coupling gives
\[ @tr@ , \qquad @qcd@ , \]
where the sign of $b$ is what makes the exponent negative. The two exponentials
have one shape: $2\pi$ times an inverse coupling over a positive one-loop
coefficient, $N-2$ in the spin model and $|b|$ in the gauge theory. In the
normalisation $b_0 = |b|/16\pi^2$ and $\alpha = g^2/4\pi$ the gauge exponent
$2\pi/(|b|\alpha)$ is $1/(2 b_0 g^2)$, which sympy confirms in the laboratory's
tests. Demanding a fixed physical mass $m_{\mathrm{lat}} = a\,m_{\mathrm{phys}}$
at spacing $a$ in the $N=3$ form gives
\[ \ln\frac{1}{a} = 2\pi\beta - \ln\beta - \ln\frac{C}{m_{\mathrm{phys}}} , \]
so $\beta(a) = \tfrac{1}{2\pi}\ln\tfrac1a + O(\ln\ln\tfrac1a)$: the coupling
must drift logarithmically as the spacing shrinks, which is the statement that
the continuum limit sits at infinite $\beta$ \cite{openai2026}. This is the
same shape as the trajectory the fork's manuscript builds; the script does not
reproduce that construction, and says so.
""", af=_entry_tex('Asymptotic-freedom mass scaling'),
        tr=_entry_tex('Dimensional transmutation'),
        qcd=_entry_tex('One-loop coefficient (QCD)'))]

    if af:
        rows = []
        for n, r in sorted(af.items()):
            rows.append(['$O(%d)$' % n, '%.2f--%.2f' % r['beta'],
                         '%.2f' % r['fit_slope'], '%.2f' % r['leading_slope'],
                         '%.2f' % r['ratio']])
        graphic = _graphic('on_model_mc', r'0.95\textwidth')
        onmc_figure = (
            '\\begin{figure}[!htbp]\n\\centering\n%s\n\\caption{Left: second-moment '
            'correlation length against $\\beta$ for $O(3)$ and $O(4)$, with the '
            'asymptotic-freedom form matched at the first point. Right: '
            '$R_N=\\xi\\,\\beta^{-1/(N-2)}e^{2\\pi\\beta/(N-2)}$, which flattens at '
            'large $\\beta$ if asymptotic scaling holds; the dotted line is the '
            "constant in the fork's $O(4)$ transfer-gap formula. Figure produced "
            "by the fork's \\code{tools/on\\_model\\_mc.py}.}\n"
            '\\label{fig:onmc}\n\\end{figure}') % graphic if graphic else ''
        text.append(fill(r"""
The fork's Wolff Monte Carlo \cite{openai2026} measures the second-moment
correlation length $\xi^2 = (\chi/F - 1)/p^2$ with $p = 2\sin(\pi/L)$ on
$L\times L$ tori. Table~\ref{tab:af} compares the fitted slope of
$\ln\xi + \tfrac{1}{N-2}\ln\beta$ against $\beta$ with the leading
asymptotic-freedom value. The simulated length grows more slowly than the
leading form at the couplings reachable here, and the ratio of local slopes
approaches one from below as $\beta$ grows@yl_on@; no plateau is claimed for
$O(3)$, whose ratio is still rising at the largest coupling. The inverse
second-moment length is a mass but not in general the transfer-matrix gap, so
this tests the shape of the scaling form, not its constant.

\begin{table}[!htbp]
\centering
\small
@table@
\caption{Fitted slope of $\ln\xi + \tfrac{1}{N-2}\ln\beta$ against $\beta$,
against the leading asymptotic-freedom value $2\pi/(N-2)$. The last column is
the ratio of the slope measured between the end points to the slope the
library's entry predicts between them. From \code{rosettaoai.asymptotic\_freedom()}.}
\label{tab:af}
\end{table}

@onmc_figure@
""", onmc_figure=onmc_figure,
        table=_table(['model', r'$\beta$', 'fitted', 'leading', 'ratio'],
                     rows, 'lcccc'),
        yl_on=(', from $%s$ to $%s$ (O(3)) and from $%s$ to $%s$ (O(4)) in the '
               'laboratory\'s comparison' % tuple(
                   '%.2f' % v for n in (3, 4) for v in
                   (yl['on'][n]['ratio'][0], yl['on'][n]['ratio'][-1]))
               if yl else '')))

    if yl:
        factor = yl['factor_two']
        su = yl['su']
        sizes = sorted(su)
        ratios = ', '.join(
            r'$%d^4$: %s' % (k, ', '.join('%.2f' % x for x in su[k]['ratio']))
            for k in sizes)
        last = [su[k]['ratio'][-1] for k in sizes]
        moved = (len(last) >= 2 and last[-1] > last[0])
        graphic = _graphic('on_local_slopes', 'height=4.8cm')
        graphic2 = _graphic('su2_slopes', 'height=4.8cm')
        figure = (r'\begin{figure}[!htbp]' '\n' r'\centering' '\n'
                  '%s\\hfill%s\n'
                  r"""\caption{Local slope $d\ln m/d\beta$ against $\beta$. Left:
$O(3)$ and $O(4)$ Monte Carlo from the fork against the asymptotic form. Right: the
SU(2) Metropolis scans of the laboratory, $d\ln\sqrt{\chi(2,2)}/d\beta$ at $4^4$ and
$6^4$, against the two-loop slope. The SU(2) lattices are small and short and the
points are far from the line; the $O(N)$ points are closer to theirs. Figures produced
by the laboratory's \code{scripts/generate\_findings.py}.}""" '\n'
                  r'\label{fig:slopes}' '\n' r'\end{figure}'
                  % (graphic, graphic2)) if (graphic and graphic2) else ''
        text.append(fill(r"""
The laboratory's own comparison \cite{elsbernd2026} puts a gauge theory beside
the spin models. Halving the scale takes a change in $\beta$ of
@halving@, at the couplings named. Each $\beta$ is in its own model's
normalisation, so these compare how far each model's coupling must move to change
the scale by the same factor, not how fast one running coupling is against
another. Its $SU(2)$
Metropolis scans measure $\sqrt{\chi(2,2)}$, the Creutz ratio, on periodic
lattices and compare $d\ln\sqrt{\chi}/d\beta$ with the two-loop prediction; the
measured-to-predicted ratios across the scan are @ratios@. These lattices are
far from asymptotic scaling: the plaquette is already close to its
weak-coupling leading term at $\beta\ge 2.8$, but the slope of $\ln\sqrt\chi$
is at most @best@\% of the two-loop value, and at the largest coupling the
ratio is @last@, so the larger lattice @moved@. A possible reason is
strong-coupling and finite-size effects in $\chi(2,2)$ on lattices this small;
it was not tested here, and nothing in this section is a statement about the
continuum mass gap.

@figure@
""", halving=', '.join('$%s$ at $\\beta=%s$ (%.2f)' % (
                r['model'].split(',')[0], r['model'].split('beta=')[1], r['delta_beta'])
                for r in factor),
            ratios=ratios,
            best=('%.0f' % (100 * max(float(max(su[k]['ratio'])) for k in sizes))),
            last=' and '.join('%.2f on $%d^4$' % (su[k]['ratio'][-1], k) for k in sizes),
            moved='moved it toward one' if moved else 'did not move it toward one',
            figure=figure))
    return '\n'.join(text)


def _ym_kt_bloch_haldane(f):
    kt, bl, hal = f['kt'], f['bloch'], f['haldane']
    if kt is None and bl is None and hal is None:
        return ''
    text = []
    if kt:
        mu_rows = ' \\\\\n'.join('%g & %.3f' % (mu, v) for mu, v in kt['mu_lstar_to_pi'])
        log_rows = ' \\\\\n'.join('%g & %.5f' % (r, v) for r, v in kt['log_exponent'][:5])
        graphic = _graphic('kt_flow', r'0.98\textwidth')
        text.append(fill(r"""
\subsection{Kosterlitz--Thouless flow}
\label{sec:ym:kt}

The two-dimensional $XY$ model is the other classic place where a coupling runs,
and the fork \cite{openai2026} computes the textbook flow exactly. In the
variables $x = \pi K - 2$ and a vortex fugacity $y$, with $\ell$ the logarithm
of the length, the library states the two equations
\[ @dx@ , \qquad @dy@ . \]
The quantity $x^2 - y^2$ is conserved. On the disordered side
$x^2 - y^2 = -\mu^2$ and the solution is
\[ x(\ell) = -\mu\tan(\ell\mu + \theta_0), \qquad
   y(\ell) = \frac{\mu}{\cos(\ell\mu+\theta_0)} , \]
and stopping when $y$ reaches one gives the correlation length
\[ \ln\xi = \ell^*(\mu) = \frac{\arccos\mu + \arccos(\mu/y_0)}{\mu},
   \qquad \mu\,\ell^* \to \pi \quad (\mu\to 0). \]
Since $\mu^2\propto T-T_c$ this is the essential singularity
$\ln\xi \sim \pi/\mu \propto 1/\sqrt{T-T_c}$. On the critical separatrix
$x = y = 1/(\ell + c)$ the spin scaling dimension is $\eta = 1/(2\pi K)$, so
with $u = \ell + c$
\[ \int \eta\,d\ell = \frac{u}{4} - \frac{\ln(2u+1)}{8}
   \quad\Longrightarrow\quad C(r) \propto r^{-1/4}(\ln r)^{1/8}. \]
Both exponents match the form quoted in the fork's repository paper; the flow
does not predict its lattice constants. The fork's script checks symbolically that the solution solves the flow, and
numerically that the integrated $\ell^*$ matches the closed form to $10^{-6}$;
Table~\ref{tab:kt} shows the two limits.

\begin{table}[!htbp]
\centering
\small
\begin{tabular}{rc@{\qquad}rc}
\toprule
$\mu$ & $\mu\,\ell^*$ & $\ln r$ & $d\ln(r^{1/4}C)/d\ln r$ \\
\midrule
@rows@ \\
\bottomrule
\end{tabular}
\caption{Left: $\mu\,\ell^*$ tends to $\pi$ as $\mu\to 0$ (for $y_0 = 0.1$). Right:
the local exponent of the logarithmic correction on the critical flow tends to
$1/8$. From the fork's \code{build/data/kt\_flow.json}.}
\label{tab:kt}
\end{table}

@graphic@
""", dx=_entry_tex('Kosterlitz coupling flow'),
            dy=_entry_tex('Kosterlitz fugacity flow'),
            rows=' \\\\\n'.join(
                '%g & %.3f & %g & %.5f' % (a[0], a[1], b[0], b[1])
                for a, b in zip(kt['mu_lstar_to_pi'], kt['log_exponent'])),
            graphic=('\\begin{figure}[!htbp]\n\\centering\n%s\n\\caption{Left: '
                     'Kosterlitz flow with the separatrices $x=\\pm y$ and two '
                     'disordered-side trajectories. Middle: $\\mu\\ln\\xi$ from the '
                     'closed form (lines) and from numerical integration (dots) '
                     'tends to $\\pi$. Right: the local exponent of the '
                     'logarithmic correction tends to $1/8$. Produced by the '
                     'fork\'s \\code{tools/kt\\_flow.py}.}\n\\label{fig:kt}\n'
                     '\\end{figure}') % graphic if graphic else ''))
    if bl or hal:
        parts = []
        if bl:
            a0, a1, a2 = bl['A'][:3]
            parts.append(fill(r"""
\emph{Bloch's law.} The ideal-magnon density of the quantum Heisenberg
ferromagnet, with $x = \beta S$,
\[ n(x) = \sum_{m\ge1}\bigl[e^{-2xm}I_0(2xm)\bigr]^3
   \sim \frac{\zeta(3/2)}{8\pi^{3/2}}x^{-3/2}
   + \frac{3\zeta(5/2)}{128\pi^{3/2}}x^{-5/2}
   + \frac{33\zeta(7/2)}{4096\pi^{3/2}}x^{-7/2} + \dots , \]
has as its first correction the coefficient quoted in the fork's repository paper. The three
coefficients are $A_0 = @a0@$, $A_1 = @a1@$ and $A_2 = @a2@$; the library's
entry \cite{openai2026} states the first two terms. This is a consistency check
of a quoted coefficient against the ideal-magnon expansion, not a re-proof of
the theorem, which is about the interacting system.""",
                             a0='%.5f' % a0, a1='%.5f' % a1, a2='%.5f' % a2))
        if hal:
            gaps = ', '.join('$\\Delta(%d)=%.4f$' % (L, g)
                             for L, g in sorted(hal['gap'].items()))
            parts.append(fill(r"""
\emph{The spin-1 Haldane gap.} On a periodic ring of spin-1 sites
$H(\theta)=\sum_i[\cos\theta\,\mathbf S_i\!\cdot\!\mathbf S_{i+1}
+\sin\theta\,(\mathbf S_i\!\cdot\!\mathbf S_{i+1})^2]$ the bond algebra gives
$\mathbf S\!\cdot\!\mathbf S + \tfrac13(\mathbf S\!\cdot\!\mathbf S)^2 =
2P_2 - \tfrac23$, so at $\tan\theta=\tfrac13$ the Hamiltonian is a sum of
projectors and $E_0 = -2L/3$ on a ring, and the fork's code is checked against
$E_0 = -2L/\sqrt{10}$ at $\tan\theta=\tfrac13$ to $10^{-8}$ before its gap is
believed. Exact diagonalisation gives @gaps@, and a
finite-size fit gives $\Delta_\infty \approx @inf@$ against the DMRG value of
about $@lit@$ from the literature. The fit assumes its form and fits three
points, so it is an illustration; the repository's paper proves a uniform lower
bound for all even $L$.""", gaps=gaps, inf='%.4f' % hal['extrapolated'],
                             lit='%.4f' % hal['literature']))
        text.append('\n\\subsection{Two models that test the machinery}\n'
                    '\\label{sec:ym:machinery}\n\n'
                    'The remaining two models are not about gauge theory. They '
                    'are in the library because each admits an independent '
                    'computation, and because a knowledge base that is going to '
                    'be trusted on the lattice should first be trusted on '
                    'something with a known answer.\n\n' + '\n\n'.join(parts))
    return '\n'.join(text)


def _ym_running_and_tilings(f):
    out = [r"""
\subsection{Running, unification and the tilings}
\label{sec:ym:cicy}
"""]
    if 'alpha3' in f:
        a3 = f['alpha3']
        spot = f['spot']
        flat = max(spot.values()) - min(spot.values()) < 1e-12
        out.append(fill(r"""
CICY \cite{cicy2026} supplies the one-loop running of the three gauge couplings
and the relation between them that unification implies. Eliminating the
unified coupling and scale from $1/\alpha_i(M_Z) = 1/\alpha_G + (b_i/2\pi)
\ln(M_G/M_Z)$ leaves
\[ @unif@ , \]
and with the measured $\alpha_1$ and $\alpha_2$ the library's algebra gives
$\alpha_3(M_Z) = @mssm@$ for the supersymmetric spectrum and $@sm@$ for the
Standard Model, against a measured $@meas@$. The only theoretical input is the
set of $b_i$. A complete generation adds the same amount to every $b_i$, so
the prediction does not depend on the number of generations: @flat@. That is
unwelcome news for a programme that computes generation counts as an index,
because the quantity the geometry gives most reliably is the one that drops out
here. What the prediction is sensitive to is the incomplete multiplets, the
Higgs doublets and any vector-like exotics, which an index cannot see.
""", unif=_entry_tex('Unification prediction'),
            mssm='%.3f' % a3['MSSM'], sm='%.3f' % a3['Standard Model'],
            meas='%.3f' % f['alpha3_measured'],
            flat=('the inverse coupling is the same to $10^{-12}$ for three to '
                  'six generations' if flat else 'it was found to vary with '
                  'the generation count, which would be a bug')))
    else:
        out.append(r"""
CICY was not found on the machine that built this document, so the running of
the couplings is not printed; \code{python3 rosettacicy.py} prints it.
""")

    hat = f['hat']
    hom = f['homogeneous']
    evidence = P.EVIDENCE
    grade_rows = []
    for name in sorted(evidence):
        info = P.evidence_for(name)
        grade_rows.append([esc(P.short(name)), esc(info['fact']),
                           info['kinds'], esc(info['lean'] or '--')])
    mat = f['matrix']
    out.append(fill(r"""
The tilings enter through a different door. The Spectre's substitution is
nine species with inflation factor $\mu = 4+\sqrt{15}$ and the Hat's is four
with $\kappa = (7+3\sqrt5)/2 = \phi^4$; their quadratics, $x^2-8x+1$ and
$x^2-7x+1$, differ in one coefficient, and that coefficient is the difference
between the fields generated by $\sqrt{15}$ and $\sqrt5$. The \texttt{nariai}
repository \cite{nariai2026} adds the linear factor $\ell = (\sqrt6+\sqrt{10})/2$
with $\mu = \ell^2$, the gap-label recurrence $G''=8G'-G$, which is the
characteristic polynomial of the counts applied to powers of the reciprocal
root, and the tile-count growth rate $\ln\mu \approx 2.063$, which is a growth
rate and not an entropy: primitive substitution tilings have zero topological
entropy. @hat@ @matrix@ @hom@

Some of these sources grade their own claims, and the library keeps the grade.
The \texttt{spectre} repository \cite{spectre2026} keeps a ledger in which every
fact is derived by exact computation, counted on a placed tiling, recomputed by
an independent route, quoted, or resting on a premise, and some are also checked
by the Lean kernel. Table~\ref{tab:ledger} copies that grade onto the library's
entries; the bridge compares it with the repository's ledger and the two agree.
The grade is the repository's, and so is the responsibility for it.

\begin{table}[!htbp]
\centering
\small
@table@
\caption{Evidence grades from the \texttt{spectre} ledger: D derived, C counted,
X recomputed by an independent route. A theorem name means the Lean kernel
checked the arithmetic. From \code{rosettaphys.EVIDENCE}.}
\label{tab:ledger}
\end{table}
""", hat=(r"""The Hat constant comes out the same by three routes: the library's closed form,
CICY's exact arithmetic in $\mathbb{Q}(\sqrt5)$ with the root verified exactly,
and the \texttt{spectre} repository's own fact, $\kappa = %.9f$.""" % hat['library']
          if hat and hat['cicy'] is not None and hat['spectre'] is not None
          and abs(hat['cicy'] - hat['library']) < 1e-12
          and abs(hat['spectre'] - hat['library']) < 1e-12 else ''),
        matrix=(r"""The two tiling repositories hold the same $9\times9$ substitution matrix, rule for rule,
with the same characteristic polynomial; they both transcribe the published metatile
rules, so this checks the transcription and not a second derivation."""
                if mat and mat['same_matrix'] and mat['same_charpoly'] else ''),
        hom=(r"""The count recurrence $N_{n+2}=8N_{n+1}-N_n$ holds exactly for %s of the nine species,
from any starting tile, once a transient of at most %s generations has passed; for the other
three, $\Xi$, $\Pi$ and $\Psi$, it does not, because the matrix also has the eigenvalues $\pm1$.
The library's first statement of this was too general, and the bridge is what found out."""
             % (number(len(hom)), number(SP.TRANSIENT)) if hom is not None else ''),
        table=_table(['entry', 'ledger fact', 'grade', 'Lean theorem'],
                     [[r[0], r'\code{%s}' % r[1], r[2], r'\code{%s}' % r[3] if r[3] != '--' else '--']
                      for r in grade_rows], 'llcl')))
    return '\n'.join(out)


def _ym_limits(f):
    ran = [r for r in f['bridges'] if r['ran']]
    return fill(r"""
\subsection{What this section does and does not say}
\label{sec:ym:limits}

Every comparison above is a comparison of arithmetic with arithmetic: the
library's algebra against what a repository's code computes, @ran@ of the five
bridges having run on the machine that built this paper. None of it is evidence
about the Clay problem, and none of it constructs four-dimensional Yang--Mills
theory. The $O(N)$ models and the $XY$ chain are toys for gauge theory, with a
different dimension, different observables and different exponents. The
$SU(2)$ lattices are small, short and single-chain. The tiling repositories bear
on Yang--Mills only through arithmetic and analogy, and the \texttt{nariai}
repository itself records a retraction, an earlier inflation factor that was
not the Spectre's, together with open findings against the physical predictions
it builds on the algebra; those predictions are not in the library and are not
claimed here. What the display records is the narrower thing that was tested:
which of these repositories agree about which quantity, and where the library
refuses to say that two similar things are the same.

\clearpage
""", ran=number(len(ran)))


def yang_mills_section():
    f = ym_facts()
    return '\n'.join([_ym_overview(f), _ym_asymptotic(f),
                      _ym_kt_bloch_haldane(f), _ym_running_and_tilings(f),
                      _ym_limits(f)])



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
\newline
\url{%s}
\newline
(the laboratory of Section~\ref{sec:lattice}: found in \code{YMLAB\_DIR}, or in
a \code{yang-mills-mass-gap-lab} directory beside this one)
\newline
\url{%s}
\newline
\url{%s}
\newline
\url{%s}
\newline
\url{%s}
\newline
(the four repositories of Section~\ref{sec:ym}: found through
\code{OPENAI\_MATH\_DIR}, \code{CICY\_DIR}, \code{SPECTRE\_DIR} and
\code{NARIAI\_DIR}, or in a directory of that name beside this one; the figures
of that section are copied from them next to the \code{.tex} when it is written)

\begin{lstlisting}[language={}]
python3 rosettaphys.py             the census: nodes, edges, joins, collisions
python3 rosettaphys.py --selftest  %d entries, the graph, and the algebra
python3 rosettalean.py             every join, as a checked conjecture
python3 rosettalean.py --selftest  the bridge, end to end
python3 rosettaym.py               the Yang-Mills laboratory, checked against the library
python3 rosettaym.py --selftest    %d comparisons, and the published campaign
python3 rosettaym.py --reproduce   rerun one chain pair here (slow)
python3 rosettaoai.py              the OpenAI-math fork, checked against the library
python3 rosettacicy.py             CICY's couplings and generation count
python3 rosettaspectre.py          the spectre repository, its ledger, and the Hat constant
python3 rosettanariai.py           nariai's constants, and its matrix against spectre's
python3 rosettapaper.py            regenerate this document
make test                          all of the above, plus the kernel
make collisions                    the table in Section 4
\end{lstlisting}
""" % (P.REFERENCES[Y.REFERENCE]['url'],
       P.REFERENCES['openai2026']['url'], P.REFERENCES['cicy2026']['url'],
       P.REFERENCES['spectre2026']['url'], P.REFERENCES['nariai2026']['url'],
       len(P.SYMBOLS) + len(P.CONCEPTS) + len(P.EQUATIONS), len(Y.checks()))


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
    computed = [eq for eq, _src in P.sourced() if P.reference_for(eq) is None]
    coded = [eq for eq, _src in P.sourced() if P.reference_for(eq) is not None]
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

Most of the library can be checked against a textbook. %s cannot, for one of
two reasons. %s are computed: their values came from a matrix or a function, and
an entry that says only which Wikipedia article explains the idea does not say
where its number came from. Those entries carry a \code{source} naming the
matrix or function it was computed from.
\newline
\url{https://github.com/brentharts/spectre}
\newline
\url{https://github.com/brentharts/CICY}

The other %s describe code rather than compute from it: the lattice gauge
theory entries drawn from the laboratory of Elsbernd \cite{elsbernd2026}, whose
\code{source} names the function the equation states. Section~\ref{sec:lattice}
checks each against that function.

The field exists because of a near-miss. Two of the substitutions below give
different inflation factors for the aperiodic monotile---$\phi^4$ for the hat
and $4+\sqrt{15}$ for the spectre---and both are right, because they are
different substitutions on different numbers of species. Written without
provenance the two entries read as a contradiction, and the first draft of the
tilings group made exactly that mistake.

\begin{longtable}{p{4.4cm}p{10cm}}
\toprule
\tiny
Entry & Source \\
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
       words(len(computed), 'entry', 'entries').capitalize(),
       words(len(coded), 'entry', 'entries'),
       source_rows, lean)


def _bibitem(key):
    """A reference from the knowledge base, as a \\bibitem.

    The key is the one the prose cites, and the fields come from
    rosettaphys.REFERENCES, so the paper and the graph cite one thing.
    """
    ref = P.REFERENCES[key]
    title = esc(ref['title']).replace('Yang-Mills', 'Yang--Mills')
    sub = esc(ref['subtitle'])
    words_ = ref['authors'].split()
    if len(words_) == 2:
        # 'Michael Elsbernd': surname, initial
        who = '%s, %s.' % (esc(words_[-1]), esc(words_[0][0]))
    else:
        # a credit line rather than a name: print it as written
        who = esc(ref['authors'])
    return (r"\bibitem{%s} %s (%d). %s: %s. %s" "\n"
            r"\url{%s}" "\n\n"
            % (key, who, ref['year'], title, sub, esc(ref['note']),
               ref['url']))


ELSBERND = _bibitem(Y.REFERENCE)

BIBLIOGRAPHY = r"""
\begin{thebibliography}{99}

\bibitem{hartshorn2026rosetta} Hartshorn, B.~S. (2026). RosettaMath: Reading,
Running and Proving Mathematics from \LaTeX{}. SSRN.
\newline
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

# The one reference that comes from the knowledge base rather than from this
# file: rosettaphys.REFERENCES is where it is defined, so the bibliography
# cannot say something the graph does not.
BIBLIOGRAPHY = BIBLIOGRAPHY.replace(
    r'\end{thebibliography}',
    ELSBERND + ''.join(_bibitem(k) for k in
                       ('openai2026', 'cicy2026', 'spectre2026', 'nariai2026'))
    + r'\end{thebibliography}')


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
        lattice_section(),
        yang_mills_section(),
        lean_section(),
        reproducibility(),
        appendices(),
        BIBLIOGRAPHY,
    )


def write(path=OUTPUT):
    text = document()
    with open(path, 'w') as handle:
        handle.write(text)
    # the figures the Yang--Mills section includes, beside the .tex
    stage_figures(os.path.dirname(os.path.abspath(path)))
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

    print('the lattice gauge theory group, and its source')
    lattice = P.equations_in(Y.FIELD)
    check('the section is present', r'\label{sec:lattice}' in text)
    check('the laboratory is cited and the reference is defined',
          r'\cite{%s}' % Y.REFERENCE in text
          and r'\bibitem{%s}' % Y.REFERENCE in text)
    check('the author is credited by name in the bibliography',
          P.REFERENCES[Y.REFERENCE]['authors'].split()[-1] in
          text.split(r'\bibitem{%s}' % Y.REFERENCE)[-1])
    check('the knowledge base and the paper cite one URL',
          P.REFERENCES[Y.REFERENCE]['url'] in text)
    check('the group is counted correctly',
          str(len(lattice)) in text)
    flat = ' '.join(text.split())
    check('the scope is stated: it does not touch the mass-gap problem',
          'does not prove a positive mass gap' in flat
          and 'Nothing below is evidence about that problem' in flat)
    check('every entry citing the laboratory is in the source appendix',
          all(esc(src) in text for eq, src in P.sourced()
              if P.reference_for(eq)))
    check('no local path to the laboratory leaks into the document',
          Y.locate() is None or Y.locate() not in text)
    if Y.available():
        results = Y.checks()
        cell = Y.aggregation()
        check('every comparison against the code is printed',
              all(esc(c.equation) in text for c in results))
        check('the headline ratio is printed, to four places',
              _ratio(cell['mean_of_paired_ratios']) in text)
        check('and so is the other way of summarising it',
              _ratio(cell['ratio_of_mean_efficiencies']) in text)
        check('the confining and fundamental string tensions are not joined',
              P.join('Area law', 'String tension') is None
              and 'confining string tension' in text)
        check('the campaign table has a row for every schedule at every beta',
              text.count(r'\code{M+1OR}') >= len(Y.published_campaign()
                                                 ['config']['betas']))
        check('the published run used is a clean one',
              not Y.published_campaign()['git'].get('dirty', True))
    else:
        check('without the laboratory the section says so',
              'was not found on the machine' in text)

    print('Yang-Mills across five repositories')
    check('the section is present', r'\label{sec:ym}' in text
          and 'Yang--Mills across five repositories' in text)
    check('every repository is cited and defined',
          all((r'\cite{%s}' % k in text or k in
               ','.join(__import__('re').findall(r'\\cite\{([^}]+)\}', text)))
              and r'\bibitem{%s}' % k in text for k in YM_KEYS))
    check('the display is the library\'s, row for row',
          P.grand_yang_mills() in text)
    members = P.grand_yang_mills_members()
    check('every row names its quantity',
          all(P._tex_escape(m.name()) in text for m in members))
    check('every repository is labelled on the display',
          all('(%s)' % P.REFERENCES[k]['tag'] in text for k in YM_KEYS))
    links = P.cross_repository_links()
    check('the correspondences are counted',
          '%d links' % len(links) in text and len(links) >= 5)
    check('the identities elaborate to one proposition',
          RL.grand_conjecture(P.YM_PIVOTS, name='yang_mills').check() == 'Prop')
    check('the supersymmetric coefficient is left out of the colour row',
          'One-loop coefficient (SUSY)' not in
          [st.equation['name'] for m in members if m.pivot == 'N'
           for st in m.steps])
    facts = ym_facts()
    check('the bridge table has a row for every repository',
          all(r'\code{%s}' % esc(P.REFERENCES[k]['tag']) in text for k in YM_KEYS))
    check('no bridge disagrees',
          all(r.get('ok', True) for r in facts['bridges'])
          and 'DISAGREE' not in text)
    check('the limits are stated',
          'None of it is evidence' in flat and 'Clay problem' in flat
          and 'toys for gauge theory' in flat)
    import re as _re
    drawn = _re.findall(r'\\includegraphics\[[^]]*\]\{figures/([a-z_0-9]+)\.pdf\}', text)
    check('every figure drawn has a source to copy from',
          all(figure_source(n) for n in drawn))
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        staged = stage_figures(tmp)
        check('and is staged beside the .tex',
              sorted(staged) == sorted(drawn)
              and all(os.path.exists(os.path.join(tmp, 'figures', n + '.pdf'))
                      for n in drawn))
    check('the repositories\' own figures are credited to their code',
          all(c in text for c in ('tools/on\\_model\\_mc.py', 'tools/kt\\_flow.py'))
          or not drawn)
    check('no local path to any repository leaks into the document',
          all(loc is None or loc not in text for loc in
              (Y.locate(), OAI.locate(), CI.locate(), SP.locate(),
               NR.locate())))
    check('the two tiling repositories are credited to the author in the bibliography',
          text.count('Hartshorn, B.~S.') >= 3 and 'B. S. Hartshorn (spectre' in text)
    if facts['homogeneous'] is not None:
        check('the recurrence is stated for the species it holds for',
              number(len(facts['homogeneous'])) in text
              and 'first statement of this was too general' in flat)

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
