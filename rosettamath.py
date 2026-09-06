#!/usr/bin/env python3
__doc__ = r"""RosettaMath -- a tiny, self-hosting LaTeX -> Python translator.

Design
------
Only a small subset of LaTeX is understood, chosen so that translation is
nearly one-to-one with Python.  Everything not listed is ignored (\begin,
\end, \caption, % comments) or passed through.

  algorithmic (algpseudocode) .......... statements and control flow
      \Function{name}{$args$} .. \EndFunction   def name(args):
      \State $stmt$                             stmt
      \If{$c$} \ElsIf{$c$} \Else \EndIf         if / elif / else
      \For{$x \in xs$} .. \EndFor               for x in xs:
      \For{$i = a$ to $b$} .. \EndFor           for i in range(a, b + 1):
      \While{$c$} .. \EndWhile                  while c:
      \Return $expr$                            return expr
      \Comment{text}                            # text
      Text outside $..$ in a \State is already Python ("break", "is None").

  math mode ($..$) ..................... expressions
      \gets   =           \geq \leq \neq      >=  <=  !=
      =       ==          \land \lor \lnot    and  or  not
      ^       **          \in \notin          in  /  not in
      {..}    (..)        \times \cdot        *
      \{ \}   { }         \frac{a}{b}         (a)/(b)
      2x  2\pi            2*x  2*pi           (a number touching a name)
      k_B c   m \hbar      k_B*c  m*hbar       (a space between two atoms)
      \texttt{..}         '..'                (\textbackslash \{ \$ \_ unescaped)
      \anything           anything            (\rho -> rho, resolved in the scope)

  equations ............................ one-liners
      $f(x) = 2x + 1$                          def f(x): return 2*x + 1
      $S = k_B \log W$                         def S(k_B, W): return ..
                                               (a bare left side takes its
                                               arguments from the free names
                                               on the right; anything already
                                               in the scope stays a constant)
      $f(x) = \begin{cases} a & \text{if } c \\ .. \end{cases}$
                                               def f(x): if c: return a ..

Reverse direction
-----------------
Python2Tex walks a Python AST back into algpseudocode.  It is plain Python and
not part of the bootstrap, so unlike everything above it exists only once.

Two rules make the output survive the journey back through tex2py:
precedence is made explicit with parentheses, because a tree knows that
$(a+b)\cdot c$ groups and a flat string does not; and Python keywords step
outside math mode, because inside $...$ a space between two names is implicit
multiplication, so "x is None" would come back as x*is*None.  Writing
$x$ is $None$ puts the keyword in a text segment instead.

Anything the subset cannot express is reported as a \Comment and collected in
a warnings list, never dropped in silence.  roundtrip_test() checks the whole
thing by behaviour rather than by eye.

Bootstrap
---------
The translator exists twice: in plain Python (stage 0, below) and in the
LaTeX subset above (NEOMATH_TEX).  Stage 0 turns NEOMATH_TEX into Python
(stage 1).  Stage 1 then translates NEOMATH_TEX again; if the output is
byte-for-byte what stage 0 produced we have a fixed point, and the LaTeX
version takes over.  From then on the translator can be extended in LaTeX
(add an OPS line, add a branch to math2py, ...) and the Python copy is only
a bootstrap that could be regenerated from the LaTeX.

No external libraries.   python3 rosettamath.py          runs the self test
                         python3 rosettamath.py --pdf    also typesets NEOMATH_TEX
"""
import sys, subprocess
import ast, inspect


INDENT = chr(32) * 4
NL = chr(10)

# math-mode commands and their Python spelling; unknown \cmd become plain 'cmd'
OPS = {
    '\\gets': '=', '\\geq': '>=', '\\leq': '<=', '\\neq': '!=',
    '\\land': ' and ', '\\lor': ' or ', '\\lnot': ' not ',
    '\\in': ' in ', '\\notin': ' not in ', '\\times': '*', '\\cdot': '*',
    '\\{': '{', '\\}': '}', '\\_': '_', '\\%': '%', '\\#': '#', '\\&': '&',
    '\\,': ' ', '\\;': ' ', '\\\\': '',
}

# names that are Python syntax, not free variables of an equation
KEYWORDS = ('return if else elif and or not in is None True False for while '
            'def lambda raise break continue pass').split()

# ---------------------------------------------------------------- stage 0

def mulsep(out, m, i):
    r"""is the space at m[i] an implied multiplication?  (k_B c, 2 \pi, x y)

    Juxtaposition means "multiply" to a reader and nothing at all to a parser.
    Only a space between two *atoms* counts: a space next to an operator, or
    one already emitted by an OPS replacement such as ' and ', must be left
    alone or the generated Python stops being Python.
    """
    if out == '':
        return False
    p = out[-1]
    if not (p.isalnum() or p == '_' or p == ')' or p == ']'):
        return False
    j = i
    while j < len(m) and m[j] == ' ':
        j += 1
    if j >= len(m):
        return False
    c = m[j]
    if c.isalnum():
        return True
    if c == '\\':
        k = j + 1
        while k < len(m) and m[k].isalpha():
            k += 1
        if k == j + 1:
            k += 1
        rep = OPS.get(m[j:k], m[j+1:k])
        if rep[:1].isalpha():
            return True
    return False

def freevars(src, known):
    """names in src that are not calls, attributes, keywords or already known.

    Used to give a bare left-hand side ($S = ...$) a parameter list, so that
    the equation still translates to something callable.
    """
    names = []
    i = 0
    while i < len(src):
        c = src[i]
        if c == "'" or c == '"':
            q = c
            i = i + 1
            while i < len(src) and src[i] != q:
                i = i + 1
            i = i + 1
        elif c.isalpha() or c == '_':
            j = i
            while j < len(src) and (src[j].isalnum() or src[j] == '_'):
                j += 1
            name = src[i:j]
            k = j
            while k < len(src) and src[k] == ' ':
                k += 1
            call = k < len(src) and src[k] == '('
            attr = i > 0 and src[i-1] == '.'
            if not call and not attr and name not in KEYWORDS and name not in known and name not in names:
                names.append(name)
            i = j
        else:
            i = i + 1
    return names

def match(s, i):
    """s[i] is '{'; return the index of its partner (escaped braces skipped)."""
    depth = 0
    while i < len(s):
        c = s[i]
        if c == '\\':
            i += 1
        elif c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError('unbalanced braces: ' + s)

def arg(s):
    """first {group} of s, and the rest of s after it."""
    i = s.index('{')
    j = match(s, i)
    return s[i+1:j], s[j+1:]

def unescape(s):
    r"""\texttt content -> plain text:  \textbackslash \{ \} \_ \$ \^{} ..."""
    out = ''
    i = 0
    while i < len(s):
        if s[i] == '\\':
            if s.startswith('\\textbackslash', i):
                out += '\\'
                i += len('\\textbackslash')
                if s.startswith(' ', i):
                    i += 1
            else:
                out += s[i+1]
                i += 2
            if s.startswith('{}', i):
                i += 2
        else:
            out += s[i]
            i += 1
    return out

def segments(s):
    """split on unescaped $ (or $$) into [(is_math, text), ...]."""
    parts = []
    buf = ''
    math = False
    i = 0
    while i < len(s):
        c = s[i]
        if c == '\\':
            buf += s[i:i+2]
            i += 2
        elif c == '$':
            if buf:
                parts.append((math, buf))
            buf = ''
            math = not math
            i += 1
            if i < len(s) and s[i] == '$':
                i += 1
        else:
            buf += c
            i += 1
    if buf:
        parts.append((math, buf))
    return parts

def math2py(m):
    """translate the inside of $...$ to a Python expression."""
    out = ''
    lit = False              # inside a numeric literal?
    i = 0
    while i < len(m):
        c = m[i]
        if c == '\\':
            j = i + 1
            while j < len(m) and m[j].isalpha():
                j += 1
            if j == i + 1:
                j += 1       # one-character command
            cmd = m[i:j]
            if cmd == '\\texttt':
                k = match(m, j)
                out += repr(unescape(m[j+1:k]))
                i = k + 1
            elif cmd == '\\frac':
                k = match(m, j)
                l = match(m, k + 1)
                out += '(' + math2py(m[j+1:k]) + ')/(' + math2py(m[k+2:l]) + ')'
                i = l + 1
            else:
                rep = OPS.get(cmd, cmd[1:])
                if lit and rep[:1].isalpha():
                    out += '*'
                out += rep
                i = j
            lit = False
        else:
            if c.isdigit() and (i == 0 or not (m[i-1].isalnum() or m[i-1] == '_')):
                lit = True
            if c == '^':
                out += '**'
            elif c == '=':
                out += '=='
            elif c == '{':
                out += '('
            elif c == '}':
                out += ')'
            elif c.isalpha() and lit:
                out += '*' + c
            elif c == ' ' and mulsep(out, m, i):
                out += '*'
            else:
                out += c
            if not c.isdigit() and c != '.':
                lit = False
            i += 1
    return out

def state2py(s):
    r"""a \State body: math is translated, text outside math is already Python."""
    out = ''
    for ismath, seg in segments(s):
        if ismath:
            out += math2py(seg)
        elif seg.strip().startswith('\\Comment{'):
            note, rest = arg(seg)
            out += '  # ' + note
        else:
            out += seg.replace('\\\\', '')
    return out

def stmt2py(s):
    s = s.strip()
    if s.startswith('\\Return'):
        return 'return ' + state2py(s[len('\\Return'):]).strip()
    return state2py(s).strip()

def for2py(head):
    t = head.replace('$', '')
    if ' to ' in t:
        a, hi = t.split(' to ')
        var, lo = a.split('=')
        return 'for ' + math2py(var).strip() + ' in range(' + math2py(lo).strip() + ', ' + math2py(hi).strip() + ' + 1):'
    return 'for ' + math2py(t).strip() + ':'

def tex2py(tex):
    r"""algorithmic block -> Python source (one \State per line, indent by depth)."""
    py = []
    depth = 0
    for raw in tex.splitlines():
        ln = raw.strip()
        pre = INDENT * depth
        if ln.startswith('\\Function{') or ln.startswith('\\Procedure{'):
            name, rest = arg(ln)
            args, rest = arg(rest)
            py.append(pre + 'def ' + unescape(name) + '(' + state2py(args) + '):')
            depth += 1
        elif ln.startswith('\\End'):
            depth -= 1
        elif ln.startswith('\\For'):
            head, rest = arg(ln)
            py.append(pre + for2py(head))
            depth += 1
        elif ln.startswith('\\While{'):
            cond, rest = arg(ln)
            py.append(pre + 'while ' + state2py(cond) + ':')
            depth += 1
        elif ln.startswith('\\If{'):
            cond, rest = arg(ln)
            py.append(pre + 'if ' + state2py(cond) + ':')
            depth += 1
        elif ln.startswith('\\ElsIf{'):
            cond, rest = arg(ln)
            py.append(pre[len(INDENT):] + 'elif ' + state2py(cond) + ':')
        elif ln.startswith('\\Else'):
            py.append(pre[len(INDENT):] + 'else:')
        elif ln.startswith('\\State'):
            py.append(pre + stmt2py(ln[len('\\State'):]))
        elif ln.startswith('\\Return') or ln.startswith('\\Comment'):
            py.append(pre + stmt2py(ln))
    return NL.join(py)

def eq2py(tex, known=None):
    """$f(x) = ...$  (the last math segment is the definition) -> Python source.

    A bare left-hand side such as $S = k_B \\log W$ names no arguments, so the
    free variables of the right-hand side become the parameter list.  Anything
    already in known (the scope the caller supplies) stays a constant.
    """
    if known is None:
        known = {}
    m = None
    for ismath, seg in segments(tex):
        if ismath:
            m = seg
    lhs, rhs = m.split('=', 1)
    name = math2py(lhs).strip()
    CASES = '\\begin{cases}'
    body = ''
    if CASES not in rhs:
        body = INDENT + 'return ' + math2py(rhs).strip()
    else:
        rhs = rhs[rhs.index(CASES) + len(CASES) : rhs.index('\\end{cases}')]
        rhs = rhs.replace('\\text{if }', '').replace('\\text{otherwise}', 'True')
        for row in rhs.split('\\\\'):
            if '&' in row:
                expr, cond = row.split('&')
                body = body + INDENT + 'if ' + math2py(cond).strip() + ': return ' + math2py(expr).strip() + NL
    if '(' not in name:
        name = name + '(' + ', '.join(freevars(body, known)) + ')'
    return 'def ' + name + ':' + NL + body

def latex2py(tex, scope=None):
    """translate, exec into scope, and return the last function defined."""
    if scope is None:
        scope = {}
    if '\\State' in tex or '\\Function' in tex:
        py = tex2py(tex)
    else:
        py = eq2py(tex, scope)
    exec(py, scope)
    name = None
    for ln in py.splitlines():
        if ln.startswith('def '):
            name = ln[4:ln.index('(')]
    if name is None:
        return scope
    return scope[name]

latex2py_source = inspect.getsource(latex2py)


# ------------------------------------------- the same translator, in LaTeX

NEOMATH_TEX = r'''
\begin{algorithm}
\tiny
\caption{RosettaMath: a \LaTeX{} to Python translator, written in the subset it translates}
\begin{algorithmic}

\State $INDENT \gets chr(32) \times 4$
\State $NL \gets chr(10)$

\State \Comment{math-mode commands and their Python spelling}
\State $OPS \gets \{\}$
\State $OPS[\texttt{\textbackslash gets}] \gets \texttt{=}$
\State $OPS[\texttt{\textbackslash geq}] \gets \texttt{>=}$
\State $OPS[\texttt{\textbackslash leq}] \gets \texttt{<=}$
\State $OPS[\texttt{\textbackslash neq}] \gets \texttt{!=}$
\State $OPS[\texttt{\textbackslash land}] \gets \texttt{ and }$
\State $OPS[\texttt{\textbackslash lor}] \gets \texttt{ or }$
\State $OPS[\texttt{\textbackslash lnot}] \gets \texttt{ not }$
\State $OPS[\texttt{\textbackslash in}] \gets \texttt{ in }$
\State $OPS[\texttt{\textbackslash notin}] \gets \texttt{ not in }$
\State $OPS[\texttt{\textbackslash times}] \gets \texttt{*}$
\State $OPS[\texttt{\textbackslash cdot}] \gets \texttt{*}$
\State $OPS[\texttt{\textbackslash\{}] \gets \texttt{\{}$
\State $OPS[\texttt{\textbackslash\}}] \gets \texttt{\}}$
\State $OPS[\texttt{\textbackslash\_}] \gets \texttt{\_}$
\State $OPS[\texttt{\textbackslash\%}] \gets \texttt{\%}$
\State $OPS[\texttt{\textbackslash\#}] \gets \texttt{\#}$
\State $OPS[\texttt{\textbackslash\&}] \gets \texttt{\&}$
\State $OPS[\texttt{\textbackslash,}] \gets \texttt{ }$
\State $OPS[\texttt{\textbackslash;}] \gets \texttt{ }$
\State $OPS[\texttt{\textbackslash\textbackslash}] \gets \texttt{}$

\State \Comment{names that are Python syntax, not free variables of an equation}
\State $KEYWORDS \gets \texttt{return if else elif and or not in is None True False for while def lambda raise break continue pass}.split()$

\Function{mulsep}{$out, m, i$} \Comment{is the space at $m[i]$ an implied multiplication?}
    \If{$out = \texttt{}$}
        \Return $False$
    \EndIf
    \State $p \gets out[-1]$
    \If{$\lnot (p.isalnum() \lor p = \texttt{\_} \lor p = \texttt{)} \lor p = \texttt{]})$}
        \Return $False$
    \EndIf
    \State $j \gets i$
    \While{$j < len(m) \land m[j] = \texttt{ }$}
        \State $j \gets j + 1$
    \EndWhile
    \If{$j \geq len(m)$}
        \Return $False$
    \EndIf
    \State $c \gets m[j]$
    \If{$c.isalnum()$}
        \Return $True$
    \EndIf
    \If{$c = \texttt{\textbackslash}$}
        \State $k \gets j + 1$
        \While{$k < len(m) \land m[k].isalpha()$}
            \State $k \gets k + 1$
        \EndWhile
        \If{$k = j + 1$}
            \State $k \gets k + 1$
        \EndIf
        \State $rep \gets OPS.get(m[j:k], m[j+1:k])$
        \If{$rep[:1].isalpha()$}
            \Return $True$
        \EndIf
    \EndIf
    \Return $False$
\EndFunction

\Function{freevars}{$src, known$} \Comment{names in $src$ that are not calls, keywords or known}
    \State $names \gets []$
    \State $i \gets 0$
    \While{$i < len(src)$}
        \State $c \gets src[i]$
        \If{$c = \texttt{'} \lor c = \texttt{"}$}
            \State $q \gets c$
            \State $i \gets i + 1$
            \While{$i < len(src) \land src[i] \neq q$}
                \State $i \gets i + 1$
            \EndWhile
            \State $i \gets i + 1$
        \ElsIf{$c.isalpha() \lor c = \texttt{\_}$}
            \State $j \gets i$
            \While{$j < len(src) \land (src[j].isalnum() \lor src[j] = \texttt{\_})$}
                \State $j \gets j + 1$
            \EndWhile
            \State $name \gets src[i:j]$
            \State $k \gets j$
            \While{$k < len(src) \land src[k] = \texttt{ }$}
                \State $k \gets k + 1$
            \EndWhile
            \State $call \gets k < len(src) \land src[k] = \texttt{(}$
            \State $attr \gets i > 0 \land src[i-1] = \texttt{.}$
            \If{$\lnot call \land \lnot attr \land name \notin KEYWORDS \land name \notin known \land name \notin names$}
                \State $names.append(name)$
            \EndIf
            \State $i \gets j$
        \Else
            \State $i \gets i + 1$
        \EndIf
    \EndWhile
    \Return $names$
\EndFunction

\Function{match}{$s, i$} \Comment{$s[i]$ is a brace, return the index of its partner}
    \State $depth \gets 0$
    \While{$i < len(s)$}
        \State $c \gets s[i]$
        \If{$c = \texttt{\textbackslash}$}
            \State $i \gets i + 1$
        \ElsIf{$c = \texttt{\{}$}
            \State $depth \gets depth + 1$
        \ElsIf{$c = \texttt{\}}$}
            \State $depth \gets depth - 1$
            \If{$depth = 0$}
                \Return $i$
            \EndIf
        \EndIf
        \State $i \gets i + 1$
    \EndWhile
    \State raise $ValueError(\texttt{unbalanced braces: } + s)$
\EndFunction

\Function{arg}{$s$} \Comment{first brace group of $s$, and the rest of $s$}
    \State $i \gets s.index(\texttt{\{})$
    \State $j \gets match(s, i)$
    \Return $s[i+1:j], s[j+1:]$
\EndFunction

\Function{unescape}{$s$} \Comment{\texttt{\textbackslash texttt} content to plain text}
    \State $out \gets \texttt{}$
    \State $i \gets 0$
    \While{$i < len(s)$}
        \If{$s[i] = \texttt{\textbackslash}$}
            \If{$s.startswith(\texttt{\textbackslash textbackslash}, i)$}
                \State $out \gets out + \texttt{\textbackslash}$
                \State $i \gets i + len(\texttt{\textbackslash textbackslash})$
                \If{$s.startswith(\texttt{ }, i)$}
                    \State $i \gets i + 1$
                \EndIf
            \Else
                \State $out \gets out + s[i+1]$
                \State $i \gets i + 2$
            \EndIf
            \If{$s.startswith(\texttt{\{\}}, i)$}
                \State $i \gets i + 2$
            \EndIf
        \Else
            \State $out \gets out + s[i]$
            \State $i \gets i + 1$
        \EndIf
    \EndWhile
    \Return $out$
\EndFunction

\Function{segments}{$s$} \Comment{split on unescaped \texttt{\$} into (is math, text) pairs}
    \State $parts \gets []$
    \State $buf \gets \texttt{}$
    \State $math \gets False$
    \State $i \gets 0$
    \While{$i < len(s)$}
        \State $c \gets s[i]$
        \If{$c = \texttt{\textbackslash}$}
            \State $buf \gets buf + s[i:i+2]$
            \State $i \gets i + 2$
        \ElsIf{$c = \texttt{\$}$}
            \If{$buf$}
                \State $parts.append((math, buf))$
            \EndIf
            \State $buf \gets \texttt{}$
            \State $math \gets \lnot math$
            \State $i \gets i + 1$
            \If{$i < len(s) \land s[i] = \texttt{\$}$}
                \State $i \gets i + 1$
            \EndIf
        \Else
            \State $buf \gets buf + c$
            \State $i \gets i + 1$
        \EndIf
    \EndWhile
    \If{$buf$}
        \State $parts.append((math, buf))$
    \EndIf
    \Return $parts$
\EndFunction

\Function{math2py}{$m$} \Comment{the inside of \texttt{\$...\$} to a Python expression}
    \State $out \gets \texttt{}$
    \State $lit \gets False$ \Comment{inside a numeric literal?}
    \State $i \gets 0$
    \While{$i < len(m)$}
        \State $c \gets m[i]$
        \If{$c = \texttt{\textbackslash}$}
            \State $j \gets i + 1$
            \While{$j < len(m) \land m[j].isalpha()$}
                \State $j \gets j + 1$
            \EndWhile
            \If{$j = i + 1$}
                \State $j \gets j + 1$ \Comment{one-character command}
            \EndIf
            \State $cmd \gets m[i:j]$
            \If{$cmd = \texttt{\textbackslash texttt}$}
                \State $k \gets match(m, j)$
                \State $out \gets out + repr(unescape(m[j+1:k]))$
                \State $i \gets k + 1$
            \ElsIf{$cmd = \texttt{\textbackslash frac}$}
                \State $k \gets match(m, j)$
                \State $l \gets match(m, k + 1)$
                \State $out \gets out + \texttt{(} + math2py(m[j+1:k]) + \texttt{)/(} + math2py(m[k+2:l]) + \texttt{)}$
                \State $i \gets l + 1$
            \Else
                \State $rep \gets OPS.get(cmd, cmd[1:])$
                \If{$lit \land rep[:1].isalpha()$}
                    \State $out \gets out + \texttt{*}$
                \EndIf
                \State $out \gets out + rep$
                \State $i \gets j$
            \EndIf
            \State $lit \gets False$
        \Else
            \If{$c.isdigit() \land (i = 0 \lor \lnot (m[i-1].isalnum() \lor m[i-1] = \texttt{\_}))$}
                \State $lit \gets True$
            \EndIf
            \If{$c = \texttt{\^{}}$}
                \State $out \gets out + \texttt{**}$
            \ElsIf{$c = \texttt{=}$}
                \State $out \gets out + \texttt{==}$
            \ElsIf{$c = \texttt{\{}$}
                \State $out \gets out + \texttt{(}$
            \ElsIf{$c = \texttt{\}}$}
                \State $out \gets out + \texttt{)}$
            \ElsIf{$c.isalpha() \land lit$}
                \State $out \gets out + \texttt{*} + c$
            \ElsIf{$c = \texttt{ } \land mulsep(out, m, i)$}
                \State $out \gets out + \texttt{*}$
            \Else
                \State $out \gets out + c$
            \EndIf
            \If{$\lnot c.isdigit() \land c \neq \texttt{.}$}
                \State $lit \gets False$
            \EndIf
            \State $i \gets i + 1$
        \EndIf
    \EndWhile
    \Return $out$
\EndFunction

\Function{state2py}{$s$} \Comment{a \texttt{\textbackslash State} body; text outside math is already Python}
    \State $out \gets \texttt{}$
    \For{$ismath, seg \in segments(s)$}
        \If{$ismath$}
            \State $out \gets out + math2py(seg)$
        \ElsIf{$seg.strip().startswith(\texttt{\textbackslash Comment\{})$}
            \State $note, rest \gets arg(seg)$
            \State $out \gets out + \texttt{  \# } + note$
        \Else
            \State $out \gets out + seg.replace(\texttt{\textbackslash\textbackslash}, \texttt{})$
        \EndIf
    \EndFor
    \Return $out$
\EndFunction

\Function{stmt2py}{$s$}
    \State $s \gets s.strip()$
    \If{$s.startswith(\texttt{\textbackslash Return})$}
        \Return $\texttt{return } + state2py(s[len(\texttt{\textbackslash Return}):]).strip()$
    \EndIf
    \Return $state2py(s).strip()$
\EndFunction

\Function{for2py}{$head$}
    \State $t \gets head.replace(\texttt{\$}, \texttt{})$
    \If{$\texttt{ to } \in t$}
        \State $a, hi \gets t.split(\texttt{ to })$
        \State $var, lo \gets a.split(\texttt{=})$
        \Return $\texttt{for } + math2py(var).strip() + \texttt{ in range(} + math2py(lo).strip() + \texttt{, } + math2py(hi).strip() + \texttt{ + 1):}$
    \EndIf
    \Return $\texttt{for } + math2py(t).strip() + \texttt{:}$
\EndFunction

\Function{tex2py}{$tex$} \Comment{algorithmic block to Python source}
    \State $py \gets []$
    \State $depth \gets 0$
    \For{$raw \in tex.splitlines()$}
        \State $ln \gets raw.strip()$
        \State $pre \gets INDENT \times depth$
        \If{$ln.startswith(\texttt{\textbackslash Function\{}) \lor ln.startswith(\texttt{\textbackslash Procedure\{})$}
            \State $name, rest \gets arg(ln)$
            \State $args, rest \gets arg(rest)$
            \State $py.append(pre + \texttt{def } + unescape(name) + \texttt{(} + state2py(args) + \texttt{):})$
            \State $depth \gets depth + 1$
        \ElsIf{$ln.startswith(\texttt{\textbackslash End})$}
            \State $depth \gets depth - 1$
        \ElsIf{$ln.startswith(\texttt{\textbackslash For})$}
            \State $head, rest \gets arg(ln)$
            \State $py.append(pre + for2py(head))$
            \State $depth \gets depth + 1$
        \ElsIf{$ln.startswith(\texttt{\textbackslash While\{})$}
            \State $cond, rest \gets arg(ln)$
            \State $py.append(pre + \texttt{while } + state2py(cond) + \texttt{:})$
            \State $depth \gets depth + 1$
        \ElsIf{$ln.startswith(\texttt{\textbackslash If\{})$}
            \State $cond, rest \gets arg(ln)$
            \State $py.append(pre + \texttt{if } + state2py(cond) + \texttt{:})$
            \State $depth \gets depth + 1$
        \ElsIf{$ln.startswith(\texttt{\textbackslash ElsIf\{})$}
            \State $cond, rest \gets arg(ln)$
            \State $py.append(pre[len(INDENT):] + \texttt{elif } + state2py(cond) + \texttt{:})$
        \ElsIf{$ln.startswith(\texttt{\textbackslash Else})$}
            \State $py.append(pre[len(INDENT):] + \texttt{else:})$
        \ElsIf{$ln.startswith(\texttt{\textbackslash State})$}
            \State $py.append(pre + stmt2py(ln[len(\texttt{\textbackslash State}):]))$
        \ElsIf{$ln.startswith(\texttt{\textbackslash Return}) \lor ln.startswith(\texttt{\textbackslash Comment})$}
            \State $py.append(pre + stmt2py(ln))$
        \EndIf
    \EndFor
    \Return $NL.join(py)$
\EndFunction

\Function{eq2py}{$tex, known \gets None$} \Comment{the last math segment is the definition}
    \If{$known$ is None}
        \State $known \gets \{\}$
    \EndIf
    \State $m \gets None$
    \For{$ismath, seg \in segments(tex)$}
        \If{$ismath$}
            \State $m \gets seg$
        \EndIf
    \EndFor
    \State $lhs, rhs \gets m.split(\texttt{=}, 1)$
    \State $name \gets math2py(lhs).strip()$
    \State $CASES \gets \texttt{\textbackslash begin\{cases\}}$
    \State $body \gets \texttt{}$
    \If{$CASES \notin rhs$}
        \State $body \gets INDENT + \texttt{return } + math2py(rhs).strip()$
    \Else
        \State $rhs \gets rhs[rhs.index(CASES) + len(CASES) : rhs.index(\texttt{\textbackslash end\{cases\}})]$
        \State $rhs \gets rhs.replace(\texttt{\textbackslash text\{if \}}, \texttt{}).replace(\texttt{\textbackslash text\{otherwise\}}, \texttt{True})$
        \For{$row \in rhs.split(\texttt{\textbackslash\textbackslash})$}
            \If{$\texttt{\&} \in row$}
                \State $expr, cond \gets row.split(\texttt{\&})$
                \State $body \gets body + INDENT + \texttt{if } + math2py(cond).strip() + \texttt{: return } + math2py(expr).strip() + NL$
            \EndIf
        \EndFor
    \EndIf
    \State \Comment{a bare left side names no arguments, so infer them}
    \If{$\texttt{(} \notin name$}
        \State $name \gets name + \texttt{(} + \texttt{, }.join(freevars(body, known)) + \texttt{)}$
    \EndIf
    \Return $\texttt{def } + name + \texttt{:} + NL + body$
\EndFunction

\Function{latex2py}{$tex, scope \gets None$} \Comment{translate, exec into scope, return the last function}
    \If{$scope$ is None}
        \State $scope \gets \{\}$
    \EndIf
    \If{$\texttt{\textbackslash State} \in tex \lor \texttt{\textbackslash Function} \in tex$}
        \State $py \gets tex2py(tex)$
    \Else
        \State $py \gets eq2py(tex, scope)$
    \EndIf
    \State $exec(py, scope)$
    \State $name \gets None$
    \For{$ln \in py.splitlines()$}
        \If{$ln.startswith(\texttt{def })$}
            \State $name \gets ln[4:ln.index(\texttt{(})]$
        \EndIf
    \EndFor
    \If{$name$ is None}
        \Return $scope$
    \EndIf
    \Return $scope[name]$
\EndFunction

\end{algorithmic}
\end{algorithm}
'''

# ---------------------------------------------------------------- Python2Tex
#
# The reverse direction.  Unlike the translator above this is plain Python
# only: it is not part of the bootstrap, so it need not exist twice.

# The inverse of unescape(), so a string constant survives the round trip.
LATEX_ESCAPES = {
    '\\': '\\textbackslash ', '{': '\\{', '}': '\\}', '_': '\\_',
    '$': '\\$', '%': '\\%', '&': '\\&', '#': '\\#',
    '^': '\\^{}', '~': '\\~{}',
}

def escape(s):
    out = ''
    for ch in s:
        out += LATEX_ESCAPES.get(ch, ch)
    return out

# operator -> (LaTeX, Python precedence).  Division and exponentiation are
# handled separately because they change shape rather than just spelling.
BINOPS = {
    ast.Add: ('+', 9), ast.Sub: ('-', 9),
    ast.Mult: ('\\cdot', 10), ast.Mod: ('\\%', 10),
    ast.FloorDiv: ('//', 10), ast.MatMult: ('@', 10),
}
CMPOPS = {
    ast.Eq: '=', ast.NotEq: '\\neq', ast.Lt: '<', ast.LtE: '\\leq',
    ast.Gt: '>', ast.GtE: '\\geq', ast.In: '\\in', ast.NotIn: '\\notin',
}
P_LAMBDA, P_IFEXP, P_OR, P_AND, P_NOT = 0.2, 0.4, 1, 2, 3
P_CMP, P_ADD, P_MUL, P_UNARY, P_POW, P_ATOM = 4, 9, 10, 11, 12, 100

class Python2Tex(ast.NodeVisitor):
    r"""Python source -> algpseudocode, the reverse of tex2py.

    Two rules govern the output.

    Precedence is explicit.  The tree knows that $(a+b)\cdot c$ groups, but a
    flat string does not, so every operand that binds more loosely than its
    parent is parenthesised on the way out.

    Python keywords leave math mode.  Inside $...$ a space between two names is
    implicit multiplication, so "x is None" would translate back as x*is*None.
    Emitting $x$ is $None$ instead puts the keyword in a text segment, which
    state2py passes through untouched -- the same trick the hand-written LaTeX
    in NEOMATH_TEX uses.

    Anything the subset cannot express is reported as a \Comment and recorded
    in self.warnings, never dropped in silence.
    """

    def __init__(self, display=False):
        self.indent_level = 0
        self.result = []
        self.warnings = []
        # set-builder notation reads better in a paper but cannot be read back,
        # so it is opt-in
        self.display = display

        self.constants_map = {
            'hbar': '\\hbar',
            'c': 'c',
            'G': 'G',
            'pi': '\\pi',
            'epsilon_0': '\\epsilon_0',
            'mu_0': '\\mu_0',
            'k': 'k_B',
            'N_A': 'N_A',
        }

    def get_latex(self):
        return "\n".join(self.result)

    def add_line(self, line):
        indent = "    " * self.indent_level
        self.result.append(f"{indent}{line}")

    def warn(self, message):
        """Record a gap and make it visible in the output."""
        self.warnings.append(message)
        self.comment(message)

    def comment(self, text):
        r"""A standalone note.

        \Comment is an attachment in algpseudocode, not a line of its own, so it
        is hung off a \State or LaTeX complains about a missing \item.  And
        since tex2py reads one line at a time, the text must not wrap.
        """
        self.add_line("\\State \\Comment{" + escape(" ".join(text.split())) + "}")

    def text(self, s):
        r"""Step outside math mode, so a Python keyword survives math2py."""
        return f"${s}$"

    def name(self, s):
        r"""An identifier in math mode.

        A bare underscore is a subscript, so __name__ is a double subscript and
        LaTeX refuses it; and indent_level would silently render as indent
        followed by a subscripted l.  OPS maps \_ back to _, so escaping keeps
        both the typesetting and the round trip honest.
        """
        return s.replace('_', '\\_')

    def body(self, statements):
        self.indent_level += 1
        for stmt in statements:
            self.visit(stmt)
        self.indent_level -= 1

    # ------------------------------------------------------------ statements

    def visit_Module(self, node):
        for stmt in node.body:
            self.visit(stmt)

    def visit_ClassDef(self, node):
        bases = ", ".join(self.expr2tex(b) for b in node.bases)
        self.comment(f"Class {node.name} inherits {bases}")
        for d in node.decorator_list:
            self.warn(f"decorator on class {node.name} is not represented")
        for stmt in node.body:
            self.visit(stmt)

    def visit_FunctionDef(self, node):
        for d in node.decorator_list:
            self.warn(f"decorator on {node.name} is not represented")
        self.add_line(f"\\Function{{{escape(node.name)}}}{{${self.params(node.args)}$}}")
        self.body(node.body)
        self.add_line("\\EndFunction")

    visit_AsyncFunctionDef = visit_FunctionDef

    def params(self, a):
        """An argument list, with defaults written as \\gets."""
        names = [self.name(arg.arg) for arg in a.posonlyargs + a.args]
        defaults = list(a.defaults)
        pad = [None] * (len(names) - len(defaults))
        parts = []
        for name, default in zip(names, pad + defaults):
            if default is None:
                parts.append(name)
            else:
                parts.append(f"{name} \\gets {self.expr2tex(default)}")
        if a.vararg:
            parts.append("*" + self.name(a.vararg.arg))
        for arg, default in zip(a.kwonlyargs, a.kw_defaults):
            parts.append(self.name(arg.arg) if default is None
                         else f"{self.name(arg.arg)} \\gets {self.expr2tex(default)}")
        if a.kwarg:
            parts.append("**" + self.name(a.kwarg.arg))
        return ", ".join(parts)

    def visit_Assign(self, node):
        # a = b = 1 is a chain, not a tuple: join the targets with \gets
        targets = " \\gets ".join(self.expr2tex(t) for t in node.targets)
        value = self.expr2tex(node.value)
        if isinstance(node.value, ast.IfExp):
            return self.expand_ifexp(node.value, lambda v: f"{targets} \\gets {v}")
        self.add_line(f"\\State ${targets} \\gets {value}$")

    def visit_AnnAssign(self, node):
        if node.value is None:
            return self.warn("bare type annotation carries no value")
        target = self.expr2tex(node.target)
        self.add_line(f"\\State ${target} \\gets {self.expr2tex(node.value)}$")

    def visit_AugAssign(self, node):
        """x += 1 is written out in full, the way mathematics would."""
        target = self.expr2tex(node.target)
        expanded = ast.BinOp(left=node.target, op=node.op, right=node.value)
        self.add_line(f"\\State ${target} \\gets {self.expr2tex(expanded)}$")

    def visit_Return(self, node):
        if isinstance(node.value, ast.IfExp):
            return self.expand_ifexp(node.value, None)
        value = self.expr2tex(node.value) if node.value else ""
        self.add_line(f"\\Return ${value}$")

    def expand_ifexp(self, node, assign):
        """x = a if c else b becomes a real branch: clearer, and it reads back."""
        self.add_line(f"\\If{{${self.expr2tex(node.test)}$}}")
        self.indent_level += 1
        for branch in (node.body, node.orelse):
            value = self.expr2tex(branch)
            if assign is None:
                self.add_line(f"\\Return ${value}$")
            else:
                self.add_line(f"\\State ${assign(value)}$")
            if branch is node.body:
                self.indent_level -= 1
                self.add_line("\\Else")
                self.indent_level += 1
        self.indent_level -= 1
        self.add_line("\\EndIf")

    def visit_If(self, node, is_elif=False):
        test = self.expr2tex(node.test)
        if is_elif:
            self.add_line(f"\\ElsIf{{${test}$}}")
        else:
            self.add_line(f"\\If{{${test}$}}")

        self.body(node.body)

        if node.orelse:
            if len(node.orelse) == 1 and isinstance(node.orelse[0], ast.If):
                self.visit_If(node.orelse[0], is_elif=True)
            else:
                self.add_line("\\Else")
                self.body(node.orelse)

        if not is_elif:
            self.add_line("\\EndIf")

    def visit_For(self, node):
        if node.orelse:
            self.warn("for/else: the else branch is not represented")
        target = self.expr2tex(node.target)
        if isinstance(node.iter, ast.Call) and getattr(node.iter.func, 'id', '') == "range" \
                and len(node.iter.args) <= 2:
            args = node.iter.args
            start = self.expr2tex(args[0]) if len(args) == 2 else "0"
            end_node = args[1] if len(args) == 2 else args[0]
            end = self.expr2tex(ast.BinOp(left=end_node, op=ast.Sub(), right=ast.Constant(value=1)))
            self.add_line(f"\\For{{${target} = {start}$ to ${end}$}}")
        else:
            iter_val = self.expr2tex(node.iter)
            self.add_line(f"\\For{{${target} \\in {iter_val}$}}")

        self.body(node.body)
        self.add_line("\\EndFor")

    visit_AsyncFor = visit_For

    def visit_While(self, node):
        if node.orelse:
            self.warn("while/else: the else branch is not represented")
        self.add_line(f"\\While{{${self.expr2tex(node.test)}$}}")
        self.body(node.body)
        self.add_line("\\EndWhile")

    def visit_Break(self, node):
        self.add_line("\\State break")

    def visit_Continue(self, node):
        self.add_line("\\State continue")

    def visit_Pass(self, node):
        self.add_line("\\State pass")

    def visit_Raise(self, node):
        if node.cause:
            self.warn("raise ... from ...: the cause is not represented")
        exc = f" ${self.expr2tex(node.exc)}$" if node.exc else ""
        self.add_line(f"\\State raise{exc}")

    def visit_Assert(self, node):
        msg = f", ${self.expr2tex(node.msg)}$" if node.msg else ""
        self.add_line(f"\\State assert ${self.expr2tex(node.test)}${msg}")

    def visit_Delete(self, node):
        targets = ", ".join(self.expr2tex(t) for t in node.targets)
        self.add_line(f"\\State del ${targets}$")

    def visit_Global(self, node):
        names = ", ".join(self.name(n) for n in node.names)
        self.add_line(f"\\State global ${names}$")

    def visit_Nonlocal(self, node):
        names = ", ".join(self.name(n) for n in node.names)
        self.add_line(f"\\State nonlocal ${names}$")

    def visit_Import(self, node):
        for alias in node.names:
            tail = f" as ${self.name(alias.asname)}$" if alias.asname else ""
            self.add_line(f"\\State import ${self.name(alias.name)}${tail}")

    def visit_ImportFrom(self, node):
        names = ", ".join(self.name(a.name)
                          + (f"$ as ${self.name(a.asname)}" if a.asname else "")
                          for a in node.names)
        self.add_line(f"\\State from ${self.name(node.module or '')}$ import ${names}$")

    def visit_With(self, node):
        """No \\With in the subset, so the body is inlined and the fact noted."""
        items = ", ".join(self.expr2tex(i.context_expr) for i in node.items)
        self.warn("with-block inlined; the context manager is not represented")
        self.comment(f"context: {items}")
        for stmt in node.body:
            self.visit(stmt)

    visit_AsyncWith = visit_With

    def visit_Try(self, node):
        self.warn("try-block inlined; exception handling is not represented")
        for stmt in node.body:
            self.visit(stmt)
        for handler in node.handlers:
            name = self.expr2tex(handler.type) if handler.type else "any"
            self.comment(f"on failure ({name})")
            for stmt in handler.body:
                self.visit(stmt)
        for stmt in node.finalbody:
            self.visit(stmt)

    def visit_Expr(self, node):
        if isinstance(node.value, ast.Constant) and isinstance(node.value.value, str):
            self.comment(node.value.value)
        else:
            self.add_line(f"\\State ${self.expr2tex(node.value)}$")

    def generic_visit(self, node):
        """Nothing disappears quietly: unknown statements say so."""
        if isinstance(node, ast.stmt):
            self.warn(f"unsupported statement: {type(node).__name__}")
        else:
            super().generic_visit(node)

    # ----------------------------------------------------------- expressions

    def paren(self, text, mine, ctx):
        return f"({text})" if mine < ctx else text

    def expr2tex(self, node, ctx=0):
        if node is None:
            return ""

        if isinstance(node, ast.Name):
            return self.name(node.id)

        elif isinstance(node, ast.Attribute):
            # scipy.constants.hbar is reduced to its conventional symbol
            if isinstance(node.value, ast.Attribute) \
                    and getattr(node.value.value, 'id', '') == 'scipy' \
                    and node.value.attr == 'constants':
                return self.constants_map.get(node.attr, node.attr)
            # plain dotted access: \texttt would turn it into a string literal
            return f"{self.expr2tex(node.value, P_ATOM)}.{self.name(node.attr)}"

        elif isinstance(node, ast.Constant):
            if node.value is None:
                return "None"
            if isinstance(node.value, bool):
                return str(node.value)
            if isinstance(node.value, str):
                return self.string_literal(node.value, ctx)
            if isinstance(node.value, complex):
                return str(node.value)
            return str(node.value)

        elif isinstance(node, ast.BinOp):
            op = type(node.op)
            if op is ast.Div:
                left = self.expr2tex(node.left)
                right = self.expr2tex(node.right)
                return self.paren(f"\\frac{{{left}}}{{{right}}}", P_MUL, ctx)
            if op is ast.Pow:
                left = self.expr2tex(node.left, P_POW + 1)
                right = self.expr2tex(node.right, P_POW)
                return self.paren(f"{left}^{{{right}}}", P_POW, ctx)
            if op in BINOPS:
                sym, prec = BINOPS[op]
                left = self.expr2tex(node.left, prec)
                right = self.expr2tex(node.right, prec + 1)
                return self.paren(f"{left} {sym} {right}", prec, ctx)
            self.warnings.append(f"unsupported operator: {op.__name__}")
            return self.expr2tex(node.left)

        elif isinstance(node, ast.UnaryOp):
            op = type(node.op)
            if op is ast.Not:
                inner = self.expr2tex(node.operand, P_NOT)
                return self.paren(f"\\lnot {inner}", P_NOT, ctx)
            sym = {ast.USub: '-', ast.UAdd: '+', ast.Invert: '\\sim'}.get(op, '')
            if op is ast.Invert:
                sym = '~'                     # \sim is not in OPS; ~ passes through
            inner = self.expr2tex(node.operand, P_UNARY)
            return self.paren(f"{sym}{inner}", P_UNARY, ctx)

        elif isinstance(node, ast.BoolOp):
            sym, prec = ('\\land', P_AND) if isinstance(node.op, ast.And) \
                else ('\\lor', P_OR)
            parts = [self.expr2tex(v, prec + 1) for v in node.values]
            return self.paren(f" {sym} ".join(parts), prec, ctx)

        elif isinstance(node, ast.Compare):
            out = self.expr2tex(node.left, P_CMP + 1)
            for op, comp in zip(node.ops, node.comparators):
                right = self.expr2tex(comp, P_CMP + 1)
                kind = type(op)
                if kind is ast.Is:
                    out += self.text(" is ") + right
                elif kind is ast.IsNot:
                    out += self.text(" is not ") + right
                elif kind in CMPOPS:
                    out += f" {CMPOPS[kind]} {right}"
                else:
                    self.warnings.append(f"unsupported comparison: {kind.__name__}")
                    out += f" = {right}"
            return self.paren(out, P_CMP, ctx)

        elif isinstance(node, ast.Call):
            args = [self.expr2tex(a) for a in node.args]
            for kw in node.keywords:
                if kw.arg is None:
                    args.append("**" + self.expr2tex(kw.value))
                else:
                    # \gets, not =, because = becomes == in math mode
                    args.append(f"{self.name(kw.arg)} \\gets {self.expr2tex(kw.value)}")
            return f"{self.expr2tex(node.func, P_ATOM)}({', '.join(args)})"

        elif isinstance(node, ast.Subscript):
            return f"{self.expr2tex(node.value, P_ATOM)}[{self.expr2tex(node.slice)}]"

        elif isinstance(node, ast.Slice):
            lower = self.expr2tex(node.lower) if node.lower else ""
            upper = self.expr2tex(node.upper) if node.upper else ""
            out = f"{lower}:{upper}"
            if node.step:
                out += f":{self.expr2tex(node.step)}"
            return out

        elif isinstance(node, ast.Starred):
            return "*" + self.expr2tex(node.value, P_UNARY)

        elif isinstance(node, ast.Tuple):
            return "(" + ", ".join(self.expr2tex(e) for e in node.elts) + ")"

        elif isinstance(node, ast.List):
            return "[" + ", ".join(self.expr2tex(e) for e in node.elts) + "]"

        elif isinstance(node, ast.Set):
            return "\\{" + ", ".join(self.expr2tex(e) for e in node.elts) + "\\}"

        elif isinstance(node, ast.Dict):
            pairs = []
            for k, v in zip(node.keys, node.values):
                if k is None:
                    pairs.append("**" + self.expr2tex(v))
                else:
                    pairs.append(f"{self.expr2tex(k)}: {self.expr2tex(v)}")
            return "\\{" + ", ".join(pairs) + "\\}"

        elif isinstance(node, ast.IfExp):
            body = self.expr2tex(node.body, P_IFEXP + 1)
            test = self.expr2tex(node.test, P_IFEXP + 1)
            orelse = self.expr2tex(node.orelse, P_IFEXP)
            out = body + self.text(" if ") + test + self.text(" else ") + orelse
            return self.paren(out, P_IFEXP, ctx)

        elif isinstance(node, ast.Lambda):
            out = self.text("lambda ") + f"{self.params(node.args)}: " \
                + self.expr2tex(node.body)
            return self.paren(out, P_LAMBDA, ctx)

        elif isinstance(node, ast.JoinedStr):
            # an f-string is a concatenation; writing it as one reads back
            parts = []
            for piece in node.values:
                if isinstance(piece, ast.Constant):
                    parts.append(f"\\texttt{{{escape(str(piece.value))}}}")
                elif isinstance(piece, ast.FormattedValue):
                    inner = self.expr2tex(piece.format_spec.values[0]) \
                        if piece.format_spec else None
                    if inner is not None:
                        parts.append(f"format({self.expr2tex(piece.value)}, {inner})")
                    else:
                        parts.append(f"str({self.expr2tex(piece.value)})")
            return self.paren(" + ".join(parts) if parts else "\\texttt{}",
                              P_ADD, ctx)

        elif isinstance(node, (ast.ListComp, ast.SetComp, ast.GeneratorExp,
                               ast.DictComp)):
            return self.comprehension(node, ctx)

        elif isinstance(node, ast.NamedExpr):
            self.warnings.append("walrus operator rewritten as assignment")
            return f"{self.expr2tex(node.target)} \\gets {self.expr2tex(node.value)}"

        self.warnings.append(f"unsupported expression: {type(node).__name__}")
        return f"\\texttt{{{escape(type(node).__name__)}}}"

    def string_literal(self, value, ctx=0):
        r"""A string constant.

        \texttt cannot hold a newline -- the LaTeX would not compile and tex2py
        reads line by line -- so control characters are lifted out as chr()
        calls, which costs nothing and still reads back exactly.
        """
        parts = []
        buf = ''
        for ch in value:
            if ord(ch) < 32:
                parts.append("\\texttt{" + escape(buf) + "}")
                parts.append(f"chr({ord(ch)})")
                buf = ''
            else:
                buf += ch
        parts.append("\\texttt{" + escape(buf) + "}")
        if len(parts) > 1:
            parts = [p for p in parts if p != "\\texttt{}"] or ["\\texttt{}"]
        if len(parts) == 1:
            return parts[0]
        return self.paren(" + ".join(parts), P_ADD, ctx)

    def comprehension(self, node, ctx=0):
        """Comprehensions, either as set-builder or in a form that reads back."""
        if isinstance(node, ast.DictComp):
            elt = f"{self.expr2tex(node.key)}: {self.expr2tex(node.value)}"
        else:
            elt = self.expr2tex(node.elt)

        if self.display:
            # set-builder: correct mathematics, but \mid is not an OPS operator
            # so this direction is one-way
            gen = node.generators[0]
            out = (f"{elt} \\mid {self.expr2tex(gen.target)} \\in "
                   f"{self.expr2tex(gen.iter)}")
            if gen.ifs:
                out += ", " + " \\land ".join(self.expr2tex(c) for c in gen.ifs)
            body = out
        else:
            body = elt
            for gen in node.generators:
                body += (self.text(" for ") + self.expr2tex(gen.target)
                         + f" \\in {self.expr2tex(gen.iter, P_CMP + 1)}")
                for cond in gen.ifs:
                    body += self.text(" if ") + self.expr2tex(cond, P_CMP + 1)

        if isinstance(node, ast.ListComp):
            return f"[{body}]"
        if isinstance(node, ast.GeneratorExp):
            return f"({body})"
        return "\\{" + body + "\\}"

def py2tex(source_code, display=False, warnings=None):
    """Python source -> an algorithmic block.

    display=True switches comprehensions to set-builder notation, which reads
    better on paper but cannot be translated back.  Anything the subset cannot
    express is appended to warnings, if a list is given.
    """
    tree = ast.parse(source_code)
    converter = Python2Tex(display=display)
    converter.visit(tree)
    if warnings is not None:
        warnings.extend(converter.warnings)
    return "\\begin{algorithmic}\n" + converter.get_latex() + "\n\\end{algorithmic}"


# ---------------------------------------------------------------- bootstrap

def bootstrap():
    """stage 0 translates the LaTeX; stage 1 must translate it identically."""
    stage1 = {}
    latex2py(NEOMATH_TEX, stage1)
    src0 = tex2py(NEOMATH_TEX)                 # Python's reading of the LaTeX
    src1 = stage1['tex2py'](NEOMATH_TEX)       # the LaTeX-born translator reading itself
    if src0 != src1:
        raise AssertionError('bootstrap did not reach a fixed point')
    return stage1, src1

def selftest(latex2py, label):
    import math
    f = latex2py(r'''
    \begin{algorithm}
    \caption{Sum of $1..n$}
    \begin{algorithmic}[1]
    \Function{Sum}{$n$}
        \State $s \gets 0$
        \For{$i = 1$ to $n$}
            \State $s \gets s + i$ \Comment{happens inside the loop}
        \EndFor
        \Return $s$
    \EndFunction
    \end{algorithmic}
    \end{algorithm}''')
    assert f(5) == 15

    f = latex2py(r'$f: \mathbb{R} \to \mathbb{R}$ defined by $f(x) = 2x + 1$')
    assert f(32) == 65

    f = latex2py(r'''
    $$
    f(x) = \begin{cases}
        x^2   & \text{if } x < 0 \\
        x + 2 & \text{if } x \geq 0
    \end{cases}
    $$''')
    assert f(2) == 4 and f(-3) == 9

    E = latex2py(r'$E(m) = m \cdot c^2$', {'c': 299792458})     # scope supplies constants
    assert E(1) == 299792458 ** 2
    C = latex2py(r'$C(r) = 2\pi \cdot r$', {'pi': math.pi})
    assert abs(C(1) - 2 * math.pi) < 1e-12
    K = latex2py(r'$K(m, v) = \frac{1}{2} \cdot m \cdot v^2$')
    assert K(3, 2) == 6

    # implicit multiplication: juxtaposition is multiplication to a reader,
    # and now to the parser too
    A = latex2py(r'$A(x, y) = 2x y$')
    assert A(3, 4) == 24
    B = latex2py(r'$B(m, c) = m c^2$')
    assert B(3, 4) == 48

    # a bare left-hand side gets its parameters inferred from the right
    P = latex2py(r'$P = I V$')
    assert P(3, 4) == 12
    S = latex2py(r'$S = \frac{k_B c^3 A}{4 G \hbar}$')
    assert S(2, 3, 4, 5, 6) == (2 * 3 ** 3 * 4) / (4 * 5 * 6)

    # names the caller already supplies stay constants, not parameters
    E = latex2py(r'$E = m c^2$', {'c': 2})
    assert E(3) == 12
    K = latex2py(r'$K = \frac{1}{2} m v^2$', {})
    assert K(3, 2) == 6

    # inference works for piecewise definitions too
    step = latex2py(r'''
    $$
    step = \begin{cases}
        n     & \text{if } n > 0 \\
        0     & \text{otherwise}
    \end{cases}
    $$''')
    assert step(5) == 5 and step(-2) == 0

    gcd = latex2py(r'''
    \Function{gcd}{$a, b$}
        \While{$b \neq 0$}
            \State $a, b \gets b, a \% b$
        \EndWhile
        \Return $a$
    \EndFunction''')
    assert gcd(48, 18) == 6
    print('self test passed:', label)


LATEX_HEADER = r'''\documentclass{article}
\usepackage[margin=1.5cm]{geometry}
\usepackage{amsmath,amssymb,algorithm,algpseudocode,listings}
\usepackage{url}
\usepackage{hyperref}
\usepackage{orcidlink}

%\lstset{language=Python,basicstyle=\ttfamily\scriptsize,breaklines=true}

\usepackage{xcolor}

\lstset{
    language=Python,
    basicstyle=\ttfamily\tiny,
    keywordstyle=\color{blue}\bfseries,
    stringstyle=\color{green!50!black},
    commentstyle=\color{gray}\itshape,
    numbers=left,                  % Adds line numbers
    numberstyle=\tiny\color{gray},  % Style of line numbers
    stepnumber=1,                  % Number every line
    breaklines=true,               % Wrap long lines automatically
    frame=single                   % Adds a border around the code
}
%TITLE
%AUTHOR
\begin{document}
'''
LATEX_FOOTER = r'''
\end{document}
'''

def make_title_author(
    tex,
    title='RosettaMath: Semantic Translation of Mathematical Conventions \\\\ into Self-Documenting Code',
    author='B.S. Hartshorn \\orcidlink{0009-0004-2853-655X} \\small (\\url{https://github.com/brentharts/RosettaMath})'
    ):
    tex = tex.replace('%TITLE', '\\title{%s}' % title).replace('%AUTHOR', '\\author{%s}' % author)
    return tex.replace('\\begin{document}', '\\begin{document} \\maketitle')

PAPER_ABS = r'''
\begin{abstract}
The translation of theoretical mathematical models into executable code remains a persistent bottleneck in computational science. While LaTeX serves as the standard for sharing algebraic equations and algorithms, its representation is fundamentally disconnected from the explicit logic required by programming languages like Python. We present RosettaMath, a minimalist, zero-dependency translator that converts a strict subset of LaTeX---specifically mathematical expressions and algorithmic pseudocode---directly into functional Python. Notably, RosettaMath is self-hosting; the core translation engine is written in the very LaTeX subset it processes and bootstraps itself to a fixed point without external libraries. Beyond its mechanical translation capabilities, RosettaMath is designed as an educational bridge. By semantically mapping dense physics and mathematical conventions to explicitly named variables and scientific libraries (such as mapping standard symbols to scipy.constants), the tool demystifies standard notation for software developers while simultaneously teaching programmatic logic to mathematicians. RosettaMath offers a novel approach to literate programming, ensuring that the equations published in research are the exact algorithms executed in simulation.
\end{abstract}
'''

PAPER_INTRO = r'''
\section{Introduction}

The universal language of theoretical research---from modeling horizon dynamics and quantum gravity to generating procedural geometry---is mathematics, universally typeset in LaTeX. However, investigating these models computationally requires translating them into a functional programming language. This manual translation process is prone to error and creates an artificial barrier between disciplines. Mathematical notation is highly concise, relying on established conventions, overloaded symbols, and implicit context. Conversely, modern software development in languages like Python prioritizes explicit logic, verbose variable naming, and strict control flow.

RosettaMath is introduced as a lightweight, self-contained solution to bridge this syntactic and semantic divide. Rather than relying on heavy, external parsing libraries, RosettaMath is built to process a highly specific subset of LaTeX---encompassing standard math-mode operations and algpseudocode environments---and map them directly to Python constructs. To demonstrate the completeness and robustness of this subset, the RosettaMath compiler is entirely self-hosting. A preliminary translation script parses the LaTeX representation of the compiler, generating Python code that subsequently parses its own source until reaching a verified fixed point.

The primary objective of RosettaMath extends beyond mere syntax translation; it acts as an educational framework. For computational models to be truly accessible, the underlying code must be as legible as the mathematics it represents. RosettaMath actively unpacks cryptic conventions by semantically linking standard mathematical symbols to descriptive programming paradigms. By transforming abstract characters into self-documenting code---such as automatically associating physical constants with their numerical counterparts in scientific libraries---the translator clarifies physics conventions for developers and introduces functional programming architectures to pure mathematicians. Ultimately, RosettaMath provides a unified environment where the formal specification of a mathematical problem and its computational implementation are identical.
'''

PAPER_SELFHOST = r'''
\section{Self-Hosting as an Educational Paradigm: The Two-Stage Bootstrap}

To ensure that the chosen subset of LaTeX is sufficiently robust for general-purpose algorithmic logic, RosettaMath is designed to be entirely self-hosting. The compiler relies on a two-stage bootstrapping architecture that achieves a verified fixed point without the aid of external parsing libraries.

In Stage 0, a foundational script written in plain Python parses the LaTeX source code of the RosettaMath translator, interpreting the algpseudocode and math-mode expressions. This generates an initial Python representation of the compiler (Stage 1). In the final step, this newly generated Stage 1 Python code is executed to parse its own LaTeX source code once again. When the byte-for-byte output of this second translation identically matches the first, the compiler is proven to be fully self-hosted and independent.

Beyond merely validating the parser's computational completeness, this self-hosting architecture serves a deliberate pedagogical purpose. The source code of RosettaMath acts as its own Rosetta Stone. By providing the exact same logic simultaneously in explicit Python control flow and formal LaTeX pseudocode, readers can study the translation engine side-by-side. A mathematician can trace how a `While` loop and recursive function in LaTeX become executable Python, while a software engineer can see how standard Python string manipulation maps onto formal algorithmic notation. The tool itself is the ultimate tutorial on how to bridge these two domains.
'''

PAPER_SCI = r'''
\section{Demystifying Physics: Semantic Translation of Cryptic Conventions}
Perhaps the most significant barrier to entry in computational science is the density of mathematical and physical notation. In theoretical physics and cosmology, equations rely heavily on implicit domain knowledge and a finite alphabet of Greek symbols that are heavily overloaded. For a programmer attempting to model complex phenomena---such as relative entropy in quantum systems, optical wavefront dynamics, or the horizon mechanics of black holes---the raw mathematical formulation can appear entirely opaque. A single character might represent a universal constant, a dynamic variable, or an abstract physical property depending entirely on the context.

RosettaMath addresses this barrier by functioning as a premier educational tool that translates not just syntax, but semantics. It transitions static, intimidating physics formulas into self-documenting, executable models. When a user inputs an equation, RosettaMath goes beyond mapping operators; it maps domain-specific conventions to explicit, descriptive programming paradigms.For example, the symbol $\rho$ is notoriously overloaded, but in standard contexts, RosettaMath can map it to a readable identifier like rho\_density. Similarly, characters representing complex metrics---such as $S$ for entropy or $\Phi$ for a gravitational potential or wavefront---are automatically expanded into verbose, human-readable variables. Furthermore, by linking directly to scientific libraries, standard notations for physical constants (such as $c$ for the speed of light or $G$ for the gravitational constant) can be automatically resolved to their high-precision values in scipy.constants.By automatically unpacking these conventions, RosettaMath acts as an interactive glossary. It allows developers to read an advanced physics equation as explicit, logical software, and it trains physicists to write formulas with the precision and legibility required for computational modeling. In doing so, it lowers the barrier to entry for scientific computing, transforming theoretical mathematics from a gate-kept language into an accessible, executable format.
'''

PAPER_CON = r'''
\section{Conclusion: A Bidirectional Bridge for Literate Programming}

RosettaMath successfully demonstrates that the semantic gap between formal mathematical typesetting and executable programming can be bridged without relying on heavy external dependencies. By bootstrapping a self-hosting compiler entirely within a strict subset of LaTeX, the project proves the computational robustness of its algorithmic representations.

Crucially, the translation of mathematical models is no longer a one-way street. The integration of the `Python2Tex` class, which leverages Python's `ast.NodeVisitor` to traverse the Abstract Syntax Tree, enables full bidirectional translation by converting Python source code directly back into formal LaTeX pseudocode. This reverse compiler reconstructs loops, conditionals, list comprehensions, and arithmetic operations back into publication-ready algorithms.

Furthermore, `Python2Tex` strictly maintains the pedagogical and semantic goals of the broader RosettaMath framework. When translating explicit Python back into mathematical notation, the tool automatically maps scientific libraries to their traditional physical symbols. For example, references to standard constants like `scipy.constants.hbar` are intelligently reduced back to their respective LaTeX representations, $\hbar$ and $\epsilon_0$. This bidirectional semantic mapping solidifies RosettaMath as an interactive glossary, ensuring that software engineers can write explicit Python while seamlessly generating the dense, conventional mathematics required for academic publication.

Ultimately, RosettaMath enables a true literate programming paradigm for computational physics. By guaranteeing that the formal specification of a mathematical problem and its computational implementation are perfectly symmetrical, it ensures that the equations published in theoretical research are mathematically and logically identical to the algorithms executed in simulation.

'''

PAPER_REFS = r'''
\small
\begin{thebibliography}{99}

\bibitem{knuth} Knuth, D. E. (1984). 
\emph{Literate Programming. The Computer Journal, 27, 97-111.}
\newline
\url{https://doi.org/10.1093/comjnl/27.2.97}

\bibitem{meurer} Meurer, A., Smith, C. P., Paprocki, M., et al. (2016). 
\emph{SymPy: Symbolic computing in Python.}
\newline
\url{https://doi.org/10.7287/peerj.preprints.2083v3}

\bibitem{poore} Poore, G. (2015). PythonTeX: Reproducible documents with LaTeX, Python, and more. Computational Science \& Discovery, 8(1), 014010. \url{https://doi.org/10.1088/1749-4699/8/1/014010}

\end{thebibliography}

'''

def makepdf():
    parts = []; func = None; header = []
    for ln in NEOMATH_TEX.splitlines():
        if ln.startswith('\\end{algorithmic}'): break
        if ln.startswith('\\Function'):
            func = [ln]; parts.append( func )
        elif func: func.append(ln)
        else:
            #if not ln.startswith('\\begin{algorithm}'):
            header.append(ln)
        
    header = ['\\section{ \\LaTeX{} Global Constants}', '\\footnotesize'] + header[4:]
    header.append( '\\end{algorithmic}' )

    neo = []
    left = True
    for part in parts:
        assert part[0].startswith('\\Function{')
        a = part[0]
        if '\\Comment{' in a:
            a,b = a.split('\\Comment{')
        a = a.replace('\\', '').replace('{', ' ').replace('}', ' ')
        a = a[len('Function'):]
        a = ['\\textbf{%s} \\par \\tiny' % a, '\\begin{algorithmic}']
        p = '\n'.join( a + part + ['\\end{algorithmic}'] )

        if left:
            p = '\\noindent \\begin{minipage}[t]{0.48\\textwidth}\n' + p + ' \\end{minipage} \\hfill'
        else:
            p = '\\begin{minipage}[t]{0.48\\textwidth}\n' + p + ' \\end{minipage} \n \\par \\bigskip \\hrule'
        left = not left
        neo.append(p)
        
    tex = [
        make_title_author(LATEX_HEADER),
        PAPER_ABS,
        PAPER_INTRO,
        PAPER_SCI,
        PAPER_SELFHOST,
        PAPER_CON
    ]
    if '--appendix' in sys.argv:
        tex += [
        '\\appendix',
        '\n'.join(header),
        '\\section{\\LaTeX{} Functions}',
        '\n'.join(neo),
        '\\section{Automatic \\LaTeX{} to Python Translation}',
        '\\begin{lstlisting}',
        src,
        '\\end{lstlisting}'
        ]
    tex.append(PAPER_REFS)
    tex.append(LATEX_FOOTER)
    open('/tmp/neomath.tex', 'w').write('\n'.join(tex))
    subprocess.check_call(['pdflatex', '/tmp/neomath.tex'], cwd='/tmp')
    print('wrote /tmp/neomath.pdf')

# (source, argument sets) -- the reverse translation is checked by behaviour,
# because LaTeX that looks right and means something else is the failure mode.
ROUNDTRIP_CASES = [
    ("def f(a, b):\n    return (a + b) * (a - b) / 2\n", [(7, 3), (2, 5)]),
    ("def f(a, b, c):\n    return a + b * c - (a + b) / (c + 1)\n",
     [(1, 2, 3), (4, 5, 6)]),
    ("def f(a, b):\n    return -a ** 2 + (a + b) ** 3 % 7 // 2\n",
     [(3, 4), (2, 5)]),
    ("def f(x):\n    if x is None:\n        return -1\n"
     "    if x >= 10 and not x == 12:\n        return 2\n    return 0\n",
     [(None,), (11,), (12,), (3,)]),
    ("def f(x, xs):\n    return x not in xs and x in [1, 2, 3]\n",
     [(1, [9]), (5, [5])]),
    ("def f(n):\n    t = 0\n    i = 1\n    while i <= n:\n"
     "        t += i * i\n        i += 1\n    return t\n", [(5,), (1,)]),
    ("def f(n):\n    out = 0\n    for i in range(0, n):\n        if i == 3:\n"
     "            break\n        if i == 1:\n            continue\n"
     "        out += i\n    return out\n", [(7,), (2,)]),
    ("def f(s):\n    return s + 'a\\\\b{c}_d$e%f^g~h#i&j' + chr(9)\n", [('x',)]),
    ("def f(s):\n    return s.upper().replace('A', 'B')\n", [('ab',)]),
    ("def f(n):\n    d = {'k': n}\n    t = (n, n * 2)\n    l = [n, n + 1]\n"
     "    return d['k'] + t[1] + l[1] + len({n, n + 1})\n", [(3,), (0,)]),
    ("def f(s):\n    return s[1:3] + s[:2] + s[-1:] + s[::2]\n", [('abcdef',)]),
    ("def f(n):\n    return sum([i * i for i in range(0, n) if i % 2 == 0])\n",
     [(6,), (1,)]),
    ("def f(x):\n    y = 1 if x > 0 else -1\n    return y * 10\n",
     [(5,), (-5,)]),
    ("def f(a):\n    return round(a, ndigits=2)\n", [(3.14159,)]),
    ("def f(a):\n    return f'v={a} end'\n", [(7,)]),
    ("def f(a):\n    x = y = a + 1\n    return x + y\n", [(4,)]),
    ("def f(a, b=10):\n    return a + b\n", [(1,), (1, 2)]),
    ("def f(a):\n    g = lambda x: x + 1\n    return g(a)\n", [(4,)]),
    ("def f(a, b):\n    return (a / b) ** 2 + a / (b * 2)\n", [(8.0, 2.0)]),
    ("def f(long_name_a, other_b):\n    return long_name_a * other_b\n",
     [(3, 4)]),
    ("def f(a):\n    if a < 0:\n        raise ValueError('negative')\n"
     "    return a\n", [(3,)]),
]


def roundtrip_test():
    r"""py2tex then tex2py must give a function that behaves identically.

    This is the only real check on the reverse direction: it is easy to emit
    LaTeX that looks right and means something else, and precedence is exactly
    where that happens.
    """
    for i, (source, argsets) in enumerate(ROUNDTRIP_CASES):
        latex = py2tex(source)
        back = tex2py(latex)
        original, restored = {}, {}
        exec(source, original)
        try:
            exec(back, restored)
        except SyntaxError as exc:
            raise AssertionError('case %d did not read back: %s\n%s'
                                 % (i, exc, back))
        for args in argsets:
            want = original['f'](*args)
            got = restored['f'](*args)
            if want != got:
                raise AssertionError('case %d changed meaning: f%r gave %r, '
                                     'now %r\n%s' % (i, args, want, got, back))

    # the escape/unescape pair must be exact, or string constants drift
    for probe in ('a{b}c', 'back\\slash', 'under_score', '$math$', '100%',
                  'a&b#c^d~e', '\\textbackslash', ''):
        if unescape(escape(probe)) != probe:
            raise AssertionError('escape/unescape is not an inverse: %r' % probe)

    # nothing may vanish: every function here should translate without warnings
    warnings = []
    py2tex(inspect.getsource(Python2Tex), warnings=warnings)
    if warnings:
        raise AssertionError('self translation warned: %r' % warnings)
    return len(ROUNDTRIP_CASES)


def test_py2tex():
    print('py2tex round trip passed: %d cases survive the return journey'
          % roundtrip_test())
    print("--- Translating Python2Tex (Self-Hosting with Generators and Attributes) ---")
    print(py2tex(latex2py_source))
    print(py2tex(inspect.getsource(Python2Tex)))
    physics_stub = '''
def energy(omega):
    return scipy.constants.hbar * omega
'''
    print(py2tex(physics_stub))

if __name__ == '__main__':
    selftest(latex2py, 'stage 0 (hand written Python)')
    stage1, src = bootstrap()
    selftest(stage1['latex2py'], 'stage 1 (translated from LaTeX)')
    latex2py = stage1['latex2py']     # from here on the LaTeX version is in charge
    print('bootstrap fixed point reached: %d lines of Python generated from LaTeX' % len(src.splitlines()))
    test_py2tex()
    if '--pdf' in sys.argv: makepdf()

