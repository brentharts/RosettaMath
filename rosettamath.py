#!/usr/bin/env python3
import os, sys, ast, subprocess

__doc__ = '''

Design Goals:

    Support a minimal subset of LaTeX, that can be transformed into Python.
    Small, and self-contained, no external libraries, or programs.  
    The exception is pdflatex and evince in a subprocess, this is just for testing.

Bootstrapping Notes:

    Our goal is to first write the basic translator in Python (latex2py),
    Then we redefine latex2py in LaTex, and use latex2py to define a new latex2py function,
    the tricky part, LaTex can not easily express everything that Python can do, we need
    some kind of hybrid.
    In theory, once we have bootstrapped latex2py, we should be able to continue to expand
    this script using mostly LaTeX and only use Python where we need to.

Python Notes:

    Note the use of old style string formatting, "foo %s bar" % "hello",
    we avoid using the new f"{}" format strings, because LaTeX uses "{}",
    and this makes things confusing.

LaTex Notes:

    Note the package{algorithm} and package{algpseudocode} seem to be the best way to
    write Python code inside of LaTeX, with simple parsing and transformation back to Python.
    Note, we also want to support math expressions wrapped in $$, because that is common.
    We can introduce our own LaTeX commands if needed, and put them in LATEX_HEADER.


Research Notes:

https://tex.stackexchange.com/questions/37094/what-is-the-recommended-way-to-assign-a-value-to-a-variable-and-retrieve-it-for

https://medium.com/bitgrit-data-science-publication/latexify-writing-latex-with-python-6c0fa4b2e9d5

https://github.com/google/latexify_py

https://github.com/alvinwan/tex2py
https://github.com/lericson/pseudopython
https://github.com/cairomassimo/py2tex

'''

DEBUG = 1

LATEX_HEADER = r'''
\documentclass{article}
\usepackage{pgffor} % Standard package for loops
\usepackage{amsmath}  % for cases and others
\usepackage{amssymb}   % for \mathbb
\usepackage{algorithm}
\usepackage{algpseudocode}
\usepackage{listings}
\usepackage{xcolor}

\lstset{
    language=Python,
    basicstyle=\ttfamily\footnotesize,
    keywordstyle=\color{blue}\bfseries,
    stringstyle=\color{green!50!black},
    commentstyle=\color{gray}\itshape,
    numbers=left,                  % Adds line numbers
    numberstyle=\tiny\color{gray},  % Style of line numbers
    stepnumber=1,                  % Number every line
    breaklines=true,               % Wrap long lines automatically
    frame=single                   % Adds a border around the code
}

\begin{document}
'''
LATEX_FOOTER = r'''
\end{document}
'''


LATEX2PYOPS = {
    r'\geq' : '>=',
    r'\gets': '=',
    ## TODO, more...
}

def latex2def(tex, full_latex, verify=0):
    wrap = False
    if '=' not in tex:
        tex = '_func() = \n' + tex
        wrap = True
    head = tex[ 0 : tex.index('=') ]
    head = 'def ' + head + ':'
    func = ast.parse( head + 'pass' ).body[0]
    args = [arg.arg for arg in func.args.args]
    if DEBUG:
        print(func)
        print('Function name:', func.name)
        print('Function args:', args)

    body = ['\tr"""' + full_latex + '"""']
    in_case = in_foreach = False
    for ln in tex[ tex.index('=')+1 : ].splitlines():
        ln = ln.strip()
        if ln.startswith('%'): continue
        if ln.endswith(r'\\'): ln = ln[:-2]
        if DEBUG: print(ln)
        if ln== r'\begin{cases}':
            in_case = True
            continue
        elif ln== r'\end{cases}':
            in_case = False
            continue
        if ln.startswith(r'\foreach '):
            assert ln.endswith('{')
            #assert ln.startswith(r'\foreach \')
            ln = ln[:-1] + ':'
            foreach_var = '\\' + ln.split('\\')[-1].split()[0]
            ln = ln.replace(r'\foreach ','for ').replace('\\', '')
            ln = ln.replace('{', 'range(').replace('...,','').replace('}',')')
            #print(ln)
            in_foreach = True
            body.append('\t' + ln)
            continue
        elif in_foreach:
            if ln=='}':
                in_foreach = False
                continue
            #print('in foreach', ln)
            #print('in foreach var', foreach_var)
            ln = 'print(f"%s")' % ln.replace(foreach_var, '{'+foreach_var[1:]+'}')
            body.append('\t\t' + ln)
            continue

        if '^' in ln: ln = ln.replace('^', '**')
        if '&' in ln: ln = ln.replace('&', '').strip()
        for key in LATEX2PYOPS:
            if key in ln: ln = ln.replace(key, LATEX2PYOPS[key])
        if in_case:
            assert r'\text{if }' in ln
            a,b = ln.split(r'\text{if }')
            if '=' not in a:
                ln = 'if %s: return %s' %(b,a)
            else:
                ln = 'if %s: %s' %(b,a)

        try: tree = ast.parse(ln)
        except SyntaxError as err:
            ## this breaks very easily - TODO a better way
            if err.msg == 'invalid decimal literal' and ln[ err.offset ] in args:
                ln = list(ln)
                ln.insert(err.offset, '*')
                ln = ''.join(ln)
                print('FIXED:', ln)
                assert ast.parse(ln)
            else:
                print(err)
                print('error msg', err.msg)
                print('error text', err.text)
                print('error offset', err.offset)
                raise err

        body.append('\t' + ln)
    if 'return ' not in body[-1] and body[-1].count('\t')==1:
        body[-1] = body[-1].replace('\t', '\treturn ')
    py = [head] + body
    #print(head)
    py = '\n'.join(py)
    print('Python:\n', py)
    if DEBUG:
        tmp = [LATEX_HEADER,full_latex, '\\begin{lstlisting}\n%s\n\\end{lstlisting}' %py ,LATEX_FOOTER]
        open('/tmp/test.tex','w').write('\n'.join(tmp))
        subprocess.check_call(['pdflatex', '/tmp/test.tex'], cwd='/tmp')
        if DEBUG >= 2: subprocess.check_call(['evince', '/tmp/test.pdf'])

    scope = {}
    exec(py, scope)
    return scope[func.name]

ALGOS = 0
def algo2py(tex):
    global ALGOS
    if DEBUG >=3:
        open('/tmp/test.tex','w').write(LATEX_HEADER+tex+LATEX_FOOTER)
        subprocess.check_call(['pdflatex', '/tmp/test.tex'], cwd='/tmp')
        subprocess.check_call(['evince', '/tmp/test.pdf'])

    py = ['"""%s"""' % tex]
    in_for = False
    for_end = None
    for ln in tex.splitlines():
        print(ln)
        ln = ln.strip().replace('$','')
        for key in LATEX2PYOPS:
            if key in ln: ln = ln.replace(key, LATEX2PYOPS[key])

        if ln.strip().startswith(r'\State '):
            ln = ln.replace(r'\State ', '')
            if ln.startswith(r'\Comment{'):
                a = ln.split('{')[-1].split('}')[0]
                ln = 'print("%s")' %(a)
            if in_for: ln = '\t' + ln
        elif ln.strip().startswith(r'\For{'):
            a = ln.split('{')[-1].split('}')[0]
            a,for_end = a.split(' to ')
            assert '=' in a
            for_var, for_start = a.split('=')
            ln = 'for %s in range(%s, %s):' %(for_var.strip(), for_start.strip(), for_end)
            in_for = True
        elif ln.strip().startswith(r'\EndFor'):
            in_for = False
        elif ln.strip().startswith(r'\Return'):
            ln = ln.replace(r'\Return', 'return')

        if ln and not ln.strip().startswith('\\'):
            py.append(ln)
    assert for_end
    algo = ['def algo%s(%s):' % (ALGOS, for_end) ]
    for ln in py: algo.append('\t'+ln)
    py = '\n'.join(algo)
    print(py)
    scope = {}
    exec(py, scope)
    if DEBUG >= 2:
        tmp = [LATEX_HEADER,tex, '\\begin{lstlisting}\n%s\n\\end{lstlisting}' %py ,LATEX_FOOTER]
        open('/tmp/test.tex','w').write('\n'.join(tmp))
        subprocess.check_call(['pdflatex', '/tmp/test.tex'], cwd='/tmp')
        subprocess.check_call(['evince', '/tmp/test.pdf'])

    fn = scope['algo%s' % ALGOS]
    ALGOS += 1
    return fn

def latex2py(tex):
    if DEBUG >= 3:
        open('/tmp/test.tex','w').write(LATEX_HEADER+tex+LATEX_FOOTER)
        subprocess.check_call(['pdflatex', '/tmp/test.tex'], cwd='/tmp')
        subprocess.check_call(['evince', '/tmp/test.pdf'])
        
    if tex.strip().startswith(r'\begin{algorithm}'):
        return algo2py(tex)
    
    orig_tex = tex
    tex = tex.strip().replace('$$', '$')
    #assert tex.count('$') >= 2
    parts = []; dollar = False; code = None; text=[]
    for c in tex:
        if c=='$':
            if not dollar:
                if text:
                    parts.append( ''.join(text) )
                    text = []
                code = []
                dollar = True
            else:
                assert code
                parts.append( ''.join(code).strip() )
                dollar = False
        elif dollar:
            code.append( c )
        else:
            text.append( c )
    if not parts and text: parts.append(''.join(text))
    return latex2def( parts[-1], orig_tex )

f = latex2py(r'''
\begin{algorithm}
\caption{An Example For Loop}
\begin{algorithmic}[1] % [1] adds line numbers
    \State $sum \gets 0$
    \For{$i = 1$ to $n$}
        \State $sum \gets sum + i$
        \State \Comment{This happens inside the loop}
    \EndFor \\
    \Return $sum$
\end{algorithmic}
\end{algorithm}
''')

print(f)
print(f(5))
assert f(5)==10


f = latex2py( r'$f: \mathbb{R} \to \mathbb{R}$ defined by $f(x) = 2x + 1$' )
print( f( 32 ) )
assert f(32) == 65


f = latex2py( r'''
$$
f(x) = \begin{cases} 
    x^2 & \text{if } x < 0 \\
    x + 2 & \text{if } x \geq 0 
\end{cases}
$$
''')

print( f(2) )
assert f(2) == 4

f = latex2py(r'''
% 1. Simple range loop (1 to 5)
\foreach \i in {1,...,5} {
    This is iteration number \i. \\
}
''')

## TODO - bootstrap
latex2py = latex2py(r'''
% TODO the latex version of latex2py that can be transformed by Python version,
% back into a runnable Python, this probably means breaking things apart into many
% smaller functions, because our simple latex2py parser/transformer works best on small
% chunks of latex that define functions, we may want to start step by step,
% where latex2py is still a Python function, but it starts to call sub-functions that
% are defined in latex.
''')

## TODO - after bootstrap
## now we can use the new latex2py to start extending this script, without using so much Python anymore
## our future goals is to connect with scipy.constants, so that when variables like c are used it is
## mapped to scipy.constants.c, mapping all the constants from scipy to latex variables will make latex
## much more readable, and educational, our next goal is to make Physics equations easy to read, and
## self documenting.  There are so many conventions in math and physics, we need to help people understand
## these symbols better, like rho (ρ) often denotes density, when transforming into Python we can make
## this clear to the user by transforming it to ρ_density.

