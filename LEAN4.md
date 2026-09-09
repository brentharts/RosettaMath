# Proving Python correct

`lean4.py` is a Calculus of Constructions micro-kernel. `hoare.py` is an
imperative language built on it, used to model an seL4-style OS kernel.

```sh
python3 lean4.py --selftest    # 153 checks
python3 hoare.py               # 157 checks
python3 crustproof.py          #  21 checks, incl. the differential test
```

The environment `hoare.py` builds has 91 declarations: 7 inductive families,
10 constructors, 14 recursors, 59 definitions, and **no axioms**. Every lemma
below is a term the kernel checked.

---

## 1. The kernel

A term is `Universe`, `Var`, `Bound`, `App`, `Meta`, `Pi` or `Lambda`, over de
Bruijn indices. Equality is structural on the de Bruijn form, so it is
alpha-equivalence for free, and substitution cannot capture.

Reduction is beta, delta (unfolding a definition) and iota (a recursor meeting
a constructor). `type_check` is the whole trusted base. The `Elaborator` —
Miller pattern unification with postponed constraints — is explicitly
untrusted: it fills in implicit arguments, and the kernel then re-checks the
result from scratch.

`inductive()` generates two recursors per family, `T.rec` into `Type 0` for
defining functions and `T.ind` into `Prop` for proving theorems, because there
is no universe polymorphism. One restriction is stated rather than hidden: a
recursive argument is not allowed in a family with indices, since the
induction hypothesis would have to name that occurrence's indices.

### 1.1 Three performance fixes, all measured

The imperative fragment was blocked on `normalize` before anything else could
happen. `leb 20 30` did not terminate. The cause took three passes:

| symptom | cause | fix |
| :--- | :--- | :--- |
| cost `2ⁿ`, normal forms `14n+3` | pure recomputation | memoise `normalize` per environment generation |
| still exponential | substitution *shares* the inserted term, so a body using its argument three times builds a DAG with `3ⁿ` paths and `O(n)` nodes — but hashing a **nested tuple** walks paths, not nodes | structural keys became interned **integers** |
| 4.5M `shift` and 2.7M `instantiate` calls building 2.25M fresh nodes | the DAG re-expanded into a tree on every substitution | memoise the three de Bruijn rewrites, so a hit returns the *same object* |

`modb 12`: 134s → 0.003s. `modb 32`: never → 0.046s. The SIMD contract
`len(ptr) >= 64 and not len(ptr) % 4` now computes in milliseconds.

**One bug is worth recording**, because the technique invites it. Keying the
caches on `key()` silently reprinted `symm`'s type, turning `{a : A}` into
`a : A`. `key()` is deliberately blind to binder name hints and implicitness —
that is what makes it alpha-equivalence — but `rebuild` carries both through.
Identity keys were correct but too sharp: they lost the structurally identical
copies that were the whole point. So there is now a second key, `fullkey()`,
drawing the line exactly where the rewrites do.

Every kernel change was gated on **byte-identical selftest and demo output**.
The demo caught the bug the selftest did not.

---

## 2. What a contract is

The tempting encoding, `le` as an inductive family, is refused by
`inductive()`. Rather than route around a deliberate restriction:

```
Holds b  :=  Eq Bool b true
```

A contract is a `Bool`-valued expression, and the proposition is that it
computes to `true`. This costs nothing that matters and buys something real:
every bound `crust`'s `extensions.py` parses (`len>=`, `len<=`, `div-by`) is
already decidable, because a contract a compiler cannot *check* is no use to
it. So the proposition is about the same expression the runtime check would
evaluate, and **the proof is what licenses deleting the check**. Closed
instances need no proof at all: they compute, and `refl` is the proof.

---

## 3. The imperative fragment

`PythonToLean` accepts exactly one `return`. `ImpToLean` accepts a body.

It is **symbolic execution**, not a semantics: there is no state type, no
`Var` type, no big-step relation. The store is a Python dict from variable to
the term it currently holds, so an assignment is a substitution performed in
the compiler rather than a `let` the kernel would have to understand.

| Python | becomes |
| :--- | :--- |
| `v = e` | substitution into the store |
| `if c: … else: …` | `ite` per assigned variable |
| `for i in range(n)` | `Nat.rec` — the fold it always was |
| `while c` + variant | iterating a guarded step, `fuel` = the variant on entry |
| several loop-carried variables | packed into a right-nested `Prod` |
| `c.field = e` | `c = Record.with_field c e` |
| `out: 'Array' = []` | `nil` at the annotation's element type |

Nothing here is trusted. Whatever it produces is handed to `type_check`, which
knows nothing of Python.

### 3.1 The `while` rule

`while` was refused at first, and the refusal was right: a while loop
terminates for a reason the text does not state, so lowering one means
inventing a variant or a fuel bound — a guess in a place where a guess is an
unproved theorem. An explicit annotation supplies what was missing:

```python
while c.current < c.nthreads:
    assert invariant(c.current <= c.nthreads)
    assert variant(c.nthreads - c.current)
    ...
```

The condition, invariant, variant and one pass are each **named as functions
of the state** (`schedule.cond1`, `schedule.inv1`, `schedule.rank1`,
`schedule.pass1`), and the fold is built from those names. That is what lets a
general lemma about folds apply to a particular loop.

Four obligations are raised, and **the soundness of the lowering is one of
them**:

| obligation | says |
| :--- | :--- |
| `progress` | the condition really is false when the fold is done |
| `invariant holds on entry` | `Holds (inv init)` |
| `invariant is preserved` | `∀s, Holds (inv s) → Holds (cond s) → Holds (inv (pass s))` |
| `variant decreases` | `∀s, Holds (inv s) → Holds (cond s) → Holds (ltb (rank (pass s)) (rank s))` |

There is no metatheorem in a comment saying "the fold equals the loop"; the
claim is a proposition the kernel checks.

**Two hypotheses, not one `andb`.** They carry the same content, but a case
split on the condition has `Holds true` to hand in the branch where it holds,
and `refl` proves that. `Holds (andb I true)` with a symbolic `I` has nothing
to reduce, and the chain stops there. Only one of the two forms composes.

### 3.2 Still refused

Roughly a third of `hoare.py`'s checks are refusals, each pinned to its reason:
`while` without a variant, `return` inside a loop or a branch, an unbounded
iterable, an unannotated parameter, a variable assigned on only one branch, a
variable changing type, division, a non-decidable postcondition, an empty list
literal with no annotation, a field that does not exist, a syscall that can
break the state invariant, a suffix that breaks it, a variant that does not
come down, a field name that is not bound.

---

## 4. Loops, proved

### 4.1 The fold shape

`iter (n+1) s` is `iter n (step s)`, **not** `step (iter n s)`. Both compute
the same thing, but the variant comes down on the first pass, so that is where
an induction on termination has to be able to look.

`sub` recurses on its **first** argument, so `sub (m+1) (n+1)` is `sub m n` by
definition. Iterating `pred` on the second argument computes the same numbers
and gives no such equation, which leaves any proof about an `n - i` variant
with nothing to induct on.

Both are cases of the same lesson: a definition that computes the right answer
can still be the wrong definition to reason about.

### 4.2 The lemmas

All proved, none assumed:

| lemma | by |
| :--- | :--- |
| `absurd : ∀ C:Prop, Holds false → C` | `Eq.ind` into a motive reading `true` as the goal, `false` as `TrueP` |
| `leb_refl`, `leb_succ` | induction |
| `leb_trans` | induction on the first argument, case split on the other two |
| `sub_le`, `sub_lt` | induction |
| `snoc_le` | induction on the list, case split on the bound |
| `andb_both`, `andb_left`, `andb_right` | `Bool.ind` |
| `guarded` | a case split turning the two-hypothesis form into one step |
| `fold_preserves` | induction on the number of passes |
| `loop_preserves` | the two composed |
| `stuck` | once the condition is false, iterating changes nothing |
| `fold_terminates` | the variant bounds the number of passes |

`fold_terminates` is the one that matters most: `progress` used to be checked
only at concrete values, which checks the examples and says nothing about the
rest. It is now proved for every starting state.

---

## 5. State: records, invariants, composition

A single-constructor inductive is a record; what `inductive()` does not give is
names. `record(env, name, fields)` generates, per field,
`Name.field : Name → T` and `Name.with_field : Name → T → Name`, both by iota
on the one constructor, so both compute. A functional update is what makes
state threadable: a syscall takes a context and returns one, and nothing is
mutated anywhere.

`state_invariant(env, 'Context', 'c.current <= c.nthreads')` defines
`Context.invariant : Context → Bool` — a property of the *state*, not of an
operation, which is the seL4 shape. `@procedure(preserves='Context')` then
lets the body assume it and obliges the syscall to hand it on.

**Composition chains proofs rather than re-proving.** If `f` hands the
invariant on and `g` hands it on, then `g ∘ f` does, and the term saying so is
just the two proofs applied in turn:

```
λ c h. tick_pf (enqueue (tick c)) (enqueue_pf (tick c) (tick_pf c h))
```

**The sequence rule.** A procedure with a loop is three steps — what runs
before, the loop, what runs after — and each has to hand the invariant on.
`replace_subterm` recovers the suffix as a function of the loop's result. Each
segment is named (`boot.before1`, `boot.after1`) and skipped when it is
definitionally the identity. `bad_suffix` — a correct loop followed by one
increment too many — is caught at exactly the right place:

> *what runs after the loop in bad_suffix changes what the Context invariant
> reads…*

### 5.1 Why a case split is needed at all

`Context.current (Context.with_ticks c v)` **does not reduce** on a symbolic
`c`: until the record is known to be built by its constructor, iota has nothing
to fire on. So even an operation that plainly leaves a field alone has nothing
to compute with. One split on the one constructor unsticks every projection at
once.

The subject need not be a record. A loop carrying two variables carries a
`Prod`, which is a one-constructor type too — the split that unsticks a
record's projections unsticks `fst` and `snd` for the same reason.

---

## 6. The proof toolkit

| tool | what it does |
| :--- | :--- |
| `discharge` | `refl`, for goals that compute. Introduces binders rather than refusing them: `Holds (leb 0 n)` is true whatever `n` is |
| `at` | instantiate an obligation at a call site, as `simd_contracts.py` does |
| `by_cases` | split on the one constructor of the subject; try `using`, then each hypothesis |
| `by_bool` | split on a `Bool` subterm that is not a variable — the `ite` an `if` left in the state |
| `unfold` | expand *named* definitions only. `normalize` is all or nothing: ask it to look inside `accepted.inv1` and it also unfolds `andb` and `ite`, and then there is no conjunction to take apart and no `ite` to split on |
| `invariant_at_exit` | the invariant, still holding, at the value the loop produced |
| `progress_by_loop` | `fold_terminates` applied to this loop |
| `preserves_by_loop` | prefix, loop and suffix chained into the syscall's obligation |
| `compose` | syscalls and their proofs, in sequence |
| `prove` | a hand-written term, checked by the kernel |

`by_cases` binds fields **by name**: `f['current']`, not `f[3]`. With a state
nested as `Prod A (Prod B C)` the index that happens to be right is an accident
of how the pack nests. A name that was not bound raises immediately rather than
falling through to the next attempt — a mistake in the caller's own lemma is
theirs to see.

### 6.1 Readability is a correctness concern

`schedule`'s postcondition once printed as ~600 characters with the same
`Nat.rec` inlined twice. A goal nobody can read is a goal nobody can tell is
the wrong one. Loops, passes, conditions, invariants, variants and segments
all get names, and procedures are declared before their contracts are stated,
so a postcondition says `schedule(c)`:

```
∀ c : Context, Holds(eqb(Context.current(schedule(c)))(Context.nthreads(schedule(c))))
```

These are definitions, so they unfold by delta whenever anything needs to
compute. The cost is zero.

---

## 7. The OS model

`Context` has six fields: `frames`, `queue`, `schemes`, `current`, `nthreads`,
`ticks`. Syscalls are `Context → Context`.

`List` is polymorphic, so a byte string is `List Nat` and a list of them is
`List (List Nat)`. On that: `find`, `take`, `drop`, `eqs`, `split`, `append`,
`snoc`, `rev`. `find` returning the length when the separator is absent is how
`str.find`'s `-1` is expressed without a negative number `Nat` does not have.

All four public functions of `crustos/schemes.py` are modelled, prefix routing
included:

| URL | scheme | path |
| :--- | :--- | :--- |
| `sys:boot` | 0 | `boot` |
| `file:/etc/passwd` | 2 | `/etc/passwd` |
| `gpu:0` | 6 | `0` |
| `nope:/x` | 7 (sentinel) | `/x` |
| `/etc/passwd` | 7 | `/etc/passwd` |

`fil:` does not route to `file` — `eqs` is equality, not prefix matching, and
that distinction is the whole of the routing bug you would want caught.

Contracts, all proved:

*   `scheme_of` — **the returned index never leaves the scheme table.**
*   `path_of` — **the path never grows.**
*   `route_all` — one scheme id per URL, in order.
*   `accepted` — **the result is never longer than the batch, for every
    input.**

### 7.1 `accepted`, end to end

```python
@procedure(ensures=['len(result) <= len(split(urls, 44))'])
def accepted(names: 'Strs', urls: 'Bytes') -> 'Array':
    parts = split(urls, 44)
    out: 'Array' = []
    i = 0
    while i < len(parts):
        assert invariant(len(out) <= i and i <= len(parts))
        assert variant(len(parts) - i)
        if scheme_of(names, parts[i]) < len(names):
            out = snoc(out, i)
        i = i + 1
    return out
```

The invariant is a conjunction because `i <= len(parts)` alone is enough for
termination and not for the result. The proof:

1.  **entry** — computes, whatever the input.
2.  **preservation** — split on the `Prod`, then `by_bool` on the `ite` the
    `if` left behind. If the URL is accepted the list grows by one and so does
    `i` (`snoc_le`); if not, only `i` moves, which only makes room
    (`leb_trans`, `leb_succ`). The two halves are rejoined with `andb_both`.
3.  **variant** — `sub_lt`, applied at the named field `f['i']`.
4.  **termination** — `progress_by_loop`, so the loop finishes for every input.
5.  **the postcondition** — `invariant_at_exit` gives the invariant at the
    value the loop produced; `andb_left` and `andb_right` take it apart and
    `leb_trans` joins the halves.

```
∀ names, ∀ urls, Holds(leb(len(accepted(names)(urls)))(len(split(urls)(44))))
```

---

## 8. Integration with Crust

`crustproof.py` turns a Crust contract into a term of the calculus of
constructions. `{'len>=': 64, 'div-by': 4}` becomes `andb (dvdb 4 n)
(leb 64 n)` of type `Nat -> Bool`; at a known length it reduces, and when it
reduces to `true` a proof term is built and type-checked.

```python
>>> check(70, {'len>=': 64, 'div-by': 4})
not proved: andb(dvdb(4)(70))(leb(64)(70)) at length 70 computes to false
```

**What the differential test found.** Crust's two consumers read one contract
two ways. `simd_contracts._satisfies` conjoins every clause;
`contracts._violates` returned on the first clause present. For
`{'len>=': 64, 'div-by': 4}` -- the contract in `SIMD_CONTRACTS.md` -- a length
of 70 clears `len>=`, so the `div-by` was never looked at: the call compiled,
while `simd_contracts` correctly refused to prove it and kept the scalar tail.
The pass that reports errors was the lenient one. Across a grid of six contracts
and 130 lengths, 110 of 780 cases differed, all of them multi-clause.

The fix is one reading, in `shivyc/proofs.py`, which both passes now call, and
which raises on a clause it cannot read rather than skipping it. The diagnostic
also names the clause the length *actually* breaks, which the first-clause
reading could not do. Crust's own suite gained four tests, and `crustproof.py`
keeps the two in step: it asserts the kernel agrees with both passes on every
case, and pins the old reading as a regression.

**Certification is on by default**, and `shivyc/proofs.py` raises if the kernel
and the reading disagree rather than picking a winner. `CRUST_PROOFS=0` turns
it off; nothing is imported until a contract actually needs certifying, so a
program without contracts pays nothing.

It used to be off, because settling a contract at length 64 took about a second
and at 1024 half a minute. Two things fixed that.

**Literals compute.** `Nat` is unary, so `leb 64 n` unfolded n times and
rebuilt a term at each step. `accelerate()` attaches a computation rule to a
definition that fires only when the arguments have already reduced to numerals,
answering by Python arithmetic; anything else falls through to ordinary delta,
so a symbolic argument behaves exactly as before and every proof by induction
is untouched. This is a real extension of the trusted base -- Lean does the
same for `Nat`, for the same reason -- and what keeps it honest is that each
accelerator is run against the definition it stands in for over a grid, in
`hoare.py`'s selftest. That test earned its place immediately: `modb n 0` is
`n`, because the definition counts up and never meets a zero divisor to reset
at, and the first accelerator said `0`.

Making the rule fire took two attempts, both instructive. `normalize` unfolds a
definition's `value` the moment it meets the bare name, so a rule on a
definition never sees its arguments; the declaration has to stop offering a
`value` and drive delta from the rule instead. Then a *partial* application
still unfolded to a lambda, which the caller beta-reduced, so the full
application -- the only place the arguments are all visible -- was never
reached. Under-application now returns `None` and stays stuck on purpose.

**And the literal is substituted before reducing.** `crustproof` built
`(lam n. contract) 64` and normalised it; normalising an application normalises
the function first, which walks into the contract with `n` still a variable and
unfolds everything it mentions -- precisely the work the literal was supplied to
avoid.

| length | before | after |
| ---: | ---: | ---: |
| 64 | 1.35 s | 0.001 s |
| 1024 | 43 s | 0.005 s |
| 65536 | (never) | 0.38 s |

What is left is the representation: building a numeral for length `n` is still
`n` nodes, so `NUMERAL_LIMIT` refuses past 200,000 rather than overflowing the
stack in a traceback. `CRUST_PROOF_MAX` (65536) is the compiler's budget within
that.

**A proof removes a runtime check.** `memsafe_elide` has a new rule.

> **Rule 4 -- a parameter with a proven contract.** `assert len(p) >= 64` on a
> parameter is a statement about every caller, and Crust can check it against
> every caller. Where it holds at all of them, the callee may treat `p` as an
> allocation of at least that size, and a constant offset into it is in bounds
> by the same arithmetic rule 2 uses.

`len` counts **elements**, so the byte extent is `len * sizeof(*p)` -- getting
that backwards would hand the pass a bound four times too large on an `int *`,
so the conversion is done once, in `simd_contracts.parameter_extents`, next to
the element size it needs.

Two conditions, both about not being wrong. The contract must have been
*established*: every visible call site traced to an allocation large enough,
and a certificate for it. An unchecked promise tells the callee nothing. And
the callee must make no calls at all -- rule 2 gets liveness from the static
pass and there is no such fact about a parameter, so the only safe substitute
is a body in which nothing could have freed the buffer.

```
void fill(int *p) assert len(p) >= 4 { p[0]=1; p[1]=2; p[2]=3; p[3]=4; }
```

goes from **5 checks emitted, 0 avoided** to **1 emitted, 4 downgraded to a
shadow update, 80% avoided**. A proved write becomes a bare shadow update
rather than nothing, for the reason rule 2 already gives: the check is also
what records which bytes are now defined.

Everything that should refuse, refuses -- no contract, a caller that allocates
less, a callee that calls anything, a withdrawn certificate. And the checks
left behind still work: add `p[4] = 5` and the fifth check stays and catches
the overflow at run time; let the caller pass two elements and the contract is
not established, all five checks stay, and the runtime reports it. Eight tests
in `tests/test_mem_safe_elide.py`.

**One thing this needed was not about proofs at all.** `p[2]` is emitted as
`Add(p, Mult(2, 4))`, so the offset is constant but is not a *literal*, and the
origin tracker walked straight past it. `_constants()` folds through `*`, `+`
and copies -- for values assigned once in the whole function, since IL values
are not SSA and a stale constant would be a wrong offset. Rule 2 wanted that
too, for every `a[3]` into a malloc'd array.

**A proof also changes instruction selection.** `simd_contracts` drops the scalar
remainder loop when a contract holds at every call site. Satisfying the
contract is no longer on its own the licence: `proofs.licenses()` also wants
the certificate, and a length past the budget or a bridge that will not load
means there is none, so the tail stays. Same rule as the rest of Crust -- a
proof that does not arrive degrades to the conservative path, never to a wrong
answer.

```
default                  proven at all 1 call site(s) (kernel-checked); scalar fallback omitted
CRUST_PROOF_MAX=8        not proven (aligned but unproved (no certificate)); keeping scalar code
```

and `calc_sum` comes out as **22 instructions using `paddd`/`movdqu`** in the
first case and **40 scalar instructions** in the second. Three tests in
`tests/test_metamorphic_simd.py` pin it, including that withdrawing the
certificate withdraws the SSE2 -- otherwise the certificate would be
decoration.

---

## 9. What is not done

*   **Rule 4 only fires in a leaf.** A function that calls anything gets no
    parameter bound, because nothing supplies liveness for a parameter and a
    call may have freed it. Crust sees the whole call graph, so "no callee
    transitively frees this" is knowable and would widen the rule a great
    deal; "no calls at all" is what is implemented.
*   **Rule 4 is for constant offsets.** `p[i]` in a loop is rule 3's problem,
    and a contract bound is not yet joined up with the loop-carried ranges
    that rule already computes.
*   **The accelerators are trusted Python.** Nine of them, each checked
    against its definition over a grid, but checked is not proved.
*   **`preserves_by_loop` handles one loop per procedure.** Two loops in
    sequence need the sequence rule applied twice.
*   **No heap.** Only a plain variable or a record field may be assigned. A
    real kernel has aliasing, and nothing here models it.
*   **`scheme_of`'s postcondition is proved; `route_all`'s is checked at a
    batch.** Its `for` loop has no invariant annotation, so there is nothing
    to carry.
*   **The `crustos` model is a model.** `kernel.c` does not boot, has no MMU
    and no interrupts; what is modelled is the scheme layer and a
    round-robin scheduler's shape, not a system.
