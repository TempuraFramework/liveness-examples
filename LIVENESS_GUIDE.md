# A Complete, Exhaustive Guide to Liveness Proofs in Ivy

*Based on Kenneth L. McMillan, "Toward Liveness Proofs at Scale" (CAV 2024), the
Ivy source code (`ivy/ivy_l2s.py`, `ivy/ivy_ranking.py`), the shipped liveness
benchmarks, and hands-on debugging with `ivy_check`.*

---

## Table of Contents

1. [What "liveness" means and why it is hard](#1)
2. [The central idea: relational rankings](#2)
3. [The proof rules of the paper, in full detail](#3)
   - 3.1 [Finiteness (Rule 5)](#3.1)
   - 3.2 [Simple relational reactivity (Rule 6)](#3.2)
   - 3.3 [Chaining lemmas (Rule 7)](#3.3)
   - 3.4 [Stable schedulers (Rule 8)](#3.4)
   - 3.5 [Lexicographic rankings (Rule 10) and parameterized justice (Rule 11)](#3.5)
   - 3.6 [Soundness](#3.6)
4. [How the rules map onto Ivy constructs](#4)
   - 4.1 [The temporal surface syntax](#4.1)
   - 4.2 [The shared liveness-to-safety monitor](#4.2)
   - 4.3 [The `work_*` parameter dictionary](#4.3)
   - 4.4 [The tactic family: `l2s`, `l2s_auto`, `l2s_auto5`, `ranking`](#4.4)
   - 4.5 [Skolemization, `_X`, and staying in EPR](#4.5)
5. [A practical methodology (recipe) for constructing a proof](#5)
6. [A debugging playbook, keyed to the failing VC names](#6)
7. [Worked Example 1 — simple ranking: a distributed barrier](#7)
8. [Worked Example 2 — stable schedulers: a two-stage approval pipeline](#8)
9. [Synthesis heuristics: how to *invent* the predicates](#9)
10. [Reference tables and gotchas](#10)

Everything in Sections 7 and 8 is backed by two Ivy files in this directory that
verify `OK` under `ivy_check`:

- `example1_barrier_liveness.ivy`
- `example2_pipeline_liveness.ivy`

The verifier used throughout is `~/workplace/ivy-tools/ivy-venv/bin/ivy_check`.

---

<a name="1"></a>
## 1. What "liveness" means and why it is hard

A **safety** property says "nothing bad ever happens" (an invariant of the
reachable states). A **liveness** property says "something good eventually
happens." Typical liveness properties:

- *Termination*: the system reaches a final state.
- *Response*: every request is eventually answered.
- *Non-starvation*: every waiting process is eventually served.

Liveness is only meaningful under **fairness**: without the assumption that
enabled actions eventually run, any system can "starve" a request simply by
never scheduling the action that would serve it. So a liveness property in Ivy
almost always has the shape

```
(fairness assumptions)  ->  (something good eventually happens)
```

### Why liveness is hard to mechanize

The classical way to prove liveness deductively (Manna–Pnueli) is a
**well-founded ranking**: a function from states into a well-founded order (e.g.
the naturals) that strictly decreases every time the "helpful" fair action runs.
Because the order is well-founded, it cannot decrease forever, so the good thing
must eventually happen.

The problem, spelled out in Section 2.1 of the paper: **reasoning about
well-foundedness requires an induction axiom**, and induction throws the SMT
verification conditions out of the decidable fragment (EPR / FAU). In practice
Z3 then *diverges* — it returns neither a proof nor a counterexample, just a
timeout. The paper's opening example (a timestamped queue) shows Z3, CVC4, and
CVC5 all failing on the trivial "removing a minimal timestamp decreases the
count of pending timestamps ≤ t" obligation, because it needs induction over t.

This is fatal at industrial scale: you cannot iteratively develop a large proof
if the prover fails opaquely and gives you no counterexample to guide you.

The paper's whole contribution is a way to get ranking-style proofs whose
verification conditions stay in **EPR**, so the prover is a genuine decision
procedure that always answers and always gives counterexamples.

---

<a name="2"></a>
## 2. The central idea: relational rankings

The key observation (Section 3): the liveness of these systems does **not**
actually depend on the well-foundedness of the ranking order. In the queue
example the timestamps could be real numbers and the queue would still be live.
The well-foundedness was an artifact of the *proof rule*, not the system.

So instead of a ranking that is an **ordinal-valued function** of the state,
use a **relation** (a set of tuples), ordered by set inclusion (⊆). This order
is *not* well-founded in general — but if we can show the relation is always
**finite**, then a finite set cannot be strictly shrunk (⊂) infinitely often.

Crucially, finiteness is established **outside the logic** (as a meta-level side
condition), not as a first-order formula (which would need induction). The
mechanism (Rule 5 below) is: the relation starts empty, and each transition adds
only the finitely many values that were *computed during that step*. Since a
finite computation produces finitely many values, the relation is finite at
every finite time.

Two shorthands used everywhere:

```
conserves δ   ≜   ∀x. δ'(x) → δ(x)          # the transition adds no tuple to δ
reduces δ     ≜   ∃x. δ(x) ∧ ¬δ'(x)          # the transition removes at least one tuple
```

(primes denote the next-state value.)

This gives "the best of both worlds": the conceptual simplicity of a ranking
proof, but verification conditions in pure first-order logic that stay in EPR.

---

<a name="3"></a>
## 3. The proof rules of the paper, in full detail

Notation: `□` = always, `♦` = eventually, `→` = ordinary implication,
`⇒` = temporal entailment (`p ⇒ q` means `□(p → q)`). Free variables in
`p, q, r` are non-temporal state predicates unless noted.

<a name="3.1"></a>
### 3.1 Finiteness (Rule 5)

To prove that a relation `R` (a function of the state) is always finite:

```
F1.  ∀x. ¬R(x)                                                  (R is initially empty)
F2.  □ ∀x. R'(x) → (R(x) ∨ x = e₁ ∨ ⋯ ∨ x = eₙ)                (each step adds ≤ n elements)
─────────────────────────────────────────────
     □ R is finite
```

Here `e₁…eₙ` are expressions depending on the current state — in practice, the
ground terms occurring in the transition, i.e. the values the step actually
manipulates. Since each step adds finitely many elements to `R`, `R` is finite
at every finite time. **Note that "R is finite" is not itself a first-order
formula** — it is a meta-level conclusion. This is what lets us avoid induction.

In Ivy this rule is realized by the monitor's *abstraction domain* relation
`l2s_d` (see §4.2): the tactic automatically maintains "every element ever
produced is in `l2s_d`," and the user's `work_created` predicate must be shown
`⊆ l2s_d`. Because `l2s_d` only ever accretes the finitely many values computed
so far, it is finite by construction.

<a name="3.2"></a>
### 3.2 Simple relational reactivity (Rule 6)

Proves properties of the form `(□♦r) → (p ⇒ ♦q)`: *if the justice condition `r`
holds infinitely often, then whenever `p` holds, `q` eventually follows.*

```
C0.  □ R is finite
C1.  p ⇒ (q ∨ φ ∧ (∀x. δ(x) → R(x)))
C2.  φ ⇒ (q′ ∨ (φ′ ∧ conserves δ))
C3.  φ ∧ r ⇒ (q′ ∨ reduces δ)
─────────────────────────────────────────────
     (□♦r) → (p ⇒ ♦q)
```

- **C1**: when `p` becomes true, either `q` is already true, or the *liveness
  invariant* `φ` holds **and the ranking `δ` is bounded by the finite `R`**
  (this is where finiteness is pinned to `δ`).
- **C2**: while we wait (φ holds and q hasn't happened), φ persists and δ never
  grows.
- **C3**: whenever the fair condition `r` fires, δ strictly shrinks (or q
  happens).

Since δ is finite, monotonically non-increasing, and strictly decreases each
time `r` fires (assumed infinitely often), δ must reach ∅, forcing `q`. This is
the relational analogue of Manna–Pnueli's classic B1–B3 rule, with the
well-founded ranking replaced by a finite relation.

<a name="3.3"></a>
### 3.3 Chaining lemmas (Rule 7)

To compose liveness lemmas (e.g. prove end-to-end response from per-stage
response lemmas), Rule 6 is relaxed in two ways: (1) `r` need not hold
infinitely, only until `q`; so `r` moves *into* the premises as a parameter;
(2) `q`/`q′` are weakened to `♦q`.

```
C0.  □ R is finite
D1.  p ⇒ ((♦q) ∨ φ ∧ (∀x. δ(x) → R(x)))
D2.  φ ⇒ ((♦q) ∨ (φ′ ∧ conserves δ))
D3.  φ ∧ r ⇒ ((♦q) ∨ reduces δ)
D4.  φ ⇒ ((♦q) ∨ (♦r))            # the justice condition is itself eventually met
─────────────────────────────────────────────
     p ⇒ ♦q
```

Premises now contain temporal operators; they are discharged **propositionally**
using the symbolic-tableau axioms (`p ⇒ ♦p` and `♦p ⇒ (p ∨ (♦p)′)`) that Ivy
generates automatically. In Ivy this is the pattern "prove per-stage lemmas with
one tactic, then combine them with `instantiate lemma with X = _X;` followed by
`tactic l2s with { invariant false }`."

<a name="3.4"></a>
### 3.4 Stable schedulers (Rule 8)

To avoid a lemma explosion, combine multiple rankings δ₁…δₙ (with justice
conditions r₁…rₙ) into one proof. In a given state, only one ranking need
decrease; that ranking's justice condition is called **helpful**. Each δᵢ gets a
**scheduler predicate ψᵢ** marking when rᵢ is helpful. Schedulers must be
**stable**: once ψᵢ is true, it stays true until rᵢ fires.

```
S1.  p ∧ ¬(♦q) ⇒ φ
S2.  ⋀ᵢ  φ ∧ ¬(♦q) ⇒  φ′ ∧
                        (conserves δᵢ) ∧
                        (ψᵢ ∧ rᵢ  → reduces δᵢ) ∧
                        (ψᵢ ∧ ¬rᵢ → ψᵢ′)             # stability
S3.  ⋀ᵢ  φ ∧ ¬(♦q) ∧ ψᵢ ⇒ ♦rᵢ                        # a scheduled condition eventually occurs
S4.  φ ∧ ¬(♦q) ⇒ ⋁ᵢ ψᵢ                               # something is always scheduled
S5.  ⋀ᵢ  φ ⇒ (∀x. δᵢ(x) → R(x))
S6.  □ R is finite
─────────────────────────────────────────────
     p ⇒ ♦q
```

This is the rule realized by Ivy's **`l2s_auto5`** tactic (the `5` variant is
precisely the one that reads a `work_helpful` predicate). The classic use: two
queues polled infinitely often; whichever queue currently has work ≤ t is the
helpful one.

<a name="3.5"></a>
### 3.5 Lexicographic rankings (Rule 10) and parameterized justice (Rule 11)

When messages can be **reordered** (a message can be bypassed an unbounded
number of times), no single finite ranking exists. The fix is a
**lexicographic** ranking δ₁ (high order) … δₙ (low order). Two notions:

```
preᵢ(ψ) = ⋁_{j<i} ψⱼ           # some higher-order ranking is scheduled  (preempted)
reqᵢ(ψ) = ψᵢ ∧ ¬preᵢ(ψ)         # scheduled and not preempted             (required)
```

A **preempted** ranking may *increase* (as long as it stays finite ⊆ R); only a
**required** ranking must be conserved/reduced, and only required schedulers
must be stable. Rule 10 replaces S2 with:

```
L2.  ⋀ᵢ  φ ∧ ¬(♦q) ⇒  φ′ ∧
                        (¬preᵢ(ψ) → conserves δᵢ) ∧
                        (reqᵢ(ψ) ∧ rᵢ  → reduces δᵢ) ∧
                        (reqᵢ(ψ) ∧ ¬rᵢ → ψᵢ′)
```

(S1, S3–S6 unchanged.) **Rule 11** generalizes to an unbounded/infinite number
of justice conditions (e.g. one per process) by replacing the finite ⋀/⋁ over
conditions with ∀/∃ over a parameter — note `n` is the number of *rankings*, not
of processes.

This is the rule realized by Ivy's **`ranking`** tactic, where the bracketed
suffixes `[0], [1], …` denote the lexicographic hierarchy (`[0]` = highest
order).

<a name="3.6"></a>
### 3.6 Soundness (Appendix A of the paper)

- **Theorem 1**: over *finite* relational rankings, the lexicographic pre-order
  `<δ` is well-founded (induction on n: the finite high-order component cannot
  decrease forever; the tail is a shorter well-founded chain).
- **Theorem 2/3**: Rules 8 and 10 are sound — a run with `p` but never `q`,
  satisfying all premises, would force `sⱼ >δ s_k` infinitely, contradicting
  Theorem 1.

**Incompleteness (acknowledged, rarely a problem in practice):** Rule 5 can't
prove finiteness when a step nondeterministically chooses an unbounded number in
one transition; and lexicographic rankings cap ordinal height at ωⁿ.

---

<a name="4"></a>
## 4. How the rules map onto Ivy constructs

<a name="4.1"></a>
### 4.1 The temporal surface syntax

Ivy 1.8 temporal logic tokens:

- `globally p` = `□p`, `eventually p` = `♦p`.
- A liveness obligation is stated as a `temporal property`, and the fairness
  assumptions are usually stated inside it (as `globally eventually …` in the
  antecedent) or as separate `explicit temporal axiom`s that are then
  `instantiate`-d in the proof.
- The **signal idiom** is the standard way to mark an "event" occurring in a
  single atomic step:

```ivy
module signal(data) = {
    action raise(val:data)
    specification {
        relation now
        var value : data
        after init { now := false; }
        before raise { value := val; now := true; now := false; }
        invariant ~now              # 'now' is only ever momentarily true
    }
}
```

`raise` sets `now := true; now := false;` in the same atomic step, so `now` is
true *exactly at the transition* where the event happens. This lets you write
"the receive event for X happens" as `receiving.now & receiving.value = X`.

- **Fairness flags**: an alternative to signals for actions. A boolean
  `f_fair` set `true; false;` at the top of the action marks "this action ran."
  Then `globally eventually f_fair` is the fairness assumption. (Used in
  `my_primary_backup.ivy` and in Example 1 here.) The invariant `~f_fair` must be
  stated so the flag reads false in every stable state.

<a name="4.2"></a>
### 4.2 The shared liveness-to-safety monitor

Both tactic families compile the temporal goal into **one ordinary
safety-checked model** by attaching a Padon-style *liveness-to-safety monitor*
(built in `ivy_l2s.py` lines 783–928). Its pieces:

- **Three phase bits** `l2s_waiting`, `l2s_frozen`, `l2s_saved`, with a
  nondeterministic edge `waiting → frozen → saved`.
- **Two abstraction-domain relations** `l2s_d` and `l2s_a`:
  - `l2s_d(x)` = "x has been *produced* in the finite computation so far" — this
    is exactly the finite reached set `R` of Rule 5. Constants are forced into
    `l2s_d`.
  - `l2s_a` = the frozen snapshot of `l2s_d` (set `l2s_a := l2s_d` at the freeze
    edge).
- **Saved-state binders** `l2s_s` (value of a term at the freeze point) and
  **wait bits** `l2s_w` (whether an eventuality is still outstanding).
- **The fair-cycle assertion** (`assert_no_fair_cycle`): `assert ¬(l2s_saved ∧
  done_waiting ∧ projection-agrees)`. In words: *you cannot return to the frozen
  snapshot state (on the finite abstraction domain) with all fairness
  eventualities satisfied.* Such a return would be a fair cycle ⇒ the liveness
  property fails.

**This single assertion is the entire liveness obligation.** Everything the
tactics generate (the `l2s_*` invariants from your `work_*` definitions) exists
to make that one safety assertion provable by the ordinary inductive-invariant
engine. That is why all VCs stay in EPR: the monitor never reasons about a
well-founded order, only about a finite reached-set relation.

You will see the desugaring `$was φ ≜ l2s_saved ∧ l2s_s[φ]` and `$happened φ ≜
l2s_saved ∧ ¬l2s_w[φ]` in traces.

<a name="4.3"></a>
### 4.3 The `work_*` parameter dictionary

Both `l2s_auto5` and `ranking` read the same vocabulary of user `definition`s.
This mapping is confirmed verbatim by comments in the shipped
`ticket_l2s_auto.ivy` / `ticket_ranking.ivy` and by the source:

| Ivy parameter        | Paper symbol | Meaning |
|----------------------|--------------|---------|
| `work_created(x)`    | **R**        | the finite reached set that bounds the ranking (forced ⊆ `l2s_d`). Usually just `true`, or `x ≤ clock`. |
| `work_needed(x)`     | **δ**        | the ranking relation — the set of "outstanding work" whose ⊂-shrinking drives progress. |
| `work_invar`         | **φ**        | the liveness invariant that holds from the trigger until the goal. |
| `work_progress(...)` | **r**        | the justice/fairness condition (a signal `.now` or a fair flag). |
| `work_helpful(...)`  | **ψ**        | the *stable scheduler* — the state predicate saying "this justice condition is currently helpful (will reduce δ when it fires)." **Only read by `l2s_auto5` and `ranking`.** |
| `work_start`         | **p**        | the trigger (antecedent of `p ⇒ ♦q`). Auto-inferred if the property ends in a bare `globally`. |
| `work_done(x)`       | —            | the "completed" set; auto-synthesized as `false` in `l2s_auto5` when omitted. |
| `work_witness(...)`  | —            | (ranking only) an explicit witness element for `∃x. δ(x)∧¬δ′(x)` when Z3 needs help. |

**Bracketed suffixes** `[0], [1], …` create multiple components. Under
`l2s_auto5` they are the multiple justice conditions of Rule 8; under `ranking`
they are the lexicographic hierarchy of Rule 10 (`[0]` highest order).

The generated invariants (names you'll see in `ivy_check` output) map to rule
premises like this:

| Generated invariant / postcond | Rule premise |
|--------------------------------|--------------|
| `l2s_created`, `l2s_needed_when_start`, `l2s_needed_implies_created` | C0/C1/S5/S6: δ ⊆ R ⊆ l2s_d (finiteness) |
| `l2s_work_preserved`, `l2s_needed_preserved`, `l2s_needed_are_frozen` | C2/S2: conserves δ |
| `l2s_progress_made` / `l2s_progress` | C3/S2: reduces δ when helpful & fair |
| `l2s_sched_stable` | S2: ψ ∧ ¬r → ψ′ (scheduler stability) |
| `l2s_sched_exists` | S4: something is always scheduled |
| `l2s_not_all_done` | while φ holds, work remains |
| `l2s_progress_invar` / `l2s_progress_eventually` | S3: ψ ⇒ ♦r |
| `l2s_globally_*` | tableau axioms for the □/♦ in the property |

The `ranking` tactic additionally accumulates a `helps` list and computes
`no_help = ¬(⋁ earlier helps)` = the preemption predicate `preᵢ(ψ)`, and guards
`l2s_needed_preserved`, `l2s_progress`, `l2s_sched_stable` by it — that is
exactly Rule 10's L2.

<a name="4.4"></a>
### 4.4 The tactic family

| Tactic       | Realizes | Notes |
|--------------|----------|-------|
| `l2s`        | raw monitor | you supply the L2S invariant by hand (`invariant …`). The escape hatch; used with `invariant false` for purely propositional lemma-chaining (Rule 7). |
| `l2s_auto`   | Rule 6 (single ranking) | reads `work_created/needed/done/progress`. **On the build in this repo it frequently reports "not in the fragment FAU"** — see the note below. |
| `l2s_auto2/3/4` | intermediate variants | successively guard more invariants with the start condition. |
| `l2s_auto5`  | **Rule 8 (stable schedulers)** | reads `work_helpful` in addition. This is the recommended multi-justice tactic. |
| `ranking`    | **Rule 10/11 (lexicographic, parameterized)** | reads `work_helpful` and treats suffixes as a lexicographic hierarchy; also the most robust single-ranking tactic on this build. |

> **Build-specific note (important, discovered empirically):** on the Ivy
> install in `~/workplace/ivy-tools/ivy-venv`, the plain `l2s_auto` tactic fails
> the shipped `1queuelive.ivy`/`2queuelive*.ivy` with *"The verification
> condition is not in the fragment FAU."* The `l2s_auto5` and `ranking` tactics
> work (`ticket_l2s_auto.ivy` and `ticket_ranking.ivy` both verify `OK`).
> **Therefore this guide realizes the "simple ranking rule" using the `ranking`
> tactic with a *single* component** (which is exactly Rule 6 — one δ, one r),
> and the "stable scheduler rule" using `l2s_auto5` with *two* components. Both
> are faithful to the paper; the choice is dictated by what the local prover
> accepts.

<a name="4.5"></a>
### 4.5 Skolemization, `_X`, and staying in EPR

Liveness properties are almost always universally quantified over the object
whose progress you track (a message id, a node, a document). The proof begins
with `tactic skolemize;` (or `skolemizenp;`), which replaces that `∀X` with a
**fresh Skolem constant `_X`**. This is the single most important trick for
staying in EPR:

- It turns the ranking (which would otherwise mention a bound variable) into a
  ground-parameterized relation, avoiding a quantifier alternation.
- All your `work_*` definitions then refer to `_X` for the tracked object, and
  to a fresh bound variable (e.g. `M`) for the *elements of the ranking set*.

`skolemize` vs `skolemizenp`: use `skolemizenp` ("no prophecy") for the
`l2s_auto5`/`ranking` tactics as in the shipped examples; `skolemize` also works
for the single-component `ranking` proofs here. When in doubt, copy the
incantation from a shipped example with the same tactic.

**The stratification pitfall (paper §4.2):** the deep reason liveness proofs
leave EPR is quantifier alternation in *invariants*, not the ranking itself.
The paper's ticket example needs "for every unserved ticket t, some process
holds t" — a `∀t ∃p` that forms a function cycle with the state's `p → ticket`
map, breaking stratification. Two remedies: (1) Herbrandize (skolemize) the
outer quantifier into a constant; (2) add an **auxiliary state variable** that
provides the existential witness explicitly, with a defining invariant. Keep
this in mind: if Z3 starts timing out unpredictably, look for a `∀∃` in your
added invariants.

---

<a name="5"></a>
## 5. A practical methodology (recipe) for constructing a proof

This is the workflow distilled from building the German-protocol proofs, the
primary/backup proof, and the two examples below.

1. **State the property in `p ⇒ ♦q` shape.** Identify:
   - the tracked object `X` (universally quantified),
   - the trigger `p` (`work_start`) — when the obligation "arms,"
   - the goal `q` — the good event,
   - the fairness assumptions (justice conditions).

   Prefer the form `forall X. (GF fair… & <trigger>) -> eventually <goal>` when
   there is a discrete "start event," or `forall X. GF fair -> globally
   (<pred>(X) -> eventually <goal>(X))` when the obligation is "any time this
   holds." Structure it so `skolemize` can lift `X` to `_X` (keep the `forall X`
   at the very outside).

2. **Identify the pipeline of stages** each object passes through, and **which
   fair action advances each stage.** Draw it: `stage₀ --actionₐ--> stage₁
   --action_b--> … --> done`.

3. **Choose the ranking `work_needed` (δ) = the set of outstanding obligations.**
   The golden rule: **δ must be *conserved* (never grow) by every action except
   the one whose justice condition is supposed to reduce it.** This is the
   single most common source of failure. Consequences:
   - Rank over a set that only shrinks. If an action *grows* your candidate set,
     that set is not a valid ranking — either the system genuinely needs an
     order (→ use timestamps as in the queue example) or you must pick a
     *monotone* underlying set (e.g. `~done(X)` where `done` only grows).
   - For a multi-stage pipeline, a *lower-order* ranking should be the **union**
     of the remaining stages, so that an action moving an object from stage k to
     stage k+1 *conserves* it (the object is still in the union). See Example 2.

4. **Choose `work_progress` (r) = the fairness flag / signal of the action that
   reduces this δ.** It must be the action that actually removes an element from
   *this* δ — not a neighboring stage's action. (This is precisely the bug in
   the original `my_primary_backup.ivy`: the ranking's progress condition named
   the *send* action, but only the *ack* action reduced that set.)

5. **Choose `work_helpful` (ψ) = the state condition under which firing r will
   *definitely* reduce δ.** Typically "the enabling guard of the action, on the
   relevant element." E.g. for a drain action guarded by `some x. present(x)`,
   the scheduler is `exists M. present(M)`. For a pipeline, the low-order
   scheduler is "stage 2 is non-empty," so `signoff` can act. ψ must be *stable*:
   once true it stays true until r fires — the tactic checks this
   (`l2s_sched_stable`), and it fails loudly if you get it wrong.

6. **Choose `work_invar` (φ)** = the liveness invariant that persists from
   trigger to goal. Usually "the tracked object is still outstanding," e.g.
   `~notified(_X)` or `pending_review(_X) | pending_signoff(_X)`.

7. **Choose `work_created` (R).** Almost always `true` for a finite type (the
   whole finite universe is a fine finite bound). Use `X ≤ clock` for
   timestamp-typed rankings over an unbounded sequence.

8. **Add the safety invariants the ranking needs.** These are *ordinary*
   `invariant`s. Liveness proofs almost always reuse the safety invariants, plus
   a few extra "well-formedness" facts that exclude spurious states the ranking
   checker would otherwise explore (e.g. "a reply is never in flight to an
   already-served node"). You discover exactly which ones from the CTIs.

9. **Run `ivy_check`; if it fails, run `ivy_check debug=true trace=true` and read
   the counterexample.** Map the failing VC name (see §6) to the rule premise,
   look at the small model, and either strengthen δ/ψ or add a safety invariant.
   Iterate.

10. **Sanity-check non-vacuity.** After it passes, deliberately break a
    parameter (set `work_progress = false`, or `work_helpful = true`) and confirm
    it now *fails*. If it still passes, that parameter wasn't load-bearing and
    your property may be vacuously true or your ranking degenerate.

---

<a name="6"></a>
## 6. A debugging playbook, keyed to the failing VC names

When `ivy_check` prints `<name> ... FAIL`, the name tells you which rule premise
broke. Run `ivy_check debug=true trace=true <file>` to get the pre-state and the
offending action; the trace stops at the *first* failing check.

| Failing check | What it means | Usual fix |
|---------------|---------------|-----------|
| `l2s_needed_preserved` / `l2s_work_preserved` | **conserves δ (C2/S2) violated** — some action grew your ranking set. | Rank over a monotone/union set; or add the missing component; or the action legitimately belongs to a *higher*-order component that should preempt this one. |
| `l2s_progress` / `l2s_progress_made` | **reduces δ (C3/S2) violated** — when the fair action fired and ψ held, δ did *not* shrink. | `work_progress` names the wrong action, or ψ is too weak (doesn't guarantee an element gets removed), or a safety invariant is missing that would rule out the spurious pre-state. |
| `l2s_sched_stable` | **scheduler not stable (S2)** — ψ was true, r didn't fire, but ψ went false. | Weaken ψ so it can't be falsified except by r; or the element ψ points at is being disturbed by another action (needs a higher-order component to preempt). |
| `l2s_sched_exists` | **S4 violated** — while φ holds, no scheduler is active. | ψ's disjunction doesn't cover all outstanding states; add/repair a component's ψ, or a component's δ domain is wrong. |
| `l2s_not_all_done` | while φ holds there should be work left, but the checker found "all done" yet not q. | The trigger/φ framing is off (often the property isn't in the auto-`work_start` shape); add an explicit `work_start`, or fix φ. |
| `l2s_progress_eventually` | **S3 (ψ ⇒ ♦r) violated** — a scheduled condition might never fire. | You scheduled a component whose fair action isn't actually assumed fair; check the `globally eventually` antecedents match the `work_progress` flags. |
| a plain safety `invariant … FAIL` at init or in an action | your added safety invariant isn't inductive. | Strengthen it or add supporting invariants exactly as in an ordinary Ivy safety proof. |

**Reading a CTI:** the small model lists the pre-state; look for
*physically impossible* combinations (e.g. `respond_channel(N)=true &
responded(N)=true` in the primary/backup example). If the bad state is
unreachable in the real system, you are missing a **safety invariant**, not a
ranking fix. If the bad state is reachable and progress genuinely doesn't
happen, your **ranking/scheduler** is wrong (or, rarely, the property is false).

---

<a name="7"></a>
## 7. Worked Example 1 — simple ranking: a distributed barrier

**File:** `example1_barrier_liveness.ivy` (verifies `OK`).

### 7.1 The system

A fixed, finite set of participants (`type node`) must all "check in" at a
barrier. A single fair action `gather` repeatedly picks *some* participant that
has not yet checked in and checks it in. The set of checked-in participants only
ever **grows** (monotone).

```ivy
#lang ivy1.8

finite type node

isolate barrier = {
    action gather

    specification {
        var checked_in_fair : bool
        relation checked_in(P:node)

        after init {
            checked_in(P)   := false;
            checked_in_fair := false;
        }

        before gather {
            checked_in_fair := true;
            checked_in_fair := false;
            if some p:node. ~checked_in(p) {
                checked_in(p) := true;
            }
        }

        invariant ~checked_in_fair

        temporal property [live]
        forall P. ((globally eventually checked_in_fair) ->
                   (globally (~checked_in(P) -> eventually checked_in(P))))
        proof {
            tactic skolemize;
            tactic ranking with {
                definition work_created(M:node) = true
                definition work_needed(M:node)  = ~checked_in(M)
                definition work_invar           = ~checked_in(_P)
                definition work_progress        = checked_in_fair
                definition work_helpful         = exists M. ~checked_in(M)
            }
        }
    }
} with node

export barrier.gather
```

### 7.2 The property

> `forall P. (□♦ checked_in_fair) -> □(¬checked_in(P) -> ♦ checked_in(P))`

"If `gather` runs infinitely often, then any participant that is currently
waiting is eventually checked in." The `forall P` is on the very outside so
`skolemize` lifts it to the constant `_P`; the body is the standard reactivity
shape `□(p → ♦q)` with `p = ¬checked_in(_P)`, `q = checked_in(_P)`. Because the
body ends in a `globally`, the `ranking` tactic auto-infers `work_start`, so we
do not write one.

### 7.3 The thought process behind the predicates

Walk the recipe of §5:

- **Tracked object:** a participant `_P`. Trigger `p`: `_P` is waiting.
  Goal `q`: `_P` checked in.
- **Pipeline:** trivially one stage — a waiting node becomes checked-in via
  `gather`. Only `gather` changes state, and it only ever *adds* to
  `checked_in`.
- **Ranking `work_needed` (δ):** here is the crucial design decision.
  The obvious candidate "the set of waiting nodes" *is* `~checked_in`. Is it
  conserved? `gather` **removes** an element from `~checked_in` (it checks
  someone in) and **never adds** one — because `checked_in` is monotone. So
  `~checked_in` shrinks monotonically: it is a valid ranking.
  `δ(M) = ~checked_in(M)`.
  *(Contrast: if the model let a node "check out" again, `~checked_in` would
  grow and this simple ranking would break — you'd need a different argument.)*
- **Justice condition `work_progress` (r):** the fair flag of the action that
  reduces δ. Only `gather` reduces δ, and its fairness flag is
  `checked_in_fair`. So `r = checked_in_fair`.
- **Scheduler `work_helpful` (ψ):** when does firing `gather` *definitely*
  reduce δ? Exactly when `gather`'s `if some p. ~checked_in(p)` guard is
  satisfied — i.e. when some node is still waiting: `ψ = exists M.
  ~checked_in(M)`. (For a single-component proof the scheduler is nearly
  ceremonial, but the `ranking` tactic requires it; it becomes essential with
  multiple components.)
- **Liveness invariant `work_invar` (φ):** "`_P` is still waiting,"
  `φ = ~checked_in(_P)`. This persists from the moment `_P` is waiting until it
  is checked in (the goal).
- **Finite bound `work_created` (R):** `node` is a `finite type`, so the whole
  universe is a finite bound: `R = true`.

### 7.4 Why it goes through

While `_P` is waiting, φ holds and δ = `~checked_in` is non-empty (it contains
at least `_P`). Every time `gather` runs (infinitely often, by fairness) with
ψ true, it removes one element from the finite δ. A finite set can't shrink
forever, so eventually the only way to keep δ from being reducible is for `_P`
itself to be checked in — the goal. `ivy_check` confirms all generated premises
(`l2s_created`, `l2s_needed_preserved`, `l2s_progress`,
`l2s_progress_eventually`, `l2s_sched_stable`, `l2s_sched_exists`) hold.

### 7.5 Non-vacuity check (actually run)

- Deleting `work_helpful` → `error: tactic requires a definition of
  work_helpful` (the `ranking` tactic requires it).
- Setting `work_progress = false` → `l2s_progress ... FAIL` and
  `l2s_progress_eventually ... FAIL` (with no fair action, no progress). 

Both confirm the parameters are load-bearing and the proof is not vacuous.

---

<a name="8"></a>
## 8. Worked Example 2 — stable schedulers: a two-stage approval pipeline

**File:** `example2_pipeline_liveness.ivy` (verifies `OK`).

### 8.1 The system

Each document must pass two stages:

```
stage 1 (pending_review)  --review-->  stage 2 (pending_signoff)  --signoff-->  done
```

Two fair actions: `review` moves one document from stage 1 to stage 2;
`signoff` completes one document from stage 2. No new documents are injected
while running (the initial workload all starts in stage 1).

```ivy
#lang ivy1.8

finite type doc

isolate pipeline = {
    action review
    action signoff

    specification {
        relation pending_review(D:doc)
        relation pending_signoff(D:doc)
        relation done(D:doc)

        var review_fair  : bool
        var signoff_fair : bool

        after init {
            done(D) := false;
            pending_signoff(D) := false;    # all initial work enters at stage 1
            review_fair  := false;
            signoff_fair := false;
        }

        before review {
            review_fair := true;
            review_fair := false;
            if some d:doc. pending_review(d) {
                pending_review(d)  := false;
                pending_signoff(d) := true;
            }
        }

        before signoff {
            signoff_fair := true;
            signoff_fair := false;
            if some d:doc. pending_signoff(d) {
                pending_signoff(d) := false;
                done(d)            := true;
            }
        }

        invariant ~review_fair
        invariant ~signoff_fair
        invariant ~(pending_review(D) & pending_signoff(D))
        invariant ~(pending_review(D) & done(D))
        invariant ~(pending_signoff(D) & done(D))

        temporal property [live]
        forall X. ((globally eventually review_fair)
                   & (globally eventually signoff_fair)
                   & (pending_review(X) | pending_signoff(X))) ->
                     (eventually done(X))
        proof {
            tactic skolemizenp;
            tactic l2s_auto5 with {
                definition work_created[0](M:doc) = true
                definition work_needed[0](M:doc)  = pending_review(M)
                definition work_invar[0]          = pending_review(_X) | pending_signoff(_X)
                definition work_progress[0]       = review_fair
                definition work_helpful[0]        = exists M. pending_review(M)

                definition work_created[1](M:doc) = true
                definition work_needed[1](M:doc)  = pending_review(M) | pending_signoff(M)
                definition work_invar[1]          = pending_review(_X) | pending_signoff(_X)
                definition work_progress[1]       = signoff_fair
                definition work_helpful[1]        = exists M. pending_signoff(M)
            }
        }
    }
} with doc

export pipeline.review
export pipeline.signoff
```

### 8.2 The property

> `forall X. (□♦review_fair & □♦signoff_fair & (pending_review(X) |
> pending_signoff(X))) -> ♦ done(X)`

"If both `review` and `signoff` fire infinitely often, then every document
currently somewhere in the pipeline is eventually done." Two fairness
assumptions ⇒ two justice conditions ⇒ we need `l2s_auto5`.

### 8.3 Why a *stable scheduler* is genuinely required here

This is the crux, and the reason this example is qualitatively harder than
Example 1. The natural combined ranking is "(# in stage 1, # in stage 2)." But:

- `review` **reduces** the stage-1 count while **increasing** the stage-2 count.
- `signoff` reduces the stage-2 count and doesn't touch stage 1.

So **neither justice condition always reduces the combined ranking**:
`signoff`'s fairness does nothing when stage 2 is empty, and `review`'s does
nothing when stage 1 is empty. We must *schedule* whichever action is helpful in
the current state. That is precisely Rule 8 (stable schedulers).

The engineering trick that makes it work: define the **low-order ranking as the
*union* of the remaining stages**, `pending_review ∪ pending_signoff`. Then:

- `review` moves a document from stage 1 to stage 2 — the document *stays in the
  union*, so `review` **conserves** the low-order ranking (no growth!).
- `signoff` removes a document from the union — it **reduces** it.
- The high-order ranking is just stage 1 (`pending_review`), reduced by
  `review`.

Lexicographically / with scheduling: while stage 1 is non-empty, `review` is
helpful and reduces the high-order set; once stage 1 empties, only `signoff` is
helpful and it reduces the union. Progress is guaranteed either way.

### 8.4 The thought process behind each predicate

- **Two justice conditions** `review_fair`, `signoff_fair` ⇒ two components
  `[0]` and `[1]`.
- **Component [0] — the "feeder" ranking:**
  - `work_needed[0] = pending_review(M)` (documents still in stage 1). Is it
    conserved by the *other* action `signoff`? `signoff` only touches stage 2,
    so yes. Is it reduced by `review`? Yes, when stage 1 is non-empty.
  - `work_progress[0] = review_fair`.
  - `work_helpful[0] = exists M. pending_review(M)` — `review` definitely
    reduces stage 1 exactly when stage 1 is non-empty.
- **Component [1] — the "drain" ranking:**
  - `work_needed[1] = pending_review(M) | pending_signoff(M)` — **the union**,
    chosen precisely so `review` (stage1→stage2) conserves it. Reduced only by
    `signoff`.
  - `work_progress[1] = signoff_fair`.
  - `work_helpful[1] = exists M. pending_signoff(M)` — `signoff` definitely
    reduces the union exactly when stage 2 is non-empty. **This is the
    load-bearing scheduler:** if you naively set it to `true`, the proof fails
    (see §8.6), because `signoff` firing while stage 2 is empty does *not* reduce
    the union.
- **`work_invar[i] = pending_review(_X) | pending_signoff(_X)`** for both:
  our tracked document is somewhere in the pipeline (not yet done). It persists
  until `done(_X)` (the goal).
- **`work_created[i] = true`**: `doc` is finite.

### 8.5 Safety invariants needed

The three disjointness invariants (`~(pending_review & pending_signoff)`,
`~(pending_review & done)`, `~(pending_signoff & done)`) are ordinary safety
invariants. They are needed so the ranking checker doesn't explore impossible
states where a document is in two stages at once (which would let the union
"not shrink" spuriously). Initializing `pending_signoff := false` (all work
enters at stage 1) is what makes the first disjointness invariant hold at init —
without it, `ivy_check` reports `pipeline.invar6 ... FAIL` at initialization
(discovered from the trace).

### 8.6 Non-vacuity / load-bearing check (actually run)

- Set **`work_helpful[1] = true`** → `l2s_progress_made[1] ... FAIL`. This is
  the decisive check: it proves the *stable scheduler is essential*, not
  cosmetic. Because `signoff` only reduces the union when stage 2 is non-empty,
  the scheduler must be `exists M. pending_signoff(M)`.
- Set **both** `work_helpful = true` → still `l2s_progress_made[1] ... FAIL`.
- Delete component **[1]** entirely → `l2s_not_all_done ... FAIL`: a single
  ranking cannot prove it, confirming two justice conditions are required.

(Contrast with a naive "two independent drains" design — e.g. serving two
independent priority classes where each action reduces its *own* disjoint set —
where `work_helpful = true` would still pass, because the two rankings never
interfere. That design does *not* exercise the stable scheduler. The pipeline is
deliberately built so the feeder action *grows* the drain's raw set, forcing the
union-ranking + scheduler construction. This is what makes it a real Rule-8
example rather than two parallel Rule-6 proofs.)

---

<a name="9"></a>
## 9. Synthesis heuristics: how to *invent* the predicates

A distilled, reusable procedure for going from "I have a fair transition system
and a liveness goal" to "I have the `work_*` definitions."

### 9.1 Finding `work_needed` (δ) — the ranking

1. **Write the goal `q` as a state predicate** (`done(_X)`, `checked_in(_P)`,
   `recv(t)`).
2. **δ is "the outstanding work that stands between now and q."** Start with the
   complement of the goal, restricted to the tracked object's "cohort."
3. **Conservation test (do this in your head *before* running Ivy):** for every
   action *other than* the intended reducer, does it add an element to δ? If
   yes, δ is wrong. Repair options, in order of preference:
   - **Use a monotone base set.** If `done` only grows, `~done` only shrinks —
     rank on `~done` rather than on a "pending" set that other actions refill.
   - **Take a union across downstream stages.** If action A moves objects from
     set S₁ into set S₂, then A grows S₂ but conserves `S₁ ∪ S₂`. Rank the
     lower-order component on the union. (Example 2.)
   - **Introduce an order (timestamps).** If objects are genuinely added in an
     unbounded stream and must be served in order, you cannot avoid an order:
     use an `unbounded_sequence` timestamp and rank on `{τ : τ ≤ _t ∧
     pending(τ)}`. (The paper's queue; the German `hyp3` FIFO channels.) This
     keeps δ finite because only timestamps ≤ the fixed `_t` count.
4. **Multiple reducers ⇒ multiple components.** If different fair actions reduce
   different parts of the outstanding work, make one component per action.

### 9.2 Finding `work_progress` (r)

Mechanical once δ is fixed: `r` is the fairness flag / signal of **the unique
action that removes elements from this specific δ.** If you find yourself wanting
two actions here, you actually have two components.

### 9.3 Finding `work_helpful` (ψ) — the scheduler

`ψ` = "the state in which firing `r` is *guaranteed* to reduce δ." Derive it
directly from the reducing action's **enabling guard**:

- Action guarded by `if some x. G(x) { … remove x … }` ⇒ `ψ = exists x. G(x)`.
- For a pipeline's low-order (union) component, the guard that guarantees
  reduction is "the drain stage is non-empty," e.g. `exists M.
  pending_signoff(M)`.
- **Stability self-check:** can any *other* action falsify ψ without `r`
  happening? If yes, either (a) that other action belongs to a higher-order
  component that should preempt this one (use `ranking` with the right ordering),
  or (b) ψ is stated over too specific an element — generalize it to an
  existential over the set. The `l2s_sched_stable` check will catch violations.

### 9.4 Finding `work_invar` (φ)

φ = "the tracked object is still outstanding." Almost always the negation of the
goal for `_X`, possibly disjoined over the stages it can occupy
(`pending_review(_X) | pending_signoff(_X)`). It must (a) hold at the trigger,
(b) be preserved until the goal, (c) imply δ is non-empty.

### 9.5 Finding `work_created` (R)

- Finite type ⇒ `true`.
- Timestamp/`unbounded_sequence` ranking ⇒ `X ≤ clock` (the current clock value
  bounds all produced timestamps; this is Rule 5's finiteness in action).

### 9.6 Finding the extra safety invariants

You don't invent these up front — you *harvest* them from CTIs. Each failing
`l2s_progress`/`l2s_needed_preserved` CTI shows a small pre-state; if that state
is unreachable in the real system, write the invariant that excludes it, prove
it inductively (ordinary Ivy), and re-run. This is exactly how the
primary/backup proof gained `respond_implies_not_responded` and
`req_replist_iff`.

---

<a name="10"></a>
## 10. Reference tables and gotchas

### 10.1 Minimal proof skeletons

**Simple ranking (Rule 6), via `ranking` with one component:**

```ivy
temporal property [live]
forall X. (□♦ fair) -> □( trigger(X) -> ♦ goal(X) )     -- shape with auto work_start
proof {
    tactic skolemize;
    tactic ranking with {
        definition work_created(M) = true
        definition work_needed(M)  = <outstanding set, must be conserved by all but reducer>
        definition work_invar      = <goal not yet reached for _X>
        definition work_progress   = fair
        definition work_helpful    = <enabling guard of the reducer, existential>
    }
}
```

**Stable schedulers (Rule 8), via `l2s_auto5` with n components:**

```ivy
temporal property [live]
forall X. (□♦ fair_1 & … & □♦ fair_n & trigger(X)) -> ♦ goal(X)
proof {
    tactic skolemizenp;
    tactic l2s_auto5 with {
        definition work_created[i](M) = true
        definition work_needed[i](M)  = <δ_i, conserved except by action i>
        definition work_invar[i]      = <goal not reached for _X>
        definition work_progress[i]   = fair_i
        definition work_helpful[i]    = <ψ_i: state where firing fair_i reduces δ_i>
        -- repeat for each i
    }
}
```

**Lexicographic (Rule 10), via `ranking` with ordered components:** same as
above but with `ranking` instead of `l2s_auto5`; `[0]` is highest order and is
allowed to preempt lower components (which may then temporarily grow). Use this
when a lower-order set can legitimately grow while a higher-order action runs
(reordering).

### 10.2 Command cheat-sheet

```bash
# verify
~/workplace/ivy-tools/ivy-venv/bin/ivy_check file.ivy

# get a liveness counterexample (CTI) for the first failing check
~/workplace/ivy-tools/ivy-venv/bin/ivy_check debug=true trace=true file.ivy

# bounded model check a property to sanity-test truth before proving:
#   append `attribute method = bmc[K]` to the file; BOUNDED/OK means no
#   violation within K steps.
```

### 10.3 Gotchas learned the hard way

1. **δ must be conserved by everything except its reducer.** The #1 cause of
   `l2s_needed_preserved` failures. If an action grows δ, restructure (monotone
   base, or union across stages).

2. **`work_progress` must name the action that reduces *this* δ.** Naming a
   neighboring stage's action gives `l2s_progress ... FAIL`. (The
   primary/backup bug.)

3. **Put `forall X` at the very outside** so `skolemize` lifts it to `_X`. A
   `forall` *inside* a `globally` produces an unbound `_X` and an
   `unknown symbol` error.

4. **The `ranking` tactic needs an explicit `work_start` unless the property
   ends in a bare `globally`.** Otherwise you get `KeyError: ''` from
   `str_invar`. Either shape the property `… -> globally (p -> ♦q)`, or provide
   `definition work_start = <trigger>` (as in Example… the shipped queue).

5. **Initialize downstream stages empty.** If a stage relation is arbitrary at
   init, disjointness invariants fail at initialization. Make the initial
   workload enter only at the first stage.

6. **Signals must pulse in one atomic step** (`now := true; now := false;`) and
   carry `invariant ~now`. Fairness flags likewise (`f := true; f := false;`
   with `invariant ~f`). Forgetting the invariant breaks the monitor.

7. **Watch for `∀∃` in *added* invariants** (paper §4.2). They break
   stratification and cause Z3 timeouts even when everything is "logically
   fine." Herbrandize the outer quantifier or add an auxiliary witness variable
   with a defining invariant.

8. **Build reality check:** on this install, plain `l2s_auto` reports "not in
   the fragment FAU" on the shipped queue benchmarks; `l2s_auto5` and `ranking`
   work. Prefer those two. Always confirm your incantation against a shipped
   example that verifies `OK` here (`ticket_l2s_auto.ivy`, `ticket_ranking.ivy`).

9. **Always do the non-vacuity check** (§7.5, §8.6): break a parameter and
   confirm the proof fails. A liveness proof that still passes with
   `work_progress = false` is proving nothing.

### 10.4 The one-paragraph summary

Ivy realizes McMillan's relational-ranking method by compiling a temporal goal
into a single safety obligation (`assert_no_fair_cycle`) over a
liveness-to-safety monitor whose `l2s_d` relation *is* the finite reached set
`R`. You supply, per justice condition, a ranking relation `work_needed` (δ)
that shrinks under the fair action `work_progress` (r) exactly when the scheduler
`work_helpful` (ψ) says it is helpful, all bounded by the finite `work_created`
(R) and held together by the liveness invariant `work_invar` (φ). `l2s_auto5`
combines several such rankings as stable-scheduled justice conditions (Rule 8);
`ranking` combines them lexicographically (Rule 10/11). Everything stays in EPR
because the ranking is a finite *set*, not a well-founded *function*, so the
prover always terminates and always gives you a counterexample to guide the
next iteration.
```
