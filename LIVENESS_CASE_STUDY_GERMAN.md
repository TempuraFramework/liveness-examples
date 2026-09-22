# Case Study: Proving Liveness of the German Cache Coherence Protocol in Ivy

*A complete record of the verification of "every client request eventually receives a
response" for the three-channel German protocol: what was built, what was learned about
Ivy's relational-ranking tactics, every dead end, and every caveat.*

Companion to `LIVENESS_GUIDE.md`. Where the guide explains the method, this file records
what actually happened when the method met a real protocol.

---

## 0. Summary of artefacts

| File | Rule | Components | Lemmas | Fairness assumed | `ivy_check` |
|---|---|---|---|---|---|
| `german_3channels_original.ivy` | Rule 8 (`l2s_auto5`) | 7 + 6 | `home_idle`, `live`→`request_answered` | weak everywhere **+ compassion for the arbiter** | OK, 2359 checks, 5.6 s |
| `german_3channels_lex.ivy` | Rule 10 (`ranking`) | 11 | none | same | OK, 1301 checks, 4.4 s |
| `german_3channels_fifo.ivy` | Rule 10 (`ranking`) | 10 | none | **weak fairness only** | OK, 1200 checks, 4.5 s |

`german_3channels_back.ivy` is the untouched safety-only baseline.

The three are not interchangeable. The first two prove the property for German *as
specified* (nondeterministic arbiter) and therefore must assume compassion. The third
proves it for a German *with a FIFO arbiter*, which needs only weak fairness. Neither
result implies the other.

**Toolchain.** `ms_ivy` 1.8.26, `ivy_check` at `/home/ruijie/workplace/venv_ivy/bin/ivy_check`.
The installed `ivy/ivy_l2s.py` and `ivy/ivy_ranking.py` are byte-identical to the reading
copy in `~/workplace/ivy/ivy/`, so all line numbers cited below are valid for both.

```bash
ivy_check german_3channels_original.ivy      # or _lex / _fifo
ivy_check debug=true trace=true <file>       # first failing check + its CTI
```

---

## 1. The model as given, and what had to change

### 1.1 The protocol

One home directory, `client` caches, three unit-capacity channels *per client*:

```
channel1(C)   : client -> home    empty1 | reqshared | reqexclusive
channel2_4(C) : home   -> client  empty2_4 | invalidate | grantshared | grantexclusive
channel3(C)   : client -> home    empty3 | invalidateAck
```

Home state: `homeCurrentCommand`, `homeCurrentclient`, `homeSharerList(C)`,
`homeinvalidateList(C)`, `homeexclusiveGranted`. Ten rules. The baseline file verified
`OK` for safety as delivered, and switching `#lang ivy1.7` → `ivy1.8` changed nothing —
the whole file, `object s = { ... }` included, is accepted verbatim by the 1.8 front end.

### 1.2 Changes made to the model

Five, in decreasing order of significance:

1. **`finite type client`** (was `type client`). Needed so `work_created = true` is a
   legitimate finite bound `R` (Rule 5). Without it the `l2s_created` checks have no
   finite reached set to appeal to. This is faithful — German is a fixed, arbitrary
   number of caches.
2. **Ghost `waiting(C)`**, raised by the request rules, lowered by the two grant-receipt
   rules. This is the predicate the liveness property is about (§2).
3. **`require ~s.waiting(cl)` on both request rules**, so a client blocks until served.
   Without it a client can issue a second request while the first is in service and the
   obligation stops being well posed (§2.1).
4. **Fairness instrumentation** on every rule, and conversion of every fair rule from
   `require`-style to guarded-command style (§3). This is the change with the subtlest
   consequences.
5. **`ts`/`clock`/`reqts` and FIFO arbitration** — only in `german_3channels_fifo.ivy` (§8).

Five safety invariants were added (§9). The original nine are untouched.

---

## 2. Formalizing "any request receives a response"

### 2.1 Why a ghost `waiting` bit, and why clients must block

The obvious candidates are all wrong:

- **`globally (channel1(C) ~= empty1 -> eventually cache(C) ~= invalid)`** is *vacuous for
  upgrades*. `reqexclusiveRule` is enabled when `cache(cl) = shared`, so `cache(C) ~= invalid`
  already holds the moment the trigger fires. The obligation is discharged by the state the
  client was already in.
- **`... -> eventually channel2_4(C) = grant*`** stops at "the home replied", not "the client
  was served", and says nothing about delivery.
- **`... -> eventually channel1(C) = empty1`** only says the request was *picked up*.

The formulation used is:

```ivy
explicit temporal property [live]
  forall C. globally (s.waiting(C) -> eventually ~s.waiting(C))
```

`waiting(C)` is raised exactly where a request is issued and lowered exactly where the
corresponding grant is consumed, so `~waiting(C)` is precisely "the access completed".
`german_3channels_original.ivy` also carries the literal phrasing as a corollary:

```ivy
explicit temporal property [request_answered]
  forall C. globally (s.channel1(C) ~= empty1 -> eventually ~s.waiting(C))
```

**Clients must block.** `reqsharedRule(cl)` requires only `cache(cl) = invalid &
channel1(cl) = empty1`; after the home picks the request, `channel1(cl)` is empty again and
`cache(cl)` is still `invalid`, so the client could immediately queue a *second* request
while the first is in service. Then `waiting` no longer identifies a single request and the
three-stage decomposition below collapses. `require ~s.waiting(cl)` is the standard German
modelling assumption (and matches `german_3_unbounded_channels.ivy` in this repo).

### 2.2 The three-stage decomposition

Every proof in all three files rests on this:

```
stage 1   channel1(C) ~= empty1                              request queued at the home
stage 2   homeCurrentCommand ~= empty1 & homeCurrentclient = C   the home is serving C
stage 3   channel2_4(C) = grantshared | = grantexclusive      grant in flight to C
```

captured by the added invariant

```ivy
invariant [waiting_stages]
    s.waiting(C) <-> (s.channel1(C) ~= empty1
                      | (s.homeCurrentCommand ~= empty1 & s.homeCurrentclient = C)
                      | s.channel2_4(C) = grantshared
                      | s.channel2_4(C) = grantexclusive)
```

plus `stage1_excl` and `stage2_excl` making the stages pairwise disjoint. `waiting_stages`
is what discharges the "something is always scheduled" premise (S4 /
`l2s_sched_exists`): one scheduler per stage, and the invariant says a waiting client is
always in one of them. `stage2_excl` additionally does real work inside the pipeline
argument — see §9.

---

## 3. Fairness encoding: the vacuity trap

This is the single most important practical finding in the whole exercise.

### 3.1 The trap

The tempting encoding, and the one partly present in `my_primary_backup.ivy`, is

```ivy
action foo(n) = {
    foo_fair := true; foo_fair := false;      # pulse
    require <guard>;                          # <-- trap
    <body>
}
explicit temporal axiom [f] globally eventually foo_fair
```

In an exported action `require` is an assumption on the environment, so any trace in which
the flag pulses while the guard is false is *pruned*. `globally eventually foo_fair` then
does not mean "the scheduler offers `foo` a turn infinitely often"; it means **"`foo`
successfully executes infinitely often"**. Consequences:

- It is strictly stronger than strong fairness — it asserts the action *runs*, not merely
  that it runs *if enabled*.
- If the guard can never hold in some execution, the assumption is unsatisfiable there and
  the property becomes **vacuously true on that execution**. For `pickNewRequestRule(C)`
  this is concrete: a client that never requests makes `globally eventually f_pick(C)`
  unsatisfiable, and the whole property is discharged for free.

Nothing in `ivy_check`'s output warns about this. It reports `OK`.

### 3.2 The discipline used here

Every fair rule is a **guarded command** with the flag pulsed *before* the guard:

```ivy
action sendinvalidateRule(cl:client) = {
    wf_sendinv(cl) := true;
    wf_sendinv(cl) := false;
    if <guard> { <body> }
}
invariant ~wf_sendinv(C)
```

Now the action is always callable, a turn on a disabled rule is a stutter step, and
`globally eventually wf_sendinv(C)` is a satisfiable statement about the *scheduler*.
This is the style of `bakery.ivy`, and it is the only style that keeps the assumptions
honest. Ten `wf_*` flags, one per rule.

Two consequences to keep in mind:

- **The two request rules keep `require` and get no fairness flag.** They are environment
  actions; we never want to force requests to be issued. A `require` with no fairness flag
  is harmless.
- **A weak-fairness flag is not usable as a ranking's progress condition on its own.**
  It pulses even when the rule no-ops. The `work_helpful` scheduler must therefore imply
  the rule's *enabling guard*, so that when the flag pulses the body actually runs. In
  `german_3channels_lex.ivy` and `_fifo.ivy` every pipeline scheduler is literally the
  guard of its rule, for exactly this reason (and for a second reason — §6.2).

### 3.3 Two kinds of flag

| flag | pulsed | meaning | used as |
|---|---|---|---|
| `wf_*` | unconditionally, before the guard | "the scheduler offered this rule a turn" | `work_progress` under weak fairness |
| `f_pick(C)`, `f_granted(C)` | inside the guard | "the rule actually fired" | the `taken` half of compassion; lemma goals |

`f_granted(C)` (the home actually responded to C) is kept in
`german_3channels_original.ivy` as instrumentation even though the final proof does not
use it; `german_3channels_fifo.ivy` drops both event signals.

---

## 4. Why German needs compassion

### 4.1 The starvation argument

`pickNewRequestRule(cl)` picks an **arbitrary** client with a pending request. Under weak
fairness the scheduler must offer `pickNewRequestRule(_C)` a turn infinitely often, but it
may offer every one of those turns while `homeCurrentCommand ~= empty1`. Other clients
cycle request → service → request forever; the home is idle only in the instants between a
grant and the next pick, and the adversary simply never schedules `_C`'s turn in one of
those instants. **The property is false under weak fairness alone.** This is not an
artefact of the encoding; it is a property of an arbiter that does not remember who is
waiting.

So the assumption is *compassion* (strong fairness) for the arbiter, and only for it:

```ivy
explicit temporal axiom [sf_pick]
  forall C. (globally eventually (s.homeCurrentCommand = empty1 & s.channel1(C) ~= empty1))
            -> (globally eventually f_pick(C))
```

Abbreviate the antecedent `E(C)`. This does **not** assume the conclusion: `globally
eventually E(_C)` still has to be discharged, and that is the entire content of the
stage-1 argument.

### 4.2 Every other rule only needs weak fairness — the stability audit

A rule needs only weak fairness if its guard, once true, stays true until the rule itself
fires. This was checked by hand for all ten rules before writing any proof; it is the
analysis that decided the shape of everything downstream.

| rule | guard stable once enabled? | why |
|---|---|---|
| `pickNewRequestRule(cl)` | **no** | another client's pick falsifies `homeCurrentCommand = empty1` |
| `sendinvalidateRule(cl)` | yes | grants are blocked while `homeSharerList(cl)`; `channel2_4(cl)` only filled by this rule |
| `sharerinvalidatescacheRule(cl)` | yes | `channel2_4(cl) = invalidate` only cleared here; `channel3(cl) = empty3` follows from an invariant |
| `receiveinvalidateAckRule(cl)` | yes | both grant rules are blocked while an ack is pending |
| `receivesharedGrantRule(cl)` / `receiveexclusiveGrantRule(cl)` | yes | only these clear a grant from `channel2_4(cl)` |
| `grantsharedRule` | yes | `sendinvalidate` cannot fill `channel2_4(hcc)` when `~homeexclusiveGranted` |
| `grantexclusiveRule` | yes | `sendinvalidate(hcc)` needs `homeinvalidateList(hcc)` → `homeSharerList(hcc)`, which blocks the rule anyway |

Exactly one row says "no". That single row is responsible for the tableau case split in
two of the three proofs, and for the entire existence of `german_3channels_fifo.ivy`.

**Note the asymmetry that §8 exploits:** the instability is caused by the rule being
*parameterized by the client*. The guard of an *unparameterized* pick — "the home is idle
and somebody is queued" — is stable, because only a pick can falsify it.

---

## 5. Proof 1 — two-step, Rule 8 (`german_3channels_original.ivy`)

### 5.1 Structure

```
[home_idle]  globally (homeCurrentCommand ~= empty1 -> eventually homeCurrentCommand = empty1)
             l2s_auto5, 7 justice conditions, weak fairness only
[live]       forall C. globally (waiting(C) -> eventually ~waiting(C))
             l2s_auto5, 6 justice conditions, uses [home_idle] + [sf_pick]
[request_answered]  the literal phrasing, chained off [live]
```

`home_idle`'s seven components are the invalidation pipeline, one per rule, each ranking on
a **superset of the stages still to come** so the advancing rule conserves it:

| # | `work_needed` (δ) | `work_helpful` (ψ) | `work_progress` (r) |
|---|---|---|---|
| 0 | `homeSharerList(N)` | `channel3(N) = invalidateAck` | `wf_recvack(N)` |
| 1 | `... & channel3(N) ~= invalidateAck` | `channel2_4(N) = invalidate` | `wf_sharerinv(N)` |
| 2 | `... & channel2_4(N) ~= invalidate` | `invalidateList(N) & channel2_4(N) = empty2_4 & INV` | `wf_sendinv(N)` |
| 3 | `homeSharerList(N) & channel2_4(N) = grantshared` | `channel2_4(N) = grantshared` | `wf_recvshared(N)` |
| 4 | `homeSharerList(N) & channel2_4(N) = grantexclusive` | `channel2_4(N) = grantexclusive` | `wf_recvexcl(N)` |
| 5 | `homeCurrentCommand ~= empty1` | guard of `grantsharedRule` | `wf_grantshared` |
| 6 | `homeCurrentCommand ~= empty1` | guard of `grantexclusiveRule` | `wf_grantexcl` |

(`INV` = `homeCurrentCommand = reqexclusive | (homeCurrentCommand = reqshared &
homeexclusiveGranted)` — "the home is in an invalidation phase".)

Components 3 and 4 are easy to miss: a client that still holds an unconsumed grant in
`channel2_4` **blocks the invalidate the home needs to send it**, so draining the stale
grant is a genuine pipeline stage.

`home_idle` verified on the **first attempt**. It is structurally the same proof as
`my_primary_backup.ivy`.

The main property's six components are one scheduler per stage, with stage 1 split into the
three cases of the tableau for `E` (following `strongfair.ivy`):

| # | case | δ | ψ | r |
|---|---|---|---|---|
| 0 | `E` finitely often, not finished | `eventually E` | `~(globally eventually E) & (eventually E)` | `~(eventually E)` |
| 1 | `E` never again | `waiting(_C)` | `~(eventually E) & channel1(_C) ~= empty1` | `homeCurrentCommand = empty1` |
| 2 | `E` infinitely often | `channel1(_C) ~= empty1` | `(globally eventually E) & channel1(_C) ~= empty1` | `f_pick(_C)` |
| 3 | stage 2 | `channel1(_C) ~= empty1 \| (cmd ~= empty1 & hcc = _C)` | `cmd ~= empty1 & hcc = _C` | `homeCurrentCommand = empty1` |
| 4 | stage 3 | `waiting(_C)` | `channel2_4(_C) = grantshared` | `wf_recvshared(_C)` |
| 5 | stage 3 | `waiting(_C)` | `channel2_4(_C) = grantexclusive` | `wf_recvexcl(_C)` |

Component 1 is a **contradiction component** (§6.9): its δ never reduces, and the premise
is discharged because `ψ ∧ r` is inconsistent — `~◇E` plus an idle home plus a queued
request *is* `E`. Component 3 is *not*, despite `ψ ∧ r` also looking contradictory: `ψ` and
`r` are read at different times (§6.9), so it needs a δ that genuinely shrinks, which is why
it ranks on the **union** of stages 1 and 2 rather than on `waiting(_C)`. Both get
`ψ ⇒ ◇r` from `[home_idle]`.

### 5.2 Why the lemma was unavoidable here

Rule 8 requires **every** ranking to be conserved by **every** action. The invalidation
pipeline has to play two roles:

1. drive the home to finish *some other client's* command while `_C` sits in stage 1;
2. drive the home to finish *`_C`'s own* command in stage 2.

Role 1 is incompatible with conservation: another client's `grantsharedRule` sets
`homeSharerList(hcc) := true`, growing δ₀, while the goal `~waiting(_C)` is nowhere near.
Under Rule 8 there is no way to express "this ranking is allowed to grow right now", so the
pipeline had to be lifted out into a separate lemma with its own `work_invar`. That is the
entire reason `home_idle` exists.

---

## 6. What the tactics actually do — findings from the source

Everything in this section was read out of `ivy_l2s.py` / `ivy_ranking.py` and then
confirmed by experiment. These are the facts that cost the most time to discover.

### 6.1 Temporal formulas in `work_*` are ordinary state variables

`globally p` inside a tactic block is **not** "a temporal invariant". The tableau
construction (`ivy_l2s.py:1028-1037`) gives every `globally p` subformula a Boolean state
variable `l2s_g[p]` that is havoc'd at each step and pinned by three assumptions:

```python
pre.append(AssignAction(old_l2s_g(...), l2s_g(...)))          # remember old value
pre.append(HavocAction(l2s_g(...)))                           # genuine mutable state
pre.append(AssumeAction(old_g -> g))                          # []p persists forward
pre.append(AssumeAction((~old_g & p) -> ~g))                  # ~[]p & p -> ~X[]p
post.append(AssumeAction(g -> p))                             # []p -> p
```

So `(globally eventually E) -> (globally eventually f_pick(_C))` is a **propositional**
implication between two state variables. Every VC stays first-order; the modal notation in
`ivy_check`'s output is only the pretty-printer naming variables after the formulas they
stand for.

### 6.2 `ranking` (Rule 10) vs `l2s_auto5` (Rule 8): only *two* premises get the preemption discount

In `ivy_ranking.py`, `no_help` is computed at line 332 as
`old_of(Not(Or(*helps)))` where `helps` accumulates
`And(work_invar, exists(args, work_helpful))` per component **after** the current one is
processed (line 339) — so `no_help[i] = ¬⋁_{j<i} helps_j`, strictly higher-order
components. It is then used in exactly two places:

| generated check | line | guarded by `no_help`? | obligation |
|---|---|---|---|
| `l2s_needed_preserved` | 337 | **yes** | conserves δ |
| `l2s_sched_stable` | 393 | **yes** | ψ ∧ ¬r → ψ′ |
| `l2s_progress` | 363 | **no** | ψ ∧ r → reduces δ |
| `l2s_progress_eventually` | 377 | **no** | ψ ⇒ ◇r |
| `l2s_invar` | 326 | no | φ preserved after the trigger |
| `l2s_sched_exists` | 402 | n/a | φ → ⋁ᵢ ψᵢ (uses `work_invar` of `sorted_tasks[0]`) |

**Practical consequence, and the thing that broke the first lexicographic attempt:** a
preempted component may *grow*, but it must still *reduce whenever its own scheduler is
on*, preempted or not. So a scheduler cannot be a loose "this stage is non-empty"
predicate that happens to be true in states where the rule is disabled; it must imply the
rule's enabling guard. In `home_idle` (Rule 8) `work_invar = homeCurrentCommand ~= empty1`
silently supplied the missing part of several guards. With `work_invar = waiting(_C)` that
crutch is gone and every scheduler has to carry its own guard. This is why, e.g.,
components [06]/[07] of `_lex.ivy` carry `INV` rather than just
`channel2_4(N) = grantshared`.

### 6.3 Component suffixes are sorted as **strings**

`ivy_ranking.py:176`:

```python
sorted_tasks = list(sorted(x for x in tasks))
```

With single-digit suffixes and eleven components the lexicographic order silently becomes
`[0] [1] [10] [2] [3] … [9]` — `[10]` lands *third from the top*. The first lexicographic
attempt failed 45 checks partly for this reason. **Always write two-digit suffixes**
(`[00]`…`[10]`) as soon as there are ten or more components. Under `l2s_auto5` the order is
irrelevant (Rule 8 has no preemption), so this only bites the `ranking` tactic.

### 6.4 `work_start` is auto-inferred as `¬(body of the outermost globally)`

`ivy_l2s.py:268-276`: the tactic walks down through `Implies` to the outermost `Globally`
and sets

```python
work_start = Definition(Symbol('work_start'+sfx), Not(gfmla.body))
```

So for `globally (p -> eventually q)` the trigger is `p & ~(eventually q)` — *"p holds and
the goal never happens"*, not just `p`. That "and never again" half is what makes the next
two findings work.

### 6.5 `l2s_not_all_done`: the goal must be a state predicate that pins `work_invar`

`ivy_l2s.py:341-351, 515, 542` build, for `l2s_auto5`:

```
l2s_not_all_done  ≡  ¬not_waiting_for_start  ∨  ⋁ᵢ ∃x. work_invarᵢ ∧ work_neededᵢ(x)
```

i.e. *once the trigger has been seen, some ranking is non-empty — forever*. Combined with
§6.4, "forever" is under the hypothesis `¬(eventually q)`. Therefore:

> **`¬(eventually q)`, together with the safety invariants, must imply that `work_invar`
> persists from the trigger onward.**

- `home_idle` satisfies this trivially: `q = (cmd = empty1)`, so `¬◇q → cmd ~= empty1 = φ`.
- `my_primary_backup.ivy` satisfies it non-trivially: `φ = requesting`, `q = acking`, and
  the only exit from `requesting` is to `acking`, which `¬◇q` blocks.
- **A pulse goal cannot satisfy it.** `¬◇f_granted(_C)` tells you nothing about the
  protocol state, so nothing pins φ.

This was the first real dead end (§7.1), and it was isolated with a controlled experiment:
two properties with *identical* rankings, *identical* `work_invar`
(`cmd ~= empty1 & hcc = _C`) and *identical* trigger, differing only in the goal.

| goal | result |
|---|---|
| `eventually f_granted(C)` (pulse) | `l2s_not_all_done ... FAIL` |
| `eventually ~(cmd ~= empty1 & hcc = C)` (= `¬work_invar`) | **OK** |

**Rule of thumb:** make the goal a state predicate and take `work_invar = ¬goal` unless you
have a specific reason not to. Use event pulses for *progress conditions*, not for goals.

### 6.6 `l2s_invar`: `work_invar` must be preserved from the trigger

`ivy_ranking.py:326` generates `(old(work_invar) ∨ ¬waiting_for_trigger) → work_invar`.
This is the `φ′` half of premise C2/S2 and is *not* conditioned on the goal not having
happened — the monitor relies on the tableau to exclude the transition that would falsify
φ. Another reason `work_invar = ¬goal` is the safe default: then falsifying φ *is* reaching
the goal, which the `¬◇q` hypothesis already forbids.

### 6.7 Fairness axioms must be instantiated at the right term

A temporal atom is created per *syntactic* formula. `□◇wf_recvshared(_C)` and
`□◇wf_recvshared(C)` (bound `C`) are **different propositions**, and Z3 will not equate
them even in a model where `_C = 0`. The CTI for this is unmistakable and looks like a
tool bug until you see it:

```
_C = 0
[] <> wf_recvshared(0)  = true       <-- the forall-instance
<>  wf_recvshared(_C)   = false      <-- what the component needs
```

- If `work_progress[i]` mentions the Skolem constant (`wf_recvshared(_C)`), you need
  `instantiate wfa_recvshared with C = _C;`.
- If it mentions the component's own bound variable (`wf_recvshared(N)`), plain
  `instantiate wfa_recvshared;` matches.

**Cleaner alternative, used in `_lex.ivy` and `_fifo.ivy`:** never mention `_C` in a
progress condition. Write `work_progress[02](N:client) = wf_recvshared(N)` and put the
Skolem constant in the scheduler instead: `work_helpful[02](N) = N = _C & channel2_4(_C) =
grantshared`. Then one `∀`-instantiation serves every component and the `with C = _C`
variants disappear.

### 6.8 A temporal hypothesis must be re-stated as an `invariant` to be usable at every state

`instantiate sf_pick with C = _C` makes the compassion axiom a **premise of the temporal
goal**, which pins it at the *initial* state. But `l2s_progress_eventually[01]` is a
*postcondition* checked at every state. Ivy does not promote premises to invariants, so the
axiom must be re-stated inside the tactic block:

```ivy
invariant (globally eventually (s.homeCurrentCommand = empty1
                                & s.channel1(_C) ~= empty1))
          -> (globally eventually f_pick(_C))
```

The lift from "time 0" to "all times" is *sound* because `□◇p` is insensitive to finite
prefixes (`□◇p` at *t* iff `□◇p` at 0), and *inductive* from the local tableau constraints:
forward by `old_g → g`, backward by `X◇p → ◇p`. Ivy proves it; you just have to ask.

Verified both ways:

| file | invariant removed |
|---|---|
| `german_3channels_lex.ivy` | `l2s_progress[01]`, `l2s_progress_eventually[01]` FAIL |
| `german_3channels_original.ivy` | `l2s_progress_made[2]` FAIL |

McMillan's own `strongfair.ivy` carries the same line, with the comment *"we need to know
that the strong fairness condition is invariant… It is inductive by the tableau
constraints."* So this is the idiom, not a workaround.

### 6.9 Contradiction components only work when the scheduler is *persistent*

A useful pattern (it is how `strongfair.ivy` discharges its cases) is a component whose δ
never shrinks — `work_needed = true`, or anything constant — where the progress obligation
is instead discharged because `ψ ∧ r` is inconsistent. It is tempting to reach for it
whenever `r` is literally the negation of part of `ψ`.

It does **not** always work, and the reason is a timing subtlety. `l2s_progress` is

```
old(work_invar) ∧ old(work_helpful) ∧ ¬waiting_for_progress  →  decreased
```

`work_helpful` is read **at the freeze point**, while `¬waiting_for_progress` only says `r`
occurred **at some later instant**. Z3 is not handed the state at that instant. So "ψ and r
are contradictory *at the same state*" is not by itself enough — the solver has to be able
to conclude that ψ *still held* when r fired. It can do that only when ψ is persistent, so
that `l2s_sched_stable` (or a tableau persistence fact) carries it forward.

- Works: `ψ = ~(eventually E) & channel1(_C) ~= empty1`. `~◇E` is a tableau bit and persists
  by construction, and under it `pickNewRequestRule(_C)` cannot fire, so the second conjunct
  persists too. When `r` (`cmd = empty1`) fires, ψ still holds, `E` holds, contradiction.
- Fails: `ψ = cmd ~= empty1 & hcc = _C` with `r = ~(cmd ~= empty1 & hcc = _C)`. Nothing makes
  ψ persistent across the gap, so the antecedent is satisfiable and Ivy demands a real
  reduction. Hence component 3 of §5.1 ranks on the union `channel1(_C) ~= empty1 |
  (cmd ~= empty1 & hcc = _C)`, which the pick conserves (stage 1 → stage 2 stays inside the
  union) and the grant empties.

**Rule of thumb:** a contradiction component is only safe when `work_helpful` is built from
tableau bits (`~(eventually p)`, `globally eventually p`) or from state that provably cannot
change until `r` fires. Otherwise build a real ranking, and take the union across the
remaining stages so the advancing rule conserves it.

---

## 7. Dead ends, in the order they were hit

### 7.1 `home_serves` with a pulse goal — `l2s_not_all_done`

The first decomposition was four lemmas: `home_idle`, `home_serves` ("whoever the home is
serving eventually gets a grant", goal `eventually f_granted(C)`), `picked`, and
`grant_delivered`. `home_serves` failed `l2s_not_all_done ... FAIL` (3 instances) with a CTI
showing `grantexclusiveRule` firing from `cmd = reqexclusive, hcc = _C = 0` into a state
where every ranking is empty. Diagnosis and fix: §6.5.

**The fix was not to repair `home_serves` but to delete it.** Once `q` has to be a state
predicate, `home_serves` collapses into `home_idle` (`cmd = empty1` implies
`~(cmd ~= empty1 & hcc = C)`), and the stage-2 component of the main proof can take
`r = homeCurrentCommand = empty1` directly. Four lemmas became one.

### 7.2 Mis-instantiated fairness — `l2s_progress_made[4]`/`[5]`

See §6.7. One-line fix once the CTI is read correctly; otherwise mystifying.

### 7.3 First lexicographic attempt — 45 failed checks

Three independent mistakes at once:

- single-digit suffixes → scrambled order (§6.3);
- schedulers not implying their rules' guards, because `l2s_progress` is not
  preemption-guarded (§6.2);
- `homeCurrentCommand ~= empty1` conjoined into δ[07]/δ[08] (correct for conservation) while
  their ψ did not imply it, so the reduction obligation was unsatisfiable when the home
  went idle. Fixed by conjoining `INV` into *both* δ and ψ for those two components.

### 7.4 `strongfair_encoded.ivy` does not verify on this build

The repo's manual-tableau encoding of strong fairness (`f_sending` bit + `assume`) reports
`error: failed checks: 1`. `strongfair.ivy` (axiom + `ranking` + the three-way case split)
verifies `OK` in 2.7 s and was used as the template throughout.

### 7.5 A missing axiom, silently inherited

`german_3channels_lex.ivy` was sliced from `german_3channels_original.ivy` *before*
`wfa_pick` was appended, so neither derived file had it. Harmless in `_lex.ivy` (unused),
but in `_fifo.ivy` it surfaced as `error: No property wfa_pick exists in the current
context`. Worth remembering when deriving files by slicing: a proof that never instantiates
an axiom will not tell you the axiom is gone.

---

## 8. Proof 3 — trading compassion for a fair arbiter (`german_3channels_fifo.ivy`)

The compassion invariant of §6.8 exists only because compassion is a *conditional* fairness
assumption whose antecedent has to be case-split on the tableau. Removing the need for
compassion removes the whole apparatus.

**Model change.** Requests get timestamps (`instance ts : unbounded_sequence`, `clock`,
`reqts(C)`), and `pickNewRequestRule` becomes **unparameterized** and serves the oldest:

```ivy
action pickNewRequestRule = {
    wf_pick := true; wf_pick := false;
    if s.homeCurrentCommand = empty1 {
        if some cl:client. s.channel1(cl) ~= empty1 minimizing s.reqts(cl) { ... }
    }
}
```

By the asymmetry noted at the end of §4.2 its guard is now stable, so
`globally eventually wf_pick` suffices.

**Proof.** One `ranking` call, ten components, **zero temporal operators inside the block**:

```
[00]       clients whose queued request is at least as old as _C's     (highest)
[01],[02]  _C's grant is in flight and has to be consumed
[03]..[09] the home's invalidation pipeline                            (lowest)
```

`[00]` is the CAV'24 "pending timestamps ≤ mine" ranking, but carried over **clients**
rather than timestamps:

```ivy
definition work_needed[00](N:client) = s.channel1(N) ~= empty1 & s.reqts(N) <= s.reqts(_C)
definition work_helpful[00](N:client)= s.homeCurrentCommand = empty1 & s.channel1(_C) ~= empty1
definition work_progress[00](N:client)= wf_pick
```

Two payoffs from carrying it on clients: `work_created = true` stays valid (finite type,
no `T <= clock` bound needed), and every component in the file has the same sort, avoiding
the untested mixed-sort case. The single supporting invariant is

```ivy
invariant [ts_below_clock] s.reqts(C) < clock
```

which is what makes the ranking shrink: a newly issued request gets `reqts = clock >
reqts(_C)` and so can never join it.

**Why it is still lexicographic.** The pipeline rankings are grown by any grant *and* by
any pick, both of which happen freely while `_C` is in stage 1 or 3. Legal under Rule 10
because whenever the home is idle — the precondition of a pick — either `[00]` is scheduled
(`_C` still queued) or `_C` is past stage 1 and `[01]`/`[02]` is. Working out the
non-preempted region gives, as in `_lex.ivy`,

```
¬pre([03]..[09]) ∧ waiting(_C)  ⟹  homeCurrentCommand ~= empty1
```

— here a purely first-order consequence of `waiting_stages` — which is why every pipeline
ranking carries `homeCurrentCommand ~= empty1`.

**Caveat, stated plainly.** This is an *incomparable* theorem, not a stronger one: weaker
scheduler assumption, but only about a home that implements FIFO arbitration. German as
literally specified is not starvation-free without compassion, and the ablation in §10.3
is precisely that counterexample.

---

## 9. The added safety invariants and where they came from

None were invented up front; all were harvested from CTIs or from hand-checking the
"something is always scheduled" premise.

| invariant | what it excludes | needed for |
|---|---|---|
| `waiting_stages` | a waiting client in no stage | `l2s_sched_exists` in all three proofs |
| `stage1_excl` | a queued request while an older one of the same client is in service | disjointness; δ conservation for the stage unions |
| `stage2_excl` | the home serving C while C's grant is already in flight | **the pipeline S4 argument** — it is what proves `channel2_4(homeCurrentclient) = empty2_4` in the "no sharers left" case, so `grantexclusiveRule`'s guard holds |
| `excl_owner_is_sharer` | `homeexclusiveGranted` with no owner on the sharer list | gives the invalidation phase a concrete client to work on |
| `inv_in_flight` | a sharer off the invalidate list with nothing in flight | no sharer can be "stuck outside the pipeline"; without it S4 has a hole |

`inv_in_flight` is the interesting one:

```ivy
invariant [inv_in_flight]
    (s.homeCurrentCommand = reqexclusive
     | (s.homeCurrentCommand = reqshared & s.homeexclusiveGranted))
    & s.homeSharerList(C) & ~s.homeinvalidateList(C)
    -> (s.channel2_4(C) = invalidate | s.channel3(C) = invalidateAck)
```

It is inductive because `pickNewRequestRule` re-snapshots `invalidateList := sharerList`
(making the antecedent false for every client), `sendinvalidateRule` moves a client from the
list into `channel2_4`, `sharerinvalidatescacheRule` moves it on to `channel3`, and both
grant rules set `homeCurrentCommand := empty1`, falsifying the antecedent. Crucially,
`homeSharerList` **cannot grow during a command**: it is written only by the two grant
rules, and both end the command in the same step.

---

## 10. Non-vacuity: methodology and full results

A liveness proof that still passes with a broken parameter proves nothing. Every claim
below was produced by mutating a verifying file and re-running `ivy_check`.

### 10.1 Reachability of the interesting states

Add a deliberately false invariant and confirm it is *violated*. (If it holds, the state is
unreachable and your property may be about nothing.)

| probe | result |
|---|---|
| `~s.waiting(C)` | violated — clients do wait |
| `s.cache(C) ~= shared` / `~= exclusive` | violated |
| `s.channel2_4(C) ~= invalidate` | violated |
| `s.channel3(C) ~= invalidateAck` | violated |
| `s.homeCurrentCommand ~= reqexclusive` | violated |
| two clients sharing simultaneously | violated |
| **a client queued while the home serves someone else** | violated — the starvation scenario is reachable |

The FIFO model was probed separately, including "two clients queued at once" (violated), so
its arbitration is genuinely exercised.

### 10.2 `german_3channels_original.ivy`

| mutation | result |
|---|---|
| drop `instantiate sf_pick` | FAIL |
| drop `instantiate home_idle` | FAIL |
| drop the compassion `invariant` | FAIL — `l2s_progress_made[2]` |
| `work_progress[2] := false` (the pick) | FAIL |
| `work_progress[3] := false` (stage 2) | FAIL |
| `work_progress[4] := false` (stage 3) | FAIL |
| `work_helpful[4] := true` | FAIL |
| `home_idle`'s `work_progress[5] := false` | FAIL |
| corollary without `instantiate live` | FAIL |

### 10.3 `german_3channels_lex.ivy`

| mutation | failing checks |
|---|---|
| **`l2s_auto5` instead of `ranking`** | 14 × `l2s_progress_made[04..10]` |
| **stage-1 components demoted to lowest** | 7 × `l2s_needed_preserved[04..10]` |
| **stage-3 components demoted below the pipeline** | 7 × `l2s_needed_preserved[04..10]` |
| pipeline δ without `homeCurrentCommand ~= empty1` | 6 × `l2s_needed_preserved[04..06]` |
| delete the tableau component `[00]` | 18 |
| drop the compassion `invariant` | `l2s_progress[01]`, `l2s_progress_eventually[01]` |
| drop `instantiate sf_pick` | 1 (the compassion invariant itself) |
| `work_progress[01] := false` | 23 |
| `work_progress[09] := false` | 22 |
| `work_helpful[07] := true` | `l2s_progress[07]` |

The first three rows are the point: they confirm that *preemption*, not merely having the
right components, is what removes the auxiliary lemma.

### 10.4 `german_3channels_fifo.ivy`

| mutation | failing checks |
|---|---|
| **arbitrary arbiter instead of `minimizing s.reqts(cl)`** | `l2s_progress[00]` — the starvation scenario, caught by the checker |
| `[00]` without the `reqts(N) <= reqts(_C)` bound | 2 × `l2s_needed_preserved[00]` |
| `[00]` demoted to lowest order | 7 × `l2s_needed_preserved[03..09]` |
| `ts_below_clock` removed | 2 × `l2s_needed_preserved[00]` |
| `work_progress[00] := false` | 22 |

---

## 11. Caveats and open questions

1. **Compassion is an assumption, not a theorem.** `german_3channels_original.ivy` and
   `_lex.ivy` are conditional results. If your home directory does not implement a fair
   arbiter, they say nothing. `_fifo.ivy` is the unconditional result for the FIFO variant.
2. **Client blocking is a modelling assumption.** `require ~s.waiting(cl)` is standard for
   German but it is an assumption about clients, not something the protocol enforces. A
   client that can pipeline requests is outside all three proofs.
3. **`finite type client`.** All three proofs rely on the client universe being finite.
   Unbounded clients would need timestamp-based rankings (`work_created(T) = T < clock`) as
   in the CAV'24 queue example.
4. **Unit-capacity channels.** This is the size-1 model. The unbounded-FIFO variant
   (`german_3_unbounded_channels.ivy`) has no liveness proof; it would need per-message
   timestamps and the `X <= clock` finiteness bound, and the stage decomposition would have
   to be redone over messages rather than over clients.
5. ~~**Mixed-sort components are untested.**~~ **Resolved** — see §13.1. Mixing sorts across
   components in one `ranking` call works, and so does a sorted `work_needed` with a nullary
   `work_progress`/`work_helpful`. Every component in the three German proofs is still
   `(N:client)`, but only because it was convenient, not because it was required.
6. **`l2s_progress` semantics across a long gap.** The check is a postcondition
   `old(φ) ∧ old(ψ) ∧ ¬waiting_for_progress → decreased`, and `waiting_for_progress` stays
   cleared once `r` has occurred since the freeze. The exact interaction with the
   `l2s_waiting`/`frozen`/`saved` phases was not fully reverse-engineered; the proofs were
   made to work by matching the shapes in `bakery.ivy` and `strongfair.ivy`. If a
   `l2s_progress` failure looks impossible, suspect this before suspecting your ranking.
7. **`~waiting(C)` is "served", not "served correctly".** Liveness only; the coherence
   safety invariants are the original ones and are unchanged.
8. **Not machine-checked: the claim that the property is false under weak fairness alone.**
   §4.1 is a hand argument. The ablation evidence (dropping compassion fails) shows the
   assumption is *load-bearing in this proof*, which is weaker than showing the property is
   false. Ivy has no LTL model checker to settle it; a small bounded-model-checking
   experiment on a 2- or 3-client instance would be the way to confirm it.

---

## 12. Cheat sheet

**Choosing the property shape**
- Goal `q`: a **state predicate**, and set `work_invar = ¬q` unless you have a reason not to (§6.5, §6.6).
- Progress `r`: an **event pulse**. Never the other way round.
- `forall X` at the very outside so `skolemizenp` lifts it to `_X`.

**Encoding fairness**
- Pulse the flag *before* the guard; make the body an `if`, never a `require` (§3.1).
- Add `invariant ~flag`.
- Environment actions that you do not want forced: keep `require`, add no flag.
- A `wf_*` flag as `work_progress` requires `work_helpful` to imply the rule's guard.

**Choosing a tactic**
- One justice condition, everything conserved → `ranking` with one component.
- Several justice conditions, everything conserved by everything → `l2s_auto5`.
- A ranking that must be allowed to *grow* while another is being worked on → `ranking`,
  lexicographic. Put the component that is active during the growth *higher*.

**`ranking`-specific**
- Two-digit suffixes (§6.3).
- Schedulers must imply their rules' guards (§6.2).
- Re-state any temporal hypothesis you need at arbitrary states as an `invariant` in the
  block (§6.8).

**Reading failures**

| check | premise | first thing to look at |
|---|---|---|
| `l2s_needed_preserved` | conserves δ | some action grows δ; use a union/monotone base, add a `cmd ~= empty1`-style conjunct, or promote the disturbing component above this one |
| `l2s_progress` / `l2s_progress_made` | reduces δ | ψ does not imply the rule's guard, or `work_progress` names the wrong rule |
| `l2s_progress_eventually` | ψ ⇒ ◇r | the fairness axiom is not instantiated at the right term (§6.7), or not re-stated as an `invariant` (§6.8) |
| `l2s_sched_stable` | ψ ∧ ¬r → ψ′ | another action falsifies ψ; promote the disturbing component above this one |
| `l2s_sched_exists` | φ → ⋁ψ | a state of the pipeline is uncovered; usually a missing safety invariant |
| `l2s_not_all_done` | work remains while waiting | the goal is a pulse, or `¬◇q` does not pin `work_invar` (§6.5) |

**Always finish with ablations.** Break each `work_progress`, each `work_helpful`, each
`instantiate`, and the component ordering, and confirm each one fails (§10).


---

## 13. Addendum: what the ABP proof added

After the German proofs, the same technique was applied to the alternating bit protocol
(`abp_ranking.ivy`), the POPL'18 / FMCAD'18 benchmark that ships here as `abp.ivy`
(unfinished — `tactic sorry`, and it does not even parse: `eventually_data_sent = true;`
in `after init` should be `:=`) and `abp_l2s.ivy` (complete, via the raw `l2s` tactic).

**Result.** One `ranking` call, eight lexicographic components, replacing `abp_l2s.ivy`'s
~50 hand-written monitor invariants over `$l2s_s`/`$l2s_w`/`l2s_a`/`l2s_d`, its witness
constant, and **all four temporal-prophecy formulas** `eventually globally (sender_bit = b1
& receiver_bit = b2)`. The case analysis on the bit combinations that the prophecy was
there to support is subsumed by the component ordering. `OK`, 910 checks, 4.5 s.

Four findings that did not come up in German:

### 13.1 Mixed-sort components work

`work_needed[04](J:index_t)`, `work_needed[06](M:data_msg_t)`, `work_needed[07](A:ack_msg_t)`
and four nullary components coexist in one `ranking` call. `work_progress`/`work_helpful`
may be nullary while `work_needed` is sorted — `ivy_ranking.py:343` computes
`wpargs = needed_args[len(helpful_args)-len(progress_args):]`, which degenerates to all of
`needed_args` when both are empty, giving the expected
`decreased = ∃x. old(δ(x)) ∧ ¬δ(x)`. This retires caveat §11.5.

### 13.2 A compound `work_progress` creates an unrelated tableau atom

`definition work_progress[06] = data_received | stale_data_dropped` fails both
`l2s_progress[06]` and `l2s_progress_eventually[06]`, even though each disjunct is
individually fine and `□◇data_received` is available. The tableau allocates an atom per
*syntactic formula* (§6.1), so `◇(data_received | stale_data_dropped)` is a fresh
proposition with no connection to `◇data_received`.

**Fix:** never build a compound progress condition. Introduce one ghost relation and pulse
it in every action that should count, then use that single symbol.

### 13.3 The tableau will not lift a pointwise implication to `□◇`

Having introduced `data_drained` (pulsed wherever `data_received` is, plus on a stale drop),
the natural move is to keep the benchmark's assumption and bridge:

```ivy
invariant (globally eventually data_received) -> (globally eventually data_drained)
```

**This is not provable**, even with `invariant data_received -> data_drained` stated
pointwise in the model *and* repeated inside the tactic block (both were tried). The local
tableau constraints give `□p → X□p` and `X◇p → ◇p`, but nothing that pushes a pointwise
implication through `◇`; the missing step needs the eventuality-discharge argument, which
lives in the fair-cycle assertion rather than in the invariant.

**Consequence for `abp_ranking.ivy`:** the channel fairness is stated on the drain signal,
`(globally eventually data_sent) -> (globally eventually data_drained)`. Because
`data_received -> data_drained` holds pointwise (checked), this is *implied by* the
benchmark's assumption, so the theorem is strictly stronger — but the implication is
justified on paper, not inside Ivy. The benchmark's own axioms are kept in the file as
`explicit` and never instantiated, so they are inert and the reader can see both.

### 13.4 Lossy channels break drain schedulers, and the fix is a ghost signal

A drain ranking ("messages still to be flushed from the head of the FIFO") needs
`ψ = ∃ stale message` so that the receive is guaranteed to remove one. But a `drop` can
remove the last stale message without any receive, falsifying ψ while `work_progress` has
not fired: `l2s_sched_stable[06] ... FAIL`. This is not a defect in the ranking — the drop
*is* progress — it is that Rule 10 records progress only through `work_progress`.

**Fix:** a ghost signal pulsed both on the receive and on a drop *that removes a stale
message*:

```ivy
before data_msg_drop {
    if data_msg.le(m,m) & ~(dbit(m) <-> sender_bit) {
        stale_data_dropped := true; stale_data_dropped := false;
        data_drained := true; data_drained := false;
    };
    call data_msg.drop(m);
}
```

Guarding the pulse matters: an unguarded `data_dropped` would fire on dropping a *fresh*
message too, and then `l2s_progress` would demand a reduction that did not happen.

### 13.5 The string-sorting trap bites twice

Two of the ABP ordering ablations came back `OK` and looked like the ordering was not
load-bearing. In fact the *ablations* were wrong: renaming `[04]` to `[055]` does not demote
it, because `'[055]' < '[05]'` — at the fourth character, `'5'` (0x35) precedes `']'`
(0x5D). Suffixes that genuinely sort later need a letter: `'[05a]' > '[05]'`. Redone
properly, both ablations fail as predicted (`l2s_needed_preserved[05]` and
`l2s_needed_preserved[06]`).

Moral: §6.3 applies to anything that manipulates component suffixes, including your own
experiments. Print `sorted(suffixes)` and read it before believing an ordering ablation.

### 13.6 ABP ablation table

| mutation | failing checks |
|---|---|
| `l2s_auto5` instead of `ranking` | 9 (`l2s_needed_are_frozen[06]`, `l2s_needed_when_start[04]`, …) |
| delivery `[04]` demoted below the round `[05]` | `l2s_needed_preserved[05]` |
| round `[05]` demoted below the data drain `[06]` | `l2s_needed_preserved[06]` |
| delivery `[04]` demoted below the ack drain `[07]` | `l2s_needed_preserved[05]` |
| data tableau components `[00]`,`[01]` deleted | 10, incl. `l2s_sched_exists` |
| `work_progress[04] := false` | 16 |
| delivery scheduler without the "no stale data" guard | `l2s_progress[04]` |
| drain signal not pulsed on a stale drop | `l2s_sched_stable[06]` |
| data channel fairness not instantiated | the fairness invariant itself |

Reachability probes on the ABP model (all violated, i.e. all reachable): a value is
delivered; the sender bit flips; phase B occurs; stale data messages occur; stale acks
occur; two data messages are in flight at once.


---

## 14. Addendum: eliminating temporal operators from the ABP ranking

`abp_ranking.ivy` is a lexicographic proof, but it is not *first-order*: sixteen temporal
operators appear inside its `ranking` block. `abp_ranking_first_order.ivy` removes all of
them. `OK`, 4.5 s.

### 14.1 Where the temporal operators came from

Every one of them traces back to the two **conditional** channel-fairness assumptions

```
(globally eventually data_sent) -> (globally eventually data_received)
```

An *unconditional* `globally eventually p` hypothesis needs no temporal operator in the
ranking at all: `instantiate` alone discharges `l2s_progress_eventually`, as
`german_3channels_fifo.ivy` demonstrates. A *conditional* one costs two things:

1. the antecedent `globally eventually data_sent` has to be case-split on the tableau
   (`strongfair.ivy` idiom), which is components `[00]`–`[03]` and puts
   `~(globally eventually …)` into their schedulers; and
2. the surviving components must carry `globally eventually data_sent` in `work_helpful` to
   reach the consequent, plus the axiom has to be restated as a temporal `invariant`
   inside the block (§6.8).

So: **temporal operators in a ranking are a symptom of conditional fairness, not of
liveness.** Make the assumption unconditional and they vanish. Exactly the same trade as
`german_3channels_lex.ivy` → `german_3channels_fifo.ivy`.

### 14.2 The instrumentation

Two changes, both in the model:

**(a) Fair-lossy channels — head protection.** A message may be lost only while some older
message is still in flight ahead of it:

```ivy
before data_msg_drop {
    if data_msg.le(m,m) & (exists X. data_msg.le(m,X) & X ~= m) {
        call data_msg.drop(m);
    }
}
```

**(b) The two receive actions become guarded commands** with turn flags pulsed *before* the
guard (§3.2), so `globally eventually recv_data_turn` is an honest statement about the
scheduler:

```ivy
before receiver_receive_data {
    recv_data_turn := true;
    recv_data_turn := false;
    if exists X. data_msg.le(X,X) { … receive the head … }
}
```

Note the original `data_received` could not serve as a weak-fairness flag: it is pulsed
*before* `data_msg.receive()`, whose `assume`s prune the trace when the channel is empty —
the vacuity trap of §3.1, inherited from the benchmark.

### 14.3 Head protection does double duty

It was introduced to make "the data channel is non-empty" stable (only a receive can empty
it now — a drop needs an older message to remain). It also, for free, makes **"a stale
message is present" stable**, which is the problem that §13.4 had to solve with a ghost
signal:

> In phase A the stale messages are exactly the FIFO's oldest ones (a safety invariant of
> the original model). So if exactly one stale message remains, it *is* the head, and the
> head cannot be dropped. The stale set can therefore only be emptied by a receive.

So `stale_data_dropped` / `data_drained` and the whole bridging problem of §13.3 disappear.
The findings of §13.2–13.4 remain valid for the un-instrumented model.

### 14.4 The price: two new components

Because the turn flag now pulses on an empty channel, a scheduler that is on while the
channel is empty would violate `l2s_progress` (nothing is received, nothing reduces). The
fix is to give "waiting for the next send" its own ranking — and the natural one is the
boolean *"the channel is empty"*, reduced by the send itself:

```ivy
definition work_needed[04]   = (sender_bit <-> receiver_bit) & ~(exists M. data_msg.le(M,M))
definition work_progress[04] = sender_scheduled
definition work_helpful[04]  = (sender_bit <-> receiver_bit) & ~(exists M. data_msg.le(M,M))
```

It must carry the phase conjunct: without it, the ranking would also grow when the data
channel empties during phase B, where nothing above it is scheduled.

### 14.5 Result

| | `abp_l2s.ivy` | `abp_ranking.ivy` | `abp_ranking_first_order.ivy` |
|---|---|---|---|
| tactic | `l2s` (manual) | `ranking` | `ranking` |
| components / invariants | ~50 invariants | 8 components | **6 components** |
| temporal prophecy | 4 formulas | none | none |
| temporal operators in the proof | many | 16 | **0** |
| channel fairness | conditional | conditional | **plain weak fairness** |
| model | benchmark | benchmark | benchmark + head protection |

The six components are: delivery `[00]`, the round `[01]`, drain stale data `[02]`, drain
stale acks `[03]`, wait-for-data-send `[04]`, wait-for-ack-send `[05]`.

**Caveat, same shape as `german_3channels_fifo.ivy`:** this is an *incomparable* theorem.
The fairness assumption is weaker (unconditional), but the model is stronger (the channel
protects its head). It is not implied by, and does not imply, the benchmark result.

### 14.6 Ablations and reachability

| mutation | failing checks |
|---|---|
| **head protection removed (unconstrained drops)** | `l2s_sched_stable[00]`,`[01]`,`[02]`,… |
| `l2s_auto5` instead of `ranking` | `l2s_needed_are_frozen[02]`,`l2s_progress_made[01]`,… |
| delivery `[00]` demoted below the round `[01]` | `l2s_needed_preserved[01]` |
| round `[01]` demoted below the data drain `[02]` | `l2s_needed_preserved[02]` |
| delivery `[00]` demoted below the ack drain `[03]` | `l2s_needed_preserved[01]`,`[03]` |
| delivery `[00]` demoted below wait-for-send `[04]` | `l2s_needed_preserved[01]`,`[03]` |
| `work_progress[00] := false` | `l2s_progress[00]`, … |
| delivery scheduler without "channel non-empty" | `l2s_progress[00]` |
| delivery scheduler without "no stale data" | `l2s_progress[00]` |
| wait-for-send components `[04]`,`[05]` deleted | `l2s_sched_exists` |

Reachability probes (all violated, i.e. all reachable) — note the first, which checks the
instrumentation did not quietly turn the channel into a reliable one:

**a message is actually lost**; a value is delivered; phase B occurs; stale data messages
occur; stale acks occur; an empty data channel in phase A occurs.
