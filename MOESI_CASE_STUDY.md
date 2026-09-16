# Case Study: Modelling MOESI in Ivy and Proving It Live

*A directory-based MOESI cache coherence protocol, its safety (the state
compatibility table), and two liveness theorems — "every memory access is
eventually served" — proved with McMillan's relational lexicographic rankings.*

Companion to `LIVENESS_GUIDE.md` (the method) and
`LIVENESS_CASE_STUDY_GERMAN.md` (the same exercise for the German protocol).
Read those first; this file records only what is new.

---

## 0. Artefacts

| File | What it proves | Rule | Components | Fairness assumed | `ivy_check` |
|---|---|---|---|---|---|
| `moesi.ivy` | safety: the MOESI compatibility table | — | — | — | OK, 289 checks, 2.2 s |
| `moesi_live.ivy` | `forall C. □(waiting(C) → ◇¬waiting(C))`, **FIFO arbiter** | Rule 10 (`ranking`) | 16 | weak fairness only | OK, 2867 checks, 8.8 s |
| `moesi_live_compassion.ivy` | same, **arbitrary arbiter** (MOESI as specified) | Rule 10 (`ranking`) | 17 | weak fairness + compassion for the arbiter | OK, 3011 checks, 8.4 s |

```bash
ivy_check moesi.ivy                 # or moesi_live.ivy / moesi_live_compassion.ivy
ivy_check debug=true trace=true <f> # first failing check + its CTI
```

Toolchain: `ivy_check` at `/home/ruijie/workplace/venv_ivy/bin/ivy_check`.

The two liveness files prove **incomparable** theorems: `moesi_live.ivy` makes
the weaker scheduler assumption but only about a home that arbitrates FIFO;
`moesi_live_compassion.ivy` covers the protocol as literally specified but has
to assume compassion. Neither implies the other. This is the same split as
`german_3channels_fifo.ivy` vs `german_3channels_lex.ivy`.

---

## 1. The protocol and how it is modelled

### 1.1 MOESI in one paragraph

Every cache line in every cache is in one of five states — **M**odified (sole
copy, dirty, writable), **O**wned (one of several copies, dirty, this cache
answers reads and owes the writeback), **E**xclusive (sole copy, clean,
writable), **S**hared (one of several copies, read-only), **I**nvalid. MOESI is
MESI plus the O state, and the point of O is *dirty sharing*: when a cache
holding M sees a read by another cache, MESI must write the line back to
memory (M → S); MOESI instead moves M → O, keeps the dirty data in the cache
and lets the owner answer future reads. E is the other inherited optimisation:
a read miss that finds *no* other copy is answered with E rather than S, so the
reader can later upgrade to M with no bus traffic at all.

### 1.2 The Ivy model

A directory-based MOESI (the AMD/HyperTransport shape, where the directory
sends *probes*), in the same three-channel skeleton as the German files so the
two are directly comparable:

```
channel1(C)   : client -> home    empty1 | reqshared | reqexclusive
channel2_4(C) : home   -> client  empty2_4 | invalidate | downgrade
                                  | grantshared | grantexclusive | grantmodified
channel3(C)   : client -> home    empty3 | invalidateAck | downgradeAck
```

All channels are unit-capacity, one set per client. The directory keeps
`homeSharerList`, `homeprobeList`, `homeexclusiveGranted`, `homeCurrentCommand`,
`homeCurrentclient`, and a witness `owner`. Serving one request is a pipeline:

```
pick  -->  probe everyone on the probe list  -->  collect the acks  -->  grant
```

with two probe kinds and three grant kinds:

| command | probe sent | to whom | grant |
|---|---|---|---|
| `reqexclusive` (write) | `invalidate` | every sharer | `grantmodified` → **M** |
| `reqshared` (read), line writable somewhere | `downgrade` | the owner | `grantshared` → **S** |
| `reqshared`, line clean-shared somewhere | — | — | `grantshared` → **S** |
| `reqshared`, no copy anywhere | — | — | `grantexclusive` → **E** |

The MOESI-defining transition lives in `clientdowngradesRule`:

```ivy
if s.cache(cl) = modified {
    s.cache(cl) := owned;          # dirty sharing: no writeback
} else if s.cache(cl) = exclusive {
    s.cache(cl) := shared;         # clean
}
```

and the E optimisation in `writeExclusiveRule` (`exclusive → modified`, silent,
no message, no directory update).

Because `homeexclusiveGranted → homeSharerList(C) → C = owner`, the downgrade
probe list is automatically the singleton `{owner}` — the same trick German uses
to get a "list" whose only member is the exclusive holder, so both probe kinds
can share one `homeprobeList` relation.

### 1.3 Differences from the German model, deliberately kept

Three modelling choices are inherited from `german_3channels_*.ivy` so that the
proofs can be compared line by line:

* **`homeprobeList := homeSharerList` at every pick.** The snapshot stays
  complete for the whole command because `homeSharerList` can only *grow* in
  the three grant rules, and all three end the command in the same step.
* **A write request invalidates the requester too** if it was a sharer (an
  S→M or O→M upgrade goes through I). Simpler than a real upgrade path and
  identical to German.
* **Clients block** (`require ~s.waiting(cl)`), so at most one access per cache
  is in flight. Without it `waiting` stops identifying a single request and the
  three-stage decomposition collapses.

---

## 2. Safety: the compatibility table

The headline property is Wikipedia's MOESI table — which pairs of states two
*different* caches may hold at the same time:

|  | M | O | E | S | I |
|---|---|---|---|---|---|
| **M** | — | — | — | — | ✓ |
| **O** | — | — | — | ✓ | ✓ |
| **E** | — | — | — | — | ✓ |
| **S** | — | ✓ | — | ✓ | ✓ |
| **I** | ✓ | ✓ | ✓ | ✓ | ✓ |

stated as four invariants:

```ivy
invariant [moesi_M_is_exclusive]           C1 ~= C2 & cache(C1) = modified  -> cache(C2) = invalid
invariant [moesi_E_is_exclusive]           C1 ~= C2 & cache(C1) = exclusive -> cache(C2) = invalid
invariant [moesi_O_compatible_with_S_only] C1 ~= C2 & cache(C1) = owned
                                               -> cache(C2) = shared | cache(C2) = invalid
invariant [moesi_O_is_unique]              cache(C1) = owned & cache(C2) = owned -> C1 = C2
```

They are inductive relative to twelve supporting directory-consistency
invariants (`moesi.ivy`, section "Supporting inductive invariants"). Eleven of
those are the German ones transposed. **One is genuinely new, and it is the
E → S downgrade that forces it:**

```ivy
invariant [shared_implies_no_writer]
    (cache(C) = shared | channel2_4(C) = grantshared)
        -> homeSharerList(C)
           & (~homeexclusiveGranted | channel3(C) = downgradeAck)
```

German's corresponding invariant has the clean `& ~homeexclusiveGranted`. In
MOESI it is false: between the cache's own E → S transition and the home
processing the resulting ack, the cache says "shared" while the directory still
says "writable". The window is real, not an artefact; the escape clause
`| channel3(C) = downgradeAck` names it exactly. `owned_not_writable` carries
the same clause for the M → O half. This was the **only** failing check on the
first run of the safety model, and the CTI named the transition directly:

```
s.cache(0) = exclusive, s.channel2_4(0) = downgrade, s.homeexclusiveGranted = true
call clientdowngradesRule   ->   s.cache(0) := shared
```

### 2.1 The protocol really does what MOESI says

Two kinds of evidence, both machine-produced.

**Bounded model checking.** Adding
`invariant ~(C1 ~= C2 & cache(C1) = owned & cache(C2) = shared)` with
`attribute method = bmc[14]` produces an 11-step counterexample — i.e. a
concrete run into MOESI dirty sharing:

```
reqexclusiveRule(1)      pickNewRequestRule(1)      reqsharedRule(0)
grantmodifiedRule        pickNewRequestRule(0)      receivemodifiedGrantRule(1)   # 1 is M
senddowngradeRule(1)     clientdowngradesRule(1)                                  # 1 is O, no writeback
receivedowngradeAckRule(1)   grantsharedRule        receivesharedGrantRule(0)     # 0 is S
```

**Violability probes.** Adding a deliberately false invariant and confirming
`ivy_check` reports it FAIL (if it *passes*, the state is unreachable and the
property is about nothing):

| probe | result |
|---|---|
| some cache in M / E / S / O | all violable |
| O and S held simultaneously (dirty sharing) | violable |
| two caches in S | violable |
| a `downgrade` probe in flight / a `downgradeAck` in flight | violable |
| the owner being invalidated by a write request | violable |
| a client queued while the home serves someone else (the starvation shape) | violable |
| a client actually waiting; two clients waiting at once | violable |

---

## 3. The liveness property

```ivy
explicit temporal property [live]
  forall C. globally (s.waiting(C) -> eventually ~s.waiting(C))
```

`waiting(C)` is a ghost bit raised exactly where C issues a request and lowered
exactly where C consumes the corresponding grant, so `~waiting(C)` is precisely
"the access completed". The goal is a **state predicate** and `work_invar` is
its negation, which is what the `l2s_not_all_done` and `l2s_invar` premises need
(guide §6.5/§6.6).

Fairness is encoded in the guarded-command discipline of the German case study
(§3 there): every rule pulses its `wf_*` flag *before* testing its guard and
the body is an `if`, never a `require`, so `globally eventually wf_x` is a
statement about the *scheduler* and cannot be vacuous. The two request rules
keep `require` and get no flag — they are environment actions and we never want
to force a cache to issue a request.

### 3.1 The three stages

```
stage 1   channel1(C) ~= empty1                              request queued
stage 2   homeCurrentCommand ~= empty1 & hcc = C             the home is serving C
stage 3   channel2_4(C) = grantshared | grantexclusive | grantmodified
```

`[waiting_stages]` says a waiting client is in one of them, `[stage1_excl]` and
`[stage2_excl]` make them disjoint. Stage 3 has **three** cases here where
German has two, because MOESI has three grant kinds.

---

## 4. The lexicographic ranking

`moesi_live.ivy`, sixteen components, one `ranking` call, no lemma, and — as in
`german_3channels_fifo.ivy` — no temporal operator anywhere in the proof.

| # | what it is | `work_needed` (δ) | `work_helpful` (ψ) | `work_progress` (r) |
|---|---|---|---|---|
| 00 | stage 1, FIFO | `channel1(N) ~= empty1 & reqts(N) <= reqts(_C)` | `cmd = empty1 & channel1(_C) ~= empty1` | `wf_pick` |
| 01 | stage 3 | `waiting(_C)` | `N = _C & channel2_4(_C) = grantshared` | `wf_recvshared(N)` |
| 02 | stage 3 | `waiting(_C)` | `N = _C & channel2_4(_C) = grantexclusive` | `wf_recvexcl(N)` |
| 03 | stage 3 | `waiting(_C)` | `N = _C & channel2_4(_C) = grantmodified` | `wf_recvmod(N)` |
| 04 | invalidate pipeline | `homeSharerList(N) & cmd ~= empty1` | `channel3(N) = invalidateAck` | `wf_recvinvack(N)` |
| 05 | " | `… & channel3(N) ~= invalidateAck` | `channel2_4(N) = invalidate` | `wf_clientinv(N)` |
| 06 | " | `… & channel2_4(N) ~= invalidate` | guard of `sendinvalidateRule` | `wf_sendinv(N)` |
| 07 | **downgrade pipeline** | `homeexclusiveGranted & cmd = reqshared` | `channel3(N) = downgradeAck` | `wf_recvdownack(N)` |
| 08 | " | `… & channel3(N) ~= downgradeAck` | `channel2_4(N) = downgrade` | `wf_clientdown(N)` |
| 09 | " | `… & channel2_4(N) ~= downgrade` | guard of `senddowngradeRule` | `wf_senddown(N)` |
| 10 | drain a stale shared grant | `channel2_4(N) = grantshared & PROBE` | same | `wf_recvshared(N)` |
| 11 | drain a stale exclusive grant | `channel2_4(N) = grantexclusive & PROBE` | same | `wf_recvexcl(N)` |
| 12 | drain a stale modified grant | `channel2_4(N) = grantmodified & PROBE` | same | `wf_recvmod(N)` |
| 13 | issue the grant | `cmd ~= empty1` | guard of `grantsharedRule` | `wf_grantshared` |
| 14 | " | `cmd ~= empty1` | guard of `grantexclusiveRule` | `wf_grantexcl` |
| 15 | " | `cmd ~= empty1` | guard of `grantmodifiedRule` | `wf_grantmod` |

`PROBE` = `cmd = reqexclusive | (cmd = reqshared & homeexclusiveGranted)`, "the
home is in a probing phase".

Three things to notice.

**MOESI has two probe pipelines where German has one.** [04]–[06] is German's
invalidation chain. [07]–[09] is its MOESI twin for the *downgrade* path, and it
is structurally identical but ranks on a different quantity: not "N is still a
sharer" but "write permission is still outstanding for this read command". Note
δ[07]–δ[09] do not use `N` in their leading conjuncts at all — a ranking that is
either the whole client set or empty, the `german [08]/[09]` idiom. A downgrade
does **not** remove anyone from the sharer list (that is the whole point of O),
so the invalidation ranking cannot drive it.

**Three grant kinds mean three drains.** A client that has not yet consumed its
own grant occupies `channel2_4`, which blocks the probe the home needs to send
it, so draining a stale grant is a genuine pipeline stage — and MOESI has three
kinds of stale grant.

**Every scheduler is literally the enabling guard of its rule.** `l2s_progress`
is *not* discounted by preemption (guide §6.2), so each component must reduce
its own ranking whenever its scheduler is on, preempted or not; a loose "this
stage is non-empty" scheduler that is true in states where the rule is disabled
fails immediately.

### 4.1 Why it must be lexicographic

While `_C` sits in stage 1 or stage 3, the home runs *whole commands for other
clients*: a grant grows δ[04] (it adds a sharer) and a pick grows δ[13] (it makes
the home busy). Rule 8 requires every ranking to be conserved by every action,
so under `l2s_auto5` the pipeline would have to be lifted into a separate lemma
— exactly what `german_3channels_original.ivy` does. Rule 10 lets a *preempted*
component grow. The load-bearing fact is

```
~pre([04]..[15])  /\  waiting(_C)   ==>   homeCurrentCommand ~= empty1
```

a first-order consequence of `[waiting_stages]`: if no stage-1 and no stage-3
scheduler is on and `_C` is waiting, then either the home is serving `_C`, or
`_C`'s request is queued and — since ψ[00] is off — the home is busy. A busy
home cannot pick, so nothing grows the pipeline in the non-preempted region.
That is why every pipeline ranking carries a "the home is busy" conjunct.

### 4.2 Exactly one cut in the order is load-bearing — a new finding

The German case study reports that demoting stage 1 or stage 3 breaks the proof,
and leaves it there. Permuting the MOESI hierarchy systematically shows the
constraint is *only* the cut between the two blocks:

| permutation | result |
|---|---|
| **entire pipeline [04]..[15] order reversed** | **OK** |
| stage 3 promoted above stage 1 (both still above the pipeline) | OK |
| grant-issuing components [13]–[15] promoted to the top of the pipeline region | OK |
| downgrade pipeline [07]–[09] swapped below the drains [10]–[12] | OK |
| stage-1 component [00] demoted to lowest | 12 × `l2s_needed_preserved[04..15]` |
| all three stage-3 components demoted to lowest | 12 × `l2s_needed_preserved[04..15]` |
| **only** stage-3 component [03] demoted to lowest | 10 × `l2s_needed_preserved` |

So the hierarchy is really two levels, not sixteen: `{stage 1, stage 3}` above
`{the whole stage-2 pipeline}`, with the internal order of each block free.
Every component is still individually required — deleting any one of the twelve
pipeline components fails `l2s_sched_exists` (§6) — but their *relative* order
is not. The sixteen-deep hierarchy in the file is a presentation choice; the
theorem needs a two-deep one.

(This was worth checking because a plausible-looking argument said otherwise:
`receivedowngradeAckRule` falsifies `PROBE`, which is a conjunct of ψ[10]–ψ[12],
so [07] "must" preempt [10] for `l2s_sched_stable[10]` to hold. Swapping them
verifies anyway — Z3 finds another route, presumably because a pending
`downgradeAck` and a grant in `channel2_4` for the same client are excluded by
`[no_overlap]`. Predicted ordering constraints are worth testing, not asserting.)

---

## 5. Two arbiters, two theorems

### 5.1 `moesi_live.ivy` — FIFO arbiter, weak fairness only

Requests are timestamped (`instance ts : unbounded_sequence`, `clock`,
`reqts(C)`) and `pickNewRequestRule` is unparameterized and serves the oldest:

```ivy
action pickNewRequestRule = {
    wf_pick := true; wf_pick := false;
    if s.homeCurrentCommand = empty1 {
        if some cl:client. s.channel1(cl) ~= empty1 minimizing s.reqts(cl) { ... }
    }
}
```

Its guard — "the home is idle and somebody is queued" — is then stable, so
`globally eventually wf_pick` suffices. Component [00] is the CAV'24 "pending
timestamps ≤ mine" ranking carried over *clients* rather than timestamps, so
`work_created = true` stays valid (finite type) and every component in the file
has the same sort. The one supporting invariant is `[ts_below_clock]
reqts(C) < clock`: a newly issued request is younger than `_C`'s and so can
never join δ[00].

### 5.2 `moesi_live_compassion.ivy` — MOESI as specified

`pickNewRequestRule(cl)` picks an arbitrary queued client. Under weak fairness
the scheduler must offer `_C`'s pick a turn infinitely often but may offer every
one of those turns while the home is busy, so `_C` starves. The assumption is
compassion, and only for the arbiter:

```ivy
explicit temporal axiom [sf_pick]
  forall C. (globally eventually (homeCurrentCommand = empty1 & channel1(C) ~= empty1))
            -> (globally eventually f_pick(C))
```

Stage 1 then splits into the three tableau cases of `strongfair.ivy`: E
infinitely often (→ [01], compassion delivers the pick), E finitely often but
not finished (→ [00], the tableau bit is itself the ranking), and E never again
(→ the home is never idle again, so the pipeline is required and drives it to a
grant, which makes it idle — contradiction). The compassion axiom also has to
be re-stated as an `invariant` inside the ranking block, because
`instantiate sf_pick` only pins it at time 0 while `l2s_progress_eventually[01]`
is checked at every state (guide §6.8).

Everything below stage 1 is identical to `moesi_live.ivy` with the components
shifted by one. The file is *generated* from it by
`gen_moesi_compassion.py` (every edit is a `rep(old, new)` that asserts its
pattern is present), so the two models cannot silently drift apart:

```bash
python3 gen_moesi_compassion.py && ivy_check moesi_live_compassion.ivy
```

---

## 6. Non-vacuity: every ablation, actually run

A liveness proof that still passes with a broken parameter proves nothing.

### 6.1 `moesi_live.ivy`

| mutation | failing checks |
|---|---|
| **arbitrary arbiter instead of `minimizing s.reqts(cl)`** | `l2s_progress[00]` — the starvation scenario, caught by the checker |
| **`l2s_auto5` (Rule 8) instead of `ranking` (Rule 10)** | 24 × `l2s_progress_made[04..15]`, `l2s_work_preserved[04..15]` |
| stage-1 component [00] demoted to lowest | 12 × `l2s_needed_preserved[04..15]` |
| all stage-3 components demoted to lowest | 12 × `l2s_needed_preserved[04..15]` |
| `[ts_below_clock]` removed | 2 × `l2s_needed_preserved[00]` |
| δ[00] without the `reqts(N) <= reqts(_C)` bound | 2 × `l2s_needed_preserved[00]` |
| `work_progress[00] := false` | 34 |
| `work_progress[07] := false` (downgrade ack) | 33 |
| `work_progress[15] := false` (grant modified) | 32 |
| `work_helpful[09] := true` (send downgrade) | `l2s_progress[09]` |
| `work_helpful[10] := true` (stale-grant drain) | `l2s_progress[10]` |
| `work_helpful[13]` weakened to `cmd = reqshared` | `l2s_progress[13]`, `l2s_sched_stable[13]` |
| drains ranked on "home busy" instead of `PROBE` | `l2s_sched_stable[10]` |
| **delete any single component [00]..[15]** | 16–29 checks; the twelve pipeline components all fail `l2s_sched_exists`, the four stage-1/stage-3 components additionally fail `l2s_needed_preserved` for most of the pipeline |
| `[waiting_stages]` removed | 31 |
| `[stage1_excl]` removed | 4 (`stage2_excl`, `waiting_stages` stop being inductive) |
| `[stage2_excl]` removed | 19 |
| `[inv_in_flight]` removed | 17 × `l2s_sched_exists` |
| `[down_in_flight]` removed | 17 × `l2s_sched_exists` |
| `[no_overlap]` removed | 12, including four ordinary safety invariants |

`[inv_in_flight]` / `[down_in_flight]` are the MOESI pair of German's
`inv_in_flight`: during a probing phase, a sharer already taken off the probe
list has its probe (or the ack) in flight, so nobody is ever stuck outside the
pipeline. Without them "something is always scheduled" has a hole — one for each
probe kind.

### 6.2 `moesi_live_compassion.ivy`

| mutation | failing checks |
|---|---|
| drop `instantiate sf_pick` | 1 (the compassion invariant itself) |
| drop the compassion `invariant` inside the block | 34, incl. `l2s_progress[01]`, `l2s_progress_eventually[01]` |
| **compassion replaced by weak fairness of the pick** (`wf_pick(_C)` for `f_pick(_C)`) | 34, incl. `l2s_progress[01]`, `l2s_progress_eventually[01]` |
| delete the tableau component [00] | 29 |
| delete the compassion component [01] | 29 |
| `l2s_auto5` instead of `ranking` | 24 |
| stage-1 components [00],[01] demoted to lowest | 12 × `l2s_needed_preserved[05..16]` |

---

## 7. What was new relative to the German case study

1. **A second probe pipeline.** The O state means a read request is served by
   *downgrading* rather than invalidating, and a downgrade removes nobody from
   the sharer list. It therefore needs its own three-stage ranking chain whose
   base quantity is "write permission is still outstanding", not "N is still a
   sharer". Nothing in the German proof generalises to it automatically.
2. **A safety invariant with a real exception window.** `shared_implies_no_writer`
   cannot be stated cleanly because E → S makes the cache and the directory
   disagree until the ack lands. German has no such window, because it has no
   downgrade.
3. **Three grant kinds propagate everywhere**: three stage-3 components, three
   stale-grant drains, three grant-issuing components, three disjuncts in
   `[waiting_stages]`.
4. **The lexicographic order is two-level, not n-level** (§4.2). Measured, not
   assumed.
5. **The whole thing verified on the first `ivy_check` run** — 2867 checks, no
   CTI debugging — once the ranking was designed on paper by the guide's recipe
   and the German template. The one iteration needed anywhere in this exercise
   was the single safety invariant in §2. That is the method working as
   advertised: the hard part is the ranking design, and the tool is a decision
   procedure that either confirms it or hands you a counterexample.

---

## 8. Caveats

1. **Compassion is an assumption, not a theorem.** `moesi_live_compassion.ivy`
   is a conditional result. `moesi_live.ivy` is unconditional but only for a
   FIFO home.
2. **Not machine-checked: the claim that the arbitrary-arbiter property is
   false under weak fairness alone.** The argument in §5.2 is by hand. The
   ablation evidence (an arbitrary arbiter breaks `l2s_progress[00]`; weak
   fairness of the pick breaks `l2s_progress[01]`) shows the assumption is
   load-bearing *in these proofs*, which is weaker than showing the property
   fails. Ivy has no LTL model checker to settle it.
3. **Client blocking is a modelling assumption** (`require ~s.waiting(cl)`), not
   something the protocol enforces. A cache that pipelines accesses is outside
   these proofs.
4. **`finite type client`.** Unbounded caches would need timestamp-based
   rankings with `work_created(T) = T < clock`.
5. **Unit-capacity channels.** The unbounded-FIFO variant would need per-message
   timestamps and a stage decomposition over messages rather than clients.
6. **No data values, hence no writeback and no silent eviction.** The model is
   about coherence *permissions*, so O's writeback duty and the M → E / O → S
   writeback transitions are unobservable and omitted, as is silent eviction of
   a clean line. Adding a `value` sort carried in the grant messages would let
   one state the stronger property "every valid copy holds the current value",
   with the O state as the unique authority when memory is stale. That is the
   natural next extension and it is not done here.
7. **`~waiting(C)` is "served", not "served correctly".** Liveness only; the
   coherence guarantees are the §2 invariants.
