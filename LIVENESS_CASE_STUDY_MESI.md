# Case Study: Modelling the MESI Cache Coherence Protocol in Ivy and Proving It Live

*A complete record of the formalisation of MESI as a first-order transition system, the
proof of its coherence (safety) theorem, and two proofs of "every memory access is
eventually served" (liveness) under two different, incomparable fairness assumptions.*

Companion to `LIVENESS_GUIDE.md` (which explains the relational-ranking method) and to
`LIVENESS_CASE_STUDY_GERMAN.md` (which records the same exercise for the German
protocol). This file records what happened when the method met MESI, which is a
*snooping* protocol rather than a directory protocol, and what that changes.

---

## 0. Summary of artefacts

| File | Theorem | Rule | Components | Fairness assumed | `ivy_check` |
|---|---|---|---|---|---|
| `mesi.ivy` | coherence: `swmr` + `data_coh` | — (safety) | — | — | OK, 416 checks, 3.9 s |
| `mesi_live.ivy` | coherence **and** `live` | Rule 10 (`ranking`) | 12 | weak fairness only | OK, 2032 checks, 7.0 s |
| `mesi_live_compassion.ivy` | coherence **and** `live` | Rule 10 (`ranking`) | 13 | weak + **compassion for the arbiter** | OK, 2158 checks, 6.8 s |

```bash
ivy_check mesi.ivy                         # or mesi_live[_compassion].ivy
ivy_check debug=true trace=true <file>     # first failing check + its CTI
```

The two liveness files prove the same property about **different models under different
assumptions**, and neither result implies the other:

* `mesi_live.ivy` pays for liveness **in the model**: the bus arbiter is FIFO
  (timestamped requests, oldest served first), and then plain weak fairness for every
  rule suffices. The proof contains no temporal operator at all.
* `mesi_live_compassion.ivy` pays **in the assumption**: the arbiter picks an arbitrary
  queued client, as MESI is usually specified, and compassion (strong fairness) is
  assumed for it alone.

Both liveness files also carry the coherence invariants, so each is a self-contained
"this protocol is coherent and it makes progress" artifact.

**Toolchain.** `ivy_check` at `/home/ruijie/workplace/venv_ivy/bin/ivy_check`; the
installed `ivy/ivy_l2s.py` and `ivy/ivy_ranking.py` match the reading copy in
`~/workplace/ivy/ivy/`.

---

## 1. Understanding MESI, and turning it into a transition system

### 1.1 The protocol

Every cache line in every cache is in one of four states:

| | meaning |
|---|---|
| **M** modified | dirty, and this is the **only** copy in the system |
| **E** exclusive | clean, and this is the **only** copy in the system |
| **S** shared | clean, other caches may hold the line too |
| **I** invalid | no copy |

Processor side:

| | action |
|---|---|
| PrRd on I | issue **BusRd**; land in **S** if somebody else had a copy, in **E** if nobody did |
| PrRd on S/E/M | hit — no bus transaction, no state change |
| PrWr on I | issue **BusRdX**; land in M, everybody else → I |
| PrWr on S | issue **BusUpgr**; land in M, everybody else → I |
| PrWr on E | **silent** upgrade E → M, no bus transaction whatsoever |
| PrWr on M | hit — no bus transaction, no state change |

Snoop side:

| snooped | M | E | S | I |
|---|---|---|---|---|
| BusRd | Flush, → S | → S | → S | → I |
| BusRdX | Flush, → I | → I | → I | → I |

The two rows that make this MESI rather than MSI are "land in **E** if nobody else had a
copy" and "**silent** E → M". Both are modelled, and both are shown reachable (§2.3).

### 1.2 The five modelling decisions

**1. A split-transaction bus.** A textbook snooping bus performs a transaction
atomically. Modelled that way, MESI has no interesting concurrency left and its
liveness proof degenerates into "assume the bus is fairly arbitrated". So the bus
controller is a separate process and a transaction is a *pipeline*:

```
arbitrate -> send a snoop to every other cache -> each cache processes its snoop
          and answers -> the controller collects the answers -> the controller
          grants the line to the requester
```

Each leg travels in its own unit-capacity channel, as in the German model:

```
chan_req(C)   : client     -> controller   busrd | busrdx
chan_snoop(C) : controller -> client       snoops AND grants
chan_resp(C)  : client     -> controller   snoop responses
```

**Snoops and grants share one channel**, as they do on a real bus. This is not a
detail: it is what serialises the protocol, and the whole safety argument rests on it
(§2.2). It also creates a genuine extra pipeline stage in the liveness proof (§6).

**2. No directory.** This is a *snooping* protocol, so the controller keeps no sharer
list. It broadcasts to every cache except the requester and learns who holds a copy
from the responses. The variable `ctl_shared` is the MESI **shared line**: the OR of
the snoop responses, and the thing that decides between granting E and granting S.

This is the sharpest structural difference from German, and it is a simplification:
German's home has persistent `homeSharerList`/`homeinvalidateList` state that must be
reasoned about across transactions, whereas here the snoop set is snapshotted once per
transaction (`snoop_todo`, `snoop_await`) and only ever shrinks.

**3. BusRdX and BusUpgr are the same message.** They differ only in whether the
requester needs the data transferred; the coherence state machine cannot tell them
apart, and this model has no data on the bus. `pr_write_miss` (from I) and
`pr_write_upgrade` (from S) therefore both put `busrdx` in the request channel.

**4. Clients block.** A ghost bit `waiting(C)` is raised when C issues a request and
lowered exactly when C consumes the grant; the request rules `require ~waiting(cl)`.
Without this a client could pipeline requests, `waiting` would stop identifying a single
request, and the three-stage decomposition of §3 would collapse. This is the standard
modelling assumption, the same one German makes.

**5. Data is modelled in `mesi.ivy`, dropped in the liveness files.** `mesi.ivy` carries
`cdata(C)` and `mem` so that the safety theorem can include real data coherence. The
liveness files drop them: data never appears in any guard, so deleting it is a sound
abstraction for a progress property.

### 1.3 The rules

Nine fair rules (the protocol) and six environment actions (the processors):

| rule | fairness flag | what it does |
|---|---|---|
| `arbitrate` | `wf_arb` | start a transaction; snapshot `snoop_todo`/`snoop_await` to "everyone but the requester" |
| `send_snoop(C)` | `wf_sendsnoop(C)` | put C's snoop in `chan_snoop(C)` |
| `snoop_respond(C)` | `wf_snoopresp(C)` | C applies the MESI snoop row and answers |
| `recv_resp(C)` | `wf_recvresp(C)` | controller collects C's answer; `ackhadcopy` asserts the shared line |
| `complete_rd` | `wf_complrd` | all answered: grant **E** if `~ctl_shared`, else **S** |
| `complete_rdx` | `wf_complrdx` | all answered: grant **M** |
| `recv_grant_shared/exclusive/modified(C)` | `wf_recvgs/ge/gm(C)` | C installs the line and stops waiting |
| `pr_read_miss`, `pr_write_miss`, `pr_write_upgrade` | *(none)* | issue a request |
| `pr_write_exclusive` | *(none)* | the silent E → M upgrade |
| `pr_write_modified`, `evict` | *(none)* | local write; drop a line (writing back if dirty) |

The processor rules deliberately get no fairness: we never want to force a processor to
issue a request or to evict.

---

## 2. The safety theorem

### 2.1 What is proved

```ivy
invariant [swmr]                       # single writer / multiple reader
    (s.cache(C1) = modified | s.cache(C1) = exclusive) & C1 ~= C2
    -> s.cache(C2) = invalid

invariant [data_coh]                   # every clean valid copy agrees with memory
    (s.cache(C) = shared | s.cache(C) = exclusive) -> s.cdata(C) = s.mem
```

Together these are exactly "the caches are coherent": an M or E copy is the only copy in
the system, and a copy that is not dirty holds the current value. A dirty copy is
allowed to differ — that is what "dirty" means — and it is flushed back before anybody
else can observe the line. `at_most_one_modified` and `modified_excludes_shared` are
recorded as corollaries.

`mesi.ivy` verified **on the first attempt**, all 416 checks.

### 2.2 The serialisation argument, and why unit-capacity channels are load bearing

The one genuinely subtle part of MESI safety in this model is the window between "the
controller decides to grant E" and "the requester installs the line". During that window
the bus is already idle (`complete_rd` sets `ctl_cmd := noreq` in the same step it posts
the grant), so a *new* transaction can start. If that new transaction could finish, a
second cache could be granted E while the first grant is still in flight, and `swmr`
would be violated.

It cannot finish, and the reason is the shared channel. The new transaction snoops
every client except its own requester, so it sets `snoop_todo(C)` for the client holding
the undelivered grant; but `chan_snoop(C)` is occupied by that grant, so `send_snoop(C)`
is blocked, `snoop_await(C)` stays true, and the completion guard
`forall I. ~snoop_await(I)` can never hold. The grant must be drained first.

This is captured by two invariants, and the ablation table (§9.3) confirms both are
load bearing for `swmr`:

```ivy
invariant [grant_blocks]          # a client holding an undelivered grant is awaited
    (chan_snoop(C) = grant*) & ctl_cmd ~= noreq -> snoop_await(C)

invariant [one_grant]             # hence at most one grant is in flight at a time
    (chan_snoop(C1) = grant*) & (chan_snoop(C2) = grant*) -> C1 = C2
```

The same mechanism reappears in the liveness proof as components [07]–[09], the "stale
grant drain" stages: a client sitting on an unconsumed grant is *blocking the pipeline*,
so draining it is real work that has to be ranked.

### 2.3 Non-vacuity: the interesting states are reachable

Every probe below was run by adding a deliberately false invariant and confirming it is
*violated* (i.e. the state is reachable). If one of these had held, the model would have
been proving something about nothing.

| probe | |
|---|---|
| a cache reaches E / M / S | reachable |
| two caches in S simultaneously | reachable |
| a BusRd is answered with **E** (nobody else had a copy) | reachable |
| the **silent E → M upgrade** actually fires (ghost-instrumented) | reachable |
| the shared line gets asserted | reachable |
| a snooprd / snooprdx is in flight | reachable |
| a dirty cache differs from memory | reachable |
| a client is queued while the bus serves another (the starvation configuration) | reachable |
| **a stale grant blocks a snoop** (the §2.2 window) | reachable |
| two clients queued at once, with distinct timestamps | reachable |

---

## 3. Formalising "every memory access is eventually served"

```ivy
explicit temporal property [live]
  forall C. globally (s.waiting(C) -> eventually ~s.waiting(C))
```

`waiting(C)` is raised exactly where a request is issued and lowered exactly where the
corresponding grant is consumed, so `~waiting(C)` is precisely "the access completed".
This is the same formulation as in the German case study, and for the same reasons
recorded there: the obvious alternatives are either vacuous for upgrades, or stop at
"the controller replied" rather than "the cache was served".

The goal is a **state predicate** and `work_invar = waiting(_C)` is its negation-complement,
which is what the `l2s_not_all_done` machinery needs (guide §6.5).

Note what the property does *not* cover: PrRd hits, PrWr on M, and the silent E → M
upgrade never raise `waiting`, because they complete within the single atomic step that
issues them. They are served trivially, and there is nothing to prove about them.

**The three stages.** Everything rests on this decomposition:

```
stage 1   chan_req(C) ~= noreq                    the request is queued at the controller
stage 2   ctl_cmd ~= noreq & ctl_client = C       C's transaction is on the bus
stage 3   chan_snoop(C) = grant*                  C's grant is in flight
```

captured by

```ivy
invariant [waiting_stages]
    s.waiting(C) <-> (s.chan_req(C) ~= noreq
                      | (s.ctl_cmd ~= noreq & s.ctl_client = C)
                      | s.chan_snoop(C) = grantshared
                      | s.chan_snoop(C) = grantexclusive
                      | s.chan_snoop(C) = grantmodified)
```

plus `stage1_excl` making stage 1 disjoint from the others. `waiting_stages` is what
discharges the "something is always scheduled" premise (S4 / `l2s_sched_exists`), and
dropping it breaks 26 checks (§9.3).

---

## 4. Fairness encoding

Every fair rule is a **guarded command** with the flag pulsed *before* the guard:

```ivy
action send_snoop(cl:client) = {
    wf_sendsnoop(cl) := true;
    wf_sendsnoop(cl) := false;
    if <guard> { <body> }
}
invariant ~wf_sendsnoop(C)
```

This is the discipline established in the German case study §3, and it is the only
honest one. If the flag were pulsed *after* a `require`, then in an exported action the
`require` would prune every trace in which the flag pulses while the guard is false, and
`globally eventually wf_x` would silently mean "rule x successfully executes infinitely
often" rather than "the scheduler offers rule x a turn infinitely often" — strictly
stronger than strong fairness, and outright vacuous on executions where the guard never
holds. `ivy_check` reports `OK` either way and warns about nothing.

With the discipline in place, a turn offered to a disabled rule is a stutter step and
every `wfa_*` axiom is a satisfiable statement about the scheduler.

Two consequences used throughout:

* The processor rules keep `require` and get **no** flag. A `require` with no fairness
  flag is harmless.
* A weak-fairness flag pulses even when its rule no-ops, so it is not usable as a
  progress condition on its own: **every `work_helpful` must imply its rule's enabling
  guard**, so that when the flag pulses the body actually runs. In both proofs every
  scheduler is literally the guard of its rule. (The second reason for this is that
  `l2s_progress` is not discounted by preemption — guide §6.2.)

---

## 5. The arbiter is the entire difficulty

Once the model is right, every rule of MESI has a guard that, once true, stays true
until that rule itself fires — **except one**. The stability audit:

| rule | guard stable once enabled? | why |
|---|---|---|
| `send_snoop(C)` | yes | `snoop_todo(C)` is cleared only here; `chan_snoop(C)` can only be filled by a grant, and `grant_blocks` shows that is blocked |
| `snoop_respond(C)` | yes | only this rule clears a snoop from `chan_snoop(C)` |
| `recv_resp(C)` | yes | only this rule drains `chan_resp(C)`; completion is blocked while `snoop_await(C)` |
| `recv_grant_*(C)` | yes | only these clear a grant from `chan_snoop(C)` |
| `complete_rd` / `complete_rdx` | yes | `snoop_await` is set only by `arbitrate`, which needs an idle bus |
| `arbitrate(cl)` (arbitrary pick) | **no** | another client's pick falsifies "the bus is idle" |

That single row is the whole problem, and it is the same row as in German. Note the
asymmetry that the FIFO variant exploits: the instability comes from the rule being
*parameterized by the client*. The guard of an **unparameterized** pick — "the bus is
idle and somebody is queued" — is stable, because only a pick can falsify it.

### 5.1 Why weak fairness alone is not enough, with the counterexample

With an arbitrary arbiter the property is **false** under weak fairness. The argument:
the scheduler must offer `arbitrate(_C)` a turn infinitely often, but it may offer every
one of those turns while the bus is busy. Other caches cycle request → service →
request forever; the bus is idle only in the instants between a grant and the next pick,
and the adversary simply never offers `_C` a turn in one of those instants.

This is usually left as a hand argument. Here the key step is machine-produced. Taking
`mesi_live_compassion.ivy`, replacing compassion with plain weak fairness for the
arbiter, and writing the best component one can (`δ = chan_req(_C) ~= noreq`,
`r = wf_arb(_C)`, `ψ =` the enabling guard of `arbitrate(_C)`) gives **exactly one**
failing check —

```
l2s_sched_stable[01] ... FAIL
```

— i.e. premise S2's stability clause, which is precisely the formal content of the
starvation argument. Its counterexample is the scenario itself:

```
_C = 0
s.chan_req(0) = busrd        <-- the tracked client's read request is queued
s.chan_req(1) = busrd        <-- and so is client 1's
s.ctl_cmd     = noreq        <-- the bus is idle: arbitrate(_C) IS enabled
  then: arbitrate(1) fires
        s.ctl_cmd   := busrd
        s.chan_req(1) := noreq
```

Client 1 is picked instead of client 0, the bus goes busy, and `_C`'s scheduler is
falsified without `_C` ever having been offered a turn.

**Stated precisely:** this is a counterexample to the proof rule's premise, exhibiting
the bypass step concretely. It is not by itself a full LTL refutation — to make the
property false you iterate that step forever, which needs an infinite fair trace in
which client 1 keeps re-requesting between the completion and the next turn offered to
client 0. Ivy has no LTL model checker to settle that mechanically. But the CTI is the
inductive step of the standard argument, which is more than the German case study was
able to produce for the corresponding claim.

---

## 6. Proof 1 — FIFO arbitration, weak fairness only (`mesi_live.ivy`)

**Model change.** Requests carry timestamps (`instance ts : unbounded_sequence`,
`clock`, `reqts(C)`), and the arbiter serves the oldest:

```ivy
action arbitrate = {
    wf_arb := true; wf_arb := false;
    if s.ctl_cmd = noreq {
        if some cl:client. s.chan_req(cl) ~= noreq minimizing s.reqts(cl) { ... }
    }
}
```

By the asymmetry noted in §5 its guard is now stable, so `globally eventually wf_arb`
suffices.

**Proof.** One `ranking` call, twelve components, **no temporal operator anywhere**:

| # | `work_needed` (δ) | `work_helpful` (ψ) | `work_progress` (r) |
|---|---|---|---|
| 00 | `chan_req(N) ~= noreq & reqts(N) <= reqts(_C)` | `ctl_cmd = noreq & chan_req(_C) ~= noreq` | `wf_arb` |
| 01 | `waiting(_C)` | `N = _C & chan_snoop(_C) = grantshared` | `wf_recvgs(N)` |
| 02 | `waiting(_C)` | `N = _C & chan_snoop(_C) = grantexclusive` | `wf_recvge(N)` |
| 03 | `waiting(_C)` | `N = _C & chan_snoop(_C) = grantmodified` | `wf_recvgm(N)` |
| 04 | `snoop_await(N) & ctl_cmd ~= noreq` | `ctl_cmd ~= noreq & chan_resp(N) ~= emptyu` | `wf_recvresp(N)` |
| 05 | `... & chan_resp(N) = emptyu` | `chan_snoop(N) = snoop* & chan_resp(N) = emptyu` | `wf_snoopresp(N)` |
| 06 | `... & chan_snoop(N) ~= snoop*` | `ctl_cmd ~= noreq & snoop_todo(N) & chan_snoop(N) = emptyd` | `wf_sendsnoop(N)` |
| 07 | `snoop_await(N) & ctl_cmd ~= noreq & chan_snoop(N) = grantshared` | same as δ | `wf_recvgs(N)` |
| 08 | likewise, `grantexclusive` | same as δ | `wf_recvge(N)` |
| 09 | likewise, `grantmodified` | same as δ | `wf_recvgm(N)` |
| 10 | `ctl_cmd ~= noreq` | guard of `complete_rd` | `wf_complrd` |
| 11 | `ctl_cmd ~= noreq` | guard of `complete_rdx` | `wf_complrdx` |

**[00]** is the CAV'24 "pending timestamps ≤ mine" ranking, carried over **clients**
rather than timestamps. Two payoffs, both inherited from the German FIFO file:
`work_created = true` stays valid (finite sort, no `T <= clock` bound needed), and every
component in the file has the same sort, avoiding the untested mixed-sort case. The
supporting invariant is `[ts_below_clock] s.reqts(C) < clock`, which is what makes the
ranking shrink: a newly issued request gets `reqts = clock > reqts(_C)` and can never
join the set.

**[01]–[03]** are stage 3. There are three of them rather than German's two because a
MESI grant comes in three flavours — S, E and M — each consumed by its own rule.

**[04]–[06]** are the snoop pipeline, each ranking on a superset of the stages still to
come, so the rule advancing a client one stage conserves the earlier rankings while
reducing its own:

```
snoop_todo(N)  --send_snoop-->     snoop in chan_snoop(N)
               --snoop_respond-->  answer in chan_resp(N)
               --recv_resp-->      ~snoop_await(N)
```

**[07]–[09]** are the MESI-specific stages: a client still holding an unconsumed grant
blocks the snoop the controller needs to send it (§2.2), so draining it is real work.
Deleting them breaks `l2s_sched_exists` (15 checks).

**Why it must be lexicographic.** The pipeline rankings [04]–[11] are grown wholesale by
`arbitrate`, which runs freely while `_C` sits in stage 1 or stage 3. Rule 10 permits
that because a *preempted* ranking may grow. The preemption is legitimate: `arbitrate`
needs an idle bus, and when the bus is idle a waiting `_C` is in stage 1 or stage 3 by
`waiting_stages`, so one of [00]–[03] is scheduled at exactly that moment. Working out
the non-preempted region gives

```
~pre([04]..[11])  /\  waiting(_C)   ==>   ctl_cmd ~= noreq
```

a purely first-order consequence of `waiting_stages`. The ablations in §9.2 confirm the
order is load bearing: demoting [00], or any stage-3 component, below the pipeline
breaks `l2s_needed_preserved[04..11]`, and switching to `l2s_auto5` breaks 16 checks.

---

## 7. Proof 2 — arbitrary arbitration under compassion (`mesi_live_compassion.ivy`)

**Model change.** `arbitrate(cl)` is parameterized and picks an arbitrary queued client.
`wf_arb(cl)` is pulsed unconditionally (a turn was offered); `f_pick(cl)` is pulsed
*inside* the guard (the rule actually fired) and is the "taken" half of

```ivy
explicit temporal axiom [sf_pick]
  forall C. (globally eventually (s.ctl_cmd = noreq & s.chan_req(C) ~= noreq))
            -> (globally eventually f_pick(C))
```

Abbreviate the antecedent `E(C)`. This does **not** assume the conclusion: `globally
eventually E(_C)` still has to be discharged, and that is the entire content of the
stage-1 argument — components [05]–[12] show the controller keeps finishing
transactions, so `_C`'s request keeps becoming pickable.

**The mechanical cost of compassion.** A compassion assumption is a *conditional*
fairness assumption, so its antecedent must be case-split on the symbolic tableau, as in
McMillan's `strongfair.ivy`. Stage 1 therefore needs two components instead of one:

| # | case | δ | ψ | r |
|---|---|---|---|---|
| 00 | `E` finitely often, last one not yet past | `eventually E` | `~(globally eventually E) & (eventually E)` | `~(eventually E)` |
| 01 | `E` infinitely often | `chan_req(_C) ~= noreq` | `(globally eventually E) & chan_req(_C) ~= noreq` | `f_pick(_C)` |

The third case, "`E` never again", leaves the bus permanently busy while `_C` is queued
and is handled by the pipeline components. Everything else shifts down by one: stage 3
is [02]–[04] and the transaction pipeline is [05]–[12].

Two pieces of Ivy-specific ceremony are unavoidable here, both documented in the German
case study and both confirmed by ablation:

* `instantiate sf_pick with C = _C;` — a temporal atom is created per *syntactic*
  formula, so `□◇f_pick(C)` with a bound `C` and `□◇f_pick(_C)` are different
  propositions. Instantiating without `with C = _C` fails.
* the axiom must be **re-stated as an `invariant` at the end of the ranking block**.
  `instantiate` makes it a premise of the temporal goal, which pins it at time 0, but
  `l2s_progress_eventually[01]` is a postcondition checked at every state. The lift is
  sound because `□◇p` is insensitive to finite prefixes, and inductive from the local
  tableau constraints. Dropping it breaks 30 checks.

---

## 8. The added safety invariants and where they came from

None were invented up front. The bookkeeping ones (§A of the files) were written while
hand-checking the "something is always scheduled" premise; the coherence ones were
harvested from the safety CTIs.

| invariant | what it excludes | needed for |
|---|---|---|
| `waiting_stages` | a waiting client in no stage | `l2s_sched_exists`, and conservation for every pipeline ranking |
| `stage1_excl` | a queued request while an older one of the same client is in service | disjointness of the stages |
| `snoop_in_flight` | a snooped client "stuck outside the pipeline" | `l2s_sched_exists` — without it S4 has a hole |
| `grant_blocks` | a transaction completing while an undelivered grant is outstanding | **`swmr`** (§2.2) |
| `one_grant` | two grants in flight at once | **`swmr`** |
| `resp_awaited`, `snoop_awaited`, `todo_sub_await`, `await_busy`, `await_not_req` | stale or mismatched channel contents | pipeline scheduler stability; the coherence invariants |
| `rd_nocopy`, `rd_downgraded`, `rdx_invalidated` | a client that has answered still holding a copy | `excl_grant_alone`, `shared_grant_clean` |
| `excl_grant_alone`, `shared_grant_clean` | a grant that would violate exclusivity on arrival | **`swmr`** |
| `ts_below_clock` | a new request joining ranking [00] | `l2s_needed_preserved[00]` |

`snoop_in_flight` is the MESI analogue of German's `inv_in_flight`:

```ivy
invariant [snoop_in_flight]
    s.snoop_await(C) & ~s.snoop_todo(C) ->
        s.chan_snoop(C) = snooprd | s.chan_snoop(C) = snooprdx
        | s.chan_resp(C) ~= emptyu
```

An awaited client whose snoop has already been sent has it either in the downward
channel or, having answered, in the upward channel. It is inductive because `arbitrate`
re-snapshots both sets together, `send_snoop` moves a client from `snoop_todo` into
`chan_snoop`, `snoop_respond` moves it on to `chan_resp`, and `recv_resp` clears
`snoop_await`. Dropping it breaks `l2s_sched_exists` in 15 places.

---

## 9. Non-vacuity: full ablation results

Every row below was produced by mutating a verifying file and re-running `ivy_check`.

### 9.1 `mesi_live.ivy` — parameters

| mutation | failing checks |
|---|---|
| `work_progress[i] := false`, each of i = 00…11 | 30–31 each, always including `l2s_progress[i]` and `l2s_progress_eventually[i]` |
| `work_helpful[i] := true`, each of i = 00,01,04,05,06,07,10,11 | `l2s_progress[i]` (1 check each) |
| drop `instantiate wfa_x`, each of the 9 | `l2s_progress[·]`, `l2s_progress_eventually[·]` for the components using it |
| delete component [i], each of i = 00…11 | 15–23 each |

The `work_helpful := true` rows are the decisive ones: they prove the schedulers are
essential rather than cosmetic, because a weak-fairness flag pulses even when its rule
no-ops.

### 9.2 `mesi_live.ivy` — structure

| mutation | failing checks |
|---|---|
| **arbitrary arbiter** (drop `minimizing s.reqts(cl)`) | `l2s_progress[00]` — the starvation scenario, caught by the checker |
| **`l2s_auto5` (Rule 8) instead of `ranking` (Rule 10)** | 16 × `l2s_progress_made[04..11]`, `l2s_work_preserved[04..11]` |
| **[00] demoted to lowest order** | 8 × `l2s_needed_preserved[04..11]` |
| **stage-3 [01] demoted below the pipeline** | 6 × `l2s_needed_preserved[·]` |
| [00] without the `reqts(N) <= reqts(_C)` bound | 3 × `l2s_needed_preserved[00]` |
| `ts_below_clock` removed | 3 × `l2s_needed_preserved[00]` |
| `[10]`/`[11]` δ := `true` | `l2s_progress[10]`, `l2s_progress[11]` |
| pipeline δ [04]–[09] without `ctl_cmd ~= noreq` | **still OK** — see below |

The middle three rows are the point: they confirm that *preemption*, not merely having
the right components, is what makes a single `ranking` call suffice with no auxiliary
lemma.

The last row is an honest negative result and is recorded as such in the file. In
German that conjunct was load bearing; here it is implied by `[await_busy]`
(`snoop_await(N) -> ctl_cmd ~= noreq`), so for [04]–[09] it is documentation rather than
logic. For [10]/[11], where it *is* the ranking, it is load bearing.

### 9.3 `mesi_live.ivy` — invariants

Each invariant was commented out and the file re-checked.

| invariant | consequence of dropping it |
|---|---|
| `waiting_stages` | LIVENESS: 8 × `l2s_needed_preserved`, `l2s_sched_exists` (26 checks) |
| `snoop_in_flight` | LIVENESS: `l2s_sched_exists` (15 checks) |
| `ts_below_clock` | LIVENESS: `l2s_needed_preserved[00]` |
| `resp_awaited` | LIVENESS: `l2s_progress[04]`, `l2s_progress[06]`, `l2s_sched_stable[04]`, + safety |
| `todo_sub_await` | LIVENESS: `l2s_progress[06]`, `l2s_sched_stable[06]`, + safety |
| `snoop_awaited` | LIVENESS: `l2s_progress[05]`, + safety |
| `grant_blocks`, `one_grant`, `excl_grant_alone`, `rd_nocopy` | SAFETY: `swmr` and its corollaries |
| `await_busy`, `await_not_req`, `snoop_matches_cmd`, `stage1_excl` | SAFETY: other invariants become non-inductive |
| `req_chan_free` | **nothing** — true, and it states the protocol clearly, but Z3 derives what it needs from the others |

### 9.4 `mesi_live_compassion.ivy`

| mutation | failing checks |
|---|---|
| drop `instantiate sf_pick with C = _C` | the in-block compassion invariant |
| `instantiate sf_pick` **without** `with C = _C` | same — the term-instantiation trap |
| drop the in-block compassion `invariant` | 30, incl. `l2s_progress[01]`, `l2s_progress_eventually[01]` |
| `work_progress[01] := false` (the pick signal) | 31 |
| `work_progress[00] := false` (the tableau bit) | 31 |
| delete the tableau component [00] | 23 |
| delete component [01] | 23 |
| `l2s_auto5` instead of `ranking` | 16 |
| **compassion replaced by weak fairness** | `l2s_sched_stable[01]` — see §5.1 |

---

## 10. What MESI taught that German did not

1. **A snooping protocol is easier to rank than a directory protocol, for a specific
   reason.** German's home carries `homeSharerList` across transactions, and *another
   client's grant grows it* while the tracked client is waiting. That is what forced the
   two-step proof with the `home_idle` lemma in `german_3channels_original.ivy`. Here
   the snoop set is snapshotted per transaction and only shrinks, so the pipeline
   rankings are grown by exactly one rule (`arbitrate`) — and that rule is precisely the
   one the higher components preempt. Both MESI proofs are therefore single `ranking`
   calls with no lemma, and both went through without a pipeline-conservation fight.

2. **Sharing one channel between snoops and grants pays for itself twice.** It is what
   makes safety work (§2.2) and it is what creates components [07]–[09]. A model with
   separate snoop and grant channels would need a different exclusivity argument.

3. **The MESI shared line is the one piece of genuinely new safety reasoning.** Granting
   E requires knowing that *every* other cache answered "no copy" and *stayed* without
   one; that is the chain `nocopy_means_invalid` → `rd_nocopy` → `excl_grant_alone` →
   `swmr`, and it has no analogue in German, which has no E state.

4. **Three grant flavours means three stage-3 components and three drain components.**
   The cost of the E state in the liveness proof is exactly six components rather than
   four; nothing structural changes.

5. **The "weak fairness is not enough" claim can be pinned to a single check.** §5.1.
   Reducing the argument to one failing premise with a two-client CTI is a better
   artifact than a paragraph of prose, and is worth doing for any protocol whose
   liveness rests on an arbitration assumption.

---

## 11. Caveats, stated plainly

1. **The two liveness theorems are incomparable.** `mesi_live.ivy` is about a home that
   implements FIFO arbitration. `mesi_live_compassion.ivy` is about an arbitrary
   arbiter but assumes compassion for it. MESI as literally specified, with an
   arbitrary arbiter and only weak fairness, is not starvation-free — §5.1.
2. **Compassion is an assumption, not a theorem.** If your bus arbiter does not
   implement some form of fair arbitration, `mesi_live_compassion.ivy` says nothing.
3. **Client blocking is a modelling assumption.** `require ~s.waiting(cl)` is standard,
   but it is an assumption about processors, not something the protocol enforces. A
   cache that pipelines requests is outside both proofs.
4. **`finite type client`.** Both proofs rely on the cache universe being finite.
   Unbounded caches would need timestamp-based rankings (`work_created(T) = T < clock`).
5. **Unit-capacity channels.** This is the size-1 model. An unbounded-FIFO variant would
   need per-message timestamps and the stage decomposition redone over messages rather
   than over clients.
6. **The liveness files drop the data.** Sound for a progress property (data appears in
   no guard), but it does mean `data_coh` is proved only in `mesi.ivy`, about the model
   with data. The two models are otherwise identical rule for rule.
7. **`~waiting(C)` is "served", not "served correctly".** Liveness only; correctness is
   `swmr` + `data_coh`, proved separately and carried in all three files.
8. **§5.1 is an argument, not a mechanical refutation.** The CTI is machine-produced and
   is the inductive step, but Ivy has no LTL model checker, so "the property is false
   under weak fairness alone" is not machine-checked end to end.
9. **Mixed-sort components are untested.** Every component in both proofs is
   `(N:client)`, including ones whose δ ignores `N` (e.g. `work_needed[10](N) =
   ctl_cmd ~= noreq`). [00] in `mesi_live.ivy` was deliberately phrased over clients
   rather than timestamps to avoid mixing sorts in one `ranking` call.
