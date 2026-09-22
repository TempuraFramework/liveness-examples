# Case Study: Proving Liveness of Lamport's Distributed Mutual Exclusion in Ivy

*A complete record of the verification of "every node waiting to enter its critical
section eventually enters it" for Lamport's DME algorithm: which of the two existing
encodings the proof was built on and why, the ranking, the fairness analysis, and the
three obstacles that turned out to be about decidability rather than about the protocol.*

Companion to `LIVENESS_GUIDE.md` and `LIVENESS_CASE_STUDY_GERMAN.md`.

---

## 0. Artefacts

| File | Contents | `ivy_check` |
|---|---|---|
| `lamport_mutex_live.ivy` | flat model, mutual exclusion, `[delivery]`, `[live]`, `[starvation_freedom]` | **OK**, 601 checks, 6.3 s |
| `lamport_mutex_man.ivy` | the safety encoding it was derived from (unchanged) | OK |
| `lamport_mutex_hist.ivy` | the other safety encoding (unchanged) | **fails**: "not in the fragment FAU" |

**Toolchain.** `ivy_check` at `/home/ruijie/workplace/venv_ivy/bin/ivy_check`.

```bash
ivy_check lamport_mutex_live.ivy
ivy_check debug=true trace=true lamport_mutex_live.ivy    # first failing check + CTI
```

Three temporal properties are proved, all under **weak fairness only**:

```ivy
explicit temporal property [delivery]
  forall S,D,K,T. globally (chan(S,D,K,T) -> eventually ~chan(S,D,K,T))

explicit temporal property [live]
  forall C,R. globally ((st(C) = waiting & req(C,C) = R)
                        -> eventually st(C) = critical)

explicit temporal property [starvation_freedom]
  forall C. globally (st(C) = waiting -> eventually st(C) = critical)
```

plus the safety property `[mutex]` (`st(X) = critical & st(Y) = critical -> X = Y`),
which is the one `lamport_mutex_man.ivy` proves.

---

## 1. Which encoding to build on, and why

The repository ships two safety encodings of the same algorithm. They differ in what a
message *is*.

### 1.1 `lamport_mutex_hist.ivy` — messages are whole local states

Every message is the sender's entire local state, a struct `(ts, req)`; on receipt the
receiver does `state(src) := incoming` and unicasts its own state back. There is no
message kind: request, reply and release are all "here is my state now". A ghost `hist`
relation records every state a node has ever been in.

Four reasons this is the wrong base for a liveness proof:

1. **It does not verify on this build.** `ivy_check lamport_mutex_hist.ivy` reports
   *"The verification condition is not in the fragment FAU."* — there is no working
   safety baseline to extend, and the first thing a liveness proof does is inherit the
   safety invariants.
2. **The receiver's view is not monotone.** The overlay's ordering `require`s are
   commented out, so the channel is unordered, and `state(src) := incoming` overwrites
   unconditionally. A stale message therefore moves the receiver's view of the sender
   *backwards*. Every ranking in a liveness proof has to be conserved by the actions
   that are not its reducer; a view that can regress makes the entry test non-monotone,
   and then even the scheduler-stability premise (`l2s_sched_stable`) is false — the
   node's guard can be switched off again by an old message. Repairing this means adding
   a "highest timestamp seen" filter, i.e. rebuilding the ordering the other file already
   has.
3. **The stage structure is erased.** The whole ranking argument below is a
   decomposition into "my request reaches you" / "your reply reaches me" / "your release
   reaches me". With one undifferentiated message kind those three obligations are not
   separable, and in particular the `lastrr` bound of ranking `[03]` — "the channel
   prefix a node still has to consume before it can move" — has nothing to be defined
   from.
4. **`hist` is a safety device.** It records historical states so that the mutual
   exclusion invariant can refer to them. It contributes nothing to a ranking; the
   liveness argument needs *current* state, not history.

### 1.2 `lamport_mutex_man.ivy` — messages are (kind, timestamp)

This is the algorithm as Lamport states it: three message kinds, a request queue
`request_ts(X)` per node, a reply-timestamp map `reply_ts(X)` per node, and the entry
test

```
state = waiting
& forall X. X = self | request_ts(X) = 0 | lexord(request_ts(self),self,request_ts(X),X)
& forall X. X = self | reply_ts(X) > request_ts(self)
```

It verifies `OK` as delivered. Crucially, its overlay *does* constrain delivery order,
and its own comment appeals to that: *"Because of in-order delivery, the timestamps are
received in increasing order, so the incoming one must be the greatest so far."*
In-order delivery is exactly what makes `check_cs`'s guard stable, which is exactly what
makes weak fairness sufficient (§4).

**Decision: build on `man`.**

### 1.3 But flatten it

`man` is written in implementation style: `process node(self:host_id)`, a
`trusted isolate overlay`, a `msg_t` struct, and a top-level
`proof [this] { tactic flatten_structs; tactic macro_expand }`. The liveness-to-safety
tactics attach their monitor to **one** monolithic transition system, and every liveness
example in this repository (`bakery.ivy`, `ticket_ranking.ivy`, `german_3channels_*.ivy`)
is a flat model. So the proof file is a flattening:

| `lamport_mutex_man.ivy` | `lamport_mutex_live.ivy` |
|---|---|
| `node(Y).request_ts(X)` | `req(Y,X)` |
| `node(Y).reply_ts(X)` | `rep(Y,X)` |
| `node(Y).ts` | `clock(Y)` |
| `node(Y).state` | `st(Y)` |
| `overlay.sent(S,D,msg_t.cons(K,T))` | `chan(S,D,K,T)` |

---

## 2. What else changed, and why

1. **`finite type node`, with `<` axiomatised as a total order.** Finiteness is what
   makes `work_created = true` a legitimate finite bound `R` for the node-sorted
   rankings `[02]` and `[04]` (Rule 5). The order is Lamport's tie-break.
2. **Delivery order weakened from global to per-channel.** `man`'s overlay requires
   `sent(S,self,M) -> ~(M < msg)` over **all** senders `S`: the receiver always takes the
   globally least timestamp pending for it. That is strictly stronger than TCP and is not
   what the algorithm needs. `lamport_mutex_live.ivy` delivers the least timestamp *of
   the channel from s to d*:

   ```ivy
   if some t:ts. (exists K. chan(s,d,K,t)) minimizing t { ... }
   ```

   Since a node stamps every message it sends with a value strictly above its clock,
   least-timestamp-first on one channel *is* FIFO on that channel. This is a **weaker**
   assumption than `man` makes, so the liveness result is correspondingly stronger.
3. **Fairness instrumentation** on the three fair rules, guarded-command style (§4).
4. **`check_cs` reads a cached `blocked` flag** instead of evaluating the two quantified
   conjuncts inline. This is an implementation detail of the model, forced by the
   decidable fragment — see §7.2.
5. **Ghost state**, none of which changes behaviour: `rcvd`, `replied`, `lastrel`,
   `last_ts`/`last_node`, `front`/`has_front`. Each is explained where it is used.
6. **`request_cs` is an `if`-guarded environment action with no fairness flag.** We never
   want to assume requests are issued, and an unguarded `require` would prune traces
   (`LIVENESS_CASE_STUDY_GERMAN.md` §3.1).

---

## 3. Formalising the property

### 3.1 The goal is `critical`, not "not waiting"

In this model there is no weaker non-vacuous wording. `waiting -> eventually ~waiting`
would be discharged by any exit from `waiting`, and the only exit is `critical`. So the
property is stated directly:

```ivy
forall C. globally (st(C) = waiting -> eventually st(C) = critical)
```

The goal is a **state predicate** and `work_invar` is essentially its negation, which is
what `l2s_not_all_done` / `l2s_invar` need (`LIVENESS_CASE_STUDY_GERMAN.md` §6.5–6.6).

### 3.2 Why there is a second Skolem constant `_R`

Every ranking has to talk about *the position of the tracked request in the global
(timestamp, id) order* — "the nodes ahead of me", "the messages older than my request".
Written against the state term `req(_C,_C)` those predicates would be re-evaluated at
every state. Carrying the request timestamp as a second universally quantified variable

```ivy
forall C,R. globally ((st(C) = waiting & req(C,C) = R) -> eventually st(C) = critical)
```

turns it into a rigid Skolem constant `_R` after `skolemizenp`, and the trigger pins it:
`work_invar` is `st(_C) = waiting & req(_C,_C) = _R`, and `~(eventually st(_C) = critical)`
keeps `_C` waiting, which keeps `req(_C,_C)` equal to `_R` (only `request_cs` and
`exit_cs` write it, and both need `_C` to be idle or critical).

The headline form is then a one-line corollary — Rule 7 lemma chaining, with a trivial
ranking and all the work done by the progress condition:

```ivy
explicit temporal property [starvation_freedom]
  forall C. globally (st(C) = waiting -> eventually st(C) = critical)
proof {
  tactic skolemizenp;
  instantiate live with C = _C;
  tactic ranking with {
    definition work_created = true
    definition work_needed  = true
    definition work_invar   = eventually st(_C) = critical
    definition work_progress= st(_C) = critical
    definition work_helpful = true
  }
}
```

`instantiate live with C = _C` leaves `R` universally quantified, and Z3 instantiates it
with `req(_C,_C)` at the state where the trigger fires.

---

## 4. Fairness: weak everywhere, and why that is enough

```ivy
explicit temporal axiom [wfa_recv]  forall S,D. globally eventually wf_recv(S,D)
explicit temporal axiom [wfa_check] forall N.   globally eventually wf_check(N)
explicit temporal axiom [wfa_exit]  forall N.   globally eventually wf_exit(N)
```

Each flag is pulsed **unconditionally, before the rule's guard**, so a turn offered to a
disabled rule is a stutter step and the axiom is an honest statement about the scheduler
rather than a disguised assumption that the rule fires
(`LIVENESS_CASE_STUDY_GERMAN.md` §3.1, the vacuity trap).

### 4.1 The stability audit

A rule needs only weak fairness if its guard, once true, stays true until the rule itself
fires. Done by hand for all three fair rules before writing any ranking:

| rule | guard | stable once enabled? | why |
|---|---|---|---|
| `recv(s,d)` | channel `(s,d)` non-empty | **yes** | only `recv(s,d)` removes from it; sends only add, and always with a larger timestamp |
| `check_cs(n)` | `st(n) = waiting & ~blocked(n)` | **yes** | `rep(n,·)` only grows and `req(n,n)` is frozen while `n` waits; and once `n` has heard a reply later than its own request from every peer, `[rep_le_rcvd]` + `[fifo]` say no *earlier* request can still arrive from that peer, so the queue conjunct cannot be falsified either |
| `exit_cs(n)` | `st(n) = critical` | **yes** | only `exit_cs(n)` leaves the critical section |

No row says "no". **Lamport's DME is starvation-free under weak fairness alone.**

### 4.2 Contrast with the German protocol

`german_3channels_original.ivy` needs *compassion* for exactly one rule,
`pickNewRequestRule(cl)`, because the home's arbiter picks an arbitrary queued client and
its guard (`homeCurrentCommand = empty1 & channel1(cl) ~= empty1`) is falsified by another
client's pick. Lamport's algorithm has no arbiter to be unfair: **the arbiter is the
(timestamp, id) order itself, which is FIFO**, and the FIFO channels propagate it. This
is the same reason `german_3channels_fifo.ivy` gets away with weak fairness — but here it
is a property of the algorithm as published, not a modelling change.

Note the assumption that is doing that work: **per-channel FIFO delivery**. Drop it and
`check_cs`'s guard stops being stable, and the proof — and, as far as the hand argument
goes, the property — needs more.

---

## 5. The ranking

One `ranking` call (Rule 10, lexicographic), five components, highest order first.
Writing `r = _R` for the tracked request's timestamp and
`aheadeq(X) = st(X) ~= idle & lexle(req(X,X),X,r,_C)`:

| # | `work_needed` (δ) | `work_helpful` (ψ) | `work_progress` (r) |
|---|---|---|---|
| `[00]` | `∃K. chan(_C,D,K,T) ∧ T ≤ r`, over `(S,D,T)` with `S = _C` | `S = _C ∧ ∃K,T. chan(_C,D,K,T) ∧ T ≤ r` | `wf_recv(S,D)` |
| `[01]` | `∃K. chan(S,D,K,T) ∧ T ≤ r`, over `(S,D,T)` | `∃K,T. chan(S,D,K,T) ∧ T ≤ r` | `wf_recv(S,D)` |
| `[02]` | `aheadeq(X)`, over `(X)` | `st(X) = critical` | `wf_exit(X)` |
| `[03]` | `∃K. chan(S,D,K,T) ∧ aheadeq(D) ∧ T ≤ lastrr(S,D)`, over `(S,D,T)` | `aheadeq(D) ∧ ∃K,T. chan(S,D,K,T) ∧ T ≤ lastrr(S,D)` | `wf_recv(S,D)` |
| `[04]` | `aheadeq(X) ∧ st(X) = waiting`, over `(X)` | `has_front ∧ X = front ∧ aheadeq(X) ∧ st(X) = waiting ∧ ~blocked(front)` | `wf_check(X)` |

`lastrr(S,D) = max(replied(S,D), lastrel(S,D))` is the timestamp of the last **reply or
release** `S` sent `D`: a reply is what satisfies `D`'s "heard a later reply from
everyone" test, a release is what clears a stale entry from `D`'s queue. So `[03]` drains
exactly the channel prefix an ahead node still has to consume before it can move.

`work_created` is `(exists K. chan(S,D,K,T))` for the three message rankings and `true`
for the two node rankings.

### 5.1 What each component buys, and why the order is what it is

Under Rule 10 a component must be **conserved** only while no higher component is
scheduled, but must **reduce** whenever its own scheduler is on and its justice condition
fires, preempted or not (`LIVENESS_CASE_STUDY_GERMAN.md` §6.2). So the whole design is a
question of "who is allowed to grow when".

- **`[00]`** — *`_C`'s own outgoing messages up to its request.* This is the top
  component, so it must **never** grow, and it does not: while `_C` waits it only ever
  sends replies, and those are stamped strictly above its clock, which already dominates
  `r`; and nothing else writes a channel out of `_C`. Emptying it means every node has
  received `_C`'s request.

- **`[01]`** — *every message in flight with timestamp ≤ r.* This one **does** grow: a
  node whose clock is still below `r` can issue a request that lands below `r`. But by
  invariant `[aware]`,

  ```ivy
  st(S) ~= idle & D ~= S & ~chan(S,D,request,req(S,S)) -> clock(D) > req(S,S)
  ```

  a node whose clock is below `r` has *not yet received `_C`'s request*, so
  `chan(_C,D,request,r)` is in flight and `[00]`'s scheduler is on. That is exactly the
  licence Rule 10 gives. Emptying `[01]` means every request ordered at or before `_C`'s
  has been delivered everywhere.

- **`[02]`** — *the nodes whose request is at or before `(r,_C)`.* Reduced by `exit_cs`.
  Its scheduler is just "somebody is in the critical section", which is sound because of

  ```ivy
  invariant [crit_global_least]
      st(X) = critical & st(Y) ~= idle & Y ~= X -> lexord(req(X,X),X,req(Y,Y),Y)
  ```

  — a critical node holds the least request in the *whole system*, so with `_C` pending it
  is necessarily one of the nodes ahead of `_C`. (This is the alternative invariant
  `lamport_mutex_man.ivy` mentions in a comment but does not use.) `[02]` grows only when
  a node with a clock below `r` requests, i.e. under `[00]`.

- **`[03]`** — *the messages that can unblock an ahead node.* `lastrr(S,D)` advances only
  when `S` answers a request from `D` (an ahead `D`'s requests all have timestamp ≤ `r`,
  so `[01]` is scheduled) or when `S` leaves its critical section (so `[02]` is). Hence
  `[02]` must sit **above** `[03]`, and `[01]` above both.

- **`[04]`** — *the ahead nodes that are still waiting.* Reduced by `check_cs`. `_C`
  itself is always in this set, so the only way for the lexicographic ranking to stop
  decreasing is for `_C` to enter — the goal.

---

## 6. "Something is always scheduled" — premise S4

`l2s_sched_exists` is the heart of the proof. Suppose `_C` is waiting with request `r`
and none of the five schedulers is on. Then:

- `¬ψ₀₀`: every node has received `_C`'s request.
- `¬ψ₀₁`: no message with timestamp ≤ `r` is in flight anywhere.
- `¬ψ₀₂`: nobody is in a critical section.
- `¬ψ₀₃`: for every ahead node `D` and every `S`, the channel `(S,D)` holds nothing with
  timestamp ≤ `lastrr(S,D)`.

Take `F = front`, the least pending node, which exists (`[front_exists]`, `_C` is
pending) and is not critical, hence waiting. `F` is ahead of or equal to `_C` by
`[front_min]`. If `F` were blocked, `[front_blocked_witness]` hands over a peer `Y` with
one of two complaints:

**(i) `F`'s queue holds a request of `Y` ordered before `F`'s own.** Either `Y` is
currently pending with that very request — impossible, since `Y` would then be a pending
node strictly before `F`, contradicting `[front_min]` — or `Y` has moved on, and then
`[stale_release]` says `Y`'s release is still on its way to `F`:

```ivy
invariant [stale_release]
    D ~= S & req(D,S) ~= 0 & ~(st(S) ~= idle & req(S,S) = req(D,S)) ->
        (chan(S,D,release,lastrel(S,D)) & lastrel(S,D) > req(D,S))
```

That message has timestamp `lastrel(Y,F) ≤ lastrr(Y,F)`, so `ψ₀₃(Y,F)` is on —
contradiction.

**(ii) `F` has not heard a reply from `Y` later than its own request.** `F`'s request has
timestamp ≤ `r`, so by `¬ψ₀₁` it is not in flight, so by `[request_known]` `Y` received
it, so by `[aware_replied]` `replied(Y,F) > req(F,F) ≥ rep(F,Y)`, so by
`[replied_inflight]` that reply is still in flight — and again its timestamp is
≤ `lastrr(Y,F)`, so `ψ₀₃(Y,F)` is on. Contradiction.

So `F` is not blocked, `ψ₀₄(front)` is on, and S4 holds.

---

## 7. Three obstacles that were about decidability, not about the protocol

All three showed up as `error: The verification condition is not in the fragment FAU.`
or as a non-inductive monitor invariant, and all three were solved by changing *how* the
model says something, not *what* it says.

### 7.1 Finiteness for the timestamp sort, and the sliced ghost

Rankings `[00]`, `[01]`, `[03]` and the `[delivery]` lemma are parameterised by a
timestamp, so Rule 5 requires `work_created → l2s_d` — every in-flight timestamp must be
in the monitor's abstraction domain. `l2s_d` is fed from two places only
(`ivy_l2s.py`): the parameters of exported actions, and the values of **nullary** state
symbols, both at the end of every step. Timestamps here are minted inside the actions
(`clock(n).next`), and `clock` is a function, not a nullary symbol.

The fix is a ghost `var last_ts : ts` assigned the timestamp minted by each step. The
trap: with nothing reading it, Ivy **slices the ghost away**, the assignment disappears
from the action, and `l2s_created` fails with a CTI in which the new timestamp is simply
absent from `l2s_d`. Anchoring it with a second ghost and an invariant fixes it:

```ivy
var last_ts : ts
var last_node : node
invariant [last_mint] clock(last_node) = last_ts
```

A second, subtler point: `work_created` must be **inductive on its own**. The first
attempt used the ranking itself as the bound,

```ivy
definition work_created[03](S,D,T) = (exists K. chan(S,D,K,T)) & aheadeq(D,_R,_C) & T <= lastrr(S,D)
```

which fails, because `aheadeq(D)` or `lastrr(S,D)` can newly become true for a message
that was already in flight, and then the induction hypothesis does not apply to it. The
bound only has to be a finite superset of δ, so `(exists K. chan(S,D,K,T))` — "the
messages produced so far" — is both correct and inductive. This was the last failing
check in the whole development.

### 7.2 A quantified entry guard cannot be a `work_helpful`

`work_helpful[04]` has to name `check_cs`'s enabling guard, or `l2s_progress` fails
(the guard is not preemption-discounted). Written as it stands in `lamport_mutex_man.ivy`
it is two universally quantified conjuncts, and `work_helpful` occurs **negatively** in
`l2s_sched_stable` and `l2s_progress` and inside `no_help` — so the `forall` becomes an
`exists` under a `forall` over nodes, and the verification condition leaves FAU.

The model therefore caches the test in a flag that `check_cs` reads:

```ivy
action refresh(n:node) = {
    if some y:node. y ~= n
         & ((req(n,y) ~= 0 & ~lexord(req(n,n),n,req(n,y),y)) | rep(n,y) <= req(n,n)) {
        blocked(n) := true;
    } else {
        blocked(n) := false;
    }
}
```

with `refresh` called wherever a node's own view changes (`request_cs`, `recv`,
`exit_cs`). This is an ordinary implementation detail — a node recomputing whether it is
still held up — and it makes `work_helpful[04]` quantifier-free.

### 7.3 The witness has to be nullary

S4 needs the *other* direction: `blocked(N)` must hand back a blocking peer. The obvious
encoding, a witness function `var blk(N:node) : node` with

```ivy
invariant [blocked_witness] st(N) = waiting & blocked(N) -> ... req(N,blk(N)) ...
```

is rejected, and Ivy says exactly why:

```
The following terms may generate an infinite sequence of instantiations:
  line 93: N1:node < N2
    (position 1 is a function from node to node)
```

A `node -> node` function is a self-loop in the stratification graph. The remedy is the
one `bakery.ivy` uses for the least ticket: a **nullary** witness.

```ivy
var front : node
relation has_front
```

maintained as the least pending request in the global (timestamp, id) order — updated in
`request_cs` by a quantifier-free comparison against the current `front`, and recomputed
in `exit_cs` by two nested `minimizing` searches (timestamp first, then node id; Ivy's
`minimizing` puts the minimality condition only in the *then* branch, so the `else`
branch stays quantifier-free). Because `front` is nullary, the existential

```ivy
invariant [front_blocked_witness]
    has_front & st(front) = waiting & blocked(front) ->
        (exists Y. Y ~= front & (...))
```

skolemizes to a **constant** and the verification condition stays in FAU.

---

## 8. The `[delivery]` lemma

```ivy
explicit temporal property [delivery]
  forall S,D,K,T. globally (chan(S,D,K,T) -> eventually ~chan(S,D,K,T))
proof {
  tactic skolemizenp;
  instantiate wfa_recv with S = _S, D = _D;
  tactic ranking with {
    definition work_created(T1:ts) = (exists K. chan(_S,_D,K,T1)) & T1 <= _T
    definition work_needed(T1:ts)  = (exists K. chan(_S,_D,K,T1)) & T1 <= _T
    definition work_invar          = chan(_S,_D,_K,_T)
    definition work_progress       = wf_recv(_S,_D)
    definition work_helpful        = exists K,T1. chan(_S,_D,K,T1) & T1 <= _T
  }
}
```

This is the CAV'24 timestamped-queue ranking, one component: the set of timestamps still
in the channel that are no larger than the tracked message's own. It is conserved because
`_S` stamps every new message strictly above its clock, which already dominates `_T`
(`[msg_below_clock]`), and each turn given to `recv(_S,_D)` removes the least timestamp in
the channel, which is ≤ `_T` whenever the ranking is non-empty.

The main proof does **not** use `[delivery]` — it drains channels with rankings `[00]`,
`[01]` and `[03]` directly, which keeps every progress condition a plain `wf_*` pulse and
keeps temporal operators out of the tactic block entirely. `[delivery]` is kept because it
is the statement the FIFO model is really making, and because it is the one place where
the finiteness mechanism of §7.1 can be seen on its own.

---

## 9. Safety invariants

The nine invariants of `lamport_mutex_man.ivy` carry over essentially unchanged
(`msg_below_clock`, `req_below_clock`, `rep_below_clock`, `no_self_msg`,
`rel_before_req`, `no_regress_req`, `no_regress_rep`, `req_le_own`, `request_known`,
`crit_heard`, `crit_least`, `mutex`). The additions, in three groups:

**Group A — the FIFO channel.**

| invariant | says |
|---|---|
| `fifo` | `chan(S,D,K,T) -> rcvd(D,S) < T`: nothing in flight is older than what has been consumed |
| `one_kind` | a timestamp identifies a message within a channel |
| `rep_le_rcvd` | a recorded reply is no later than the last timestamp consumed — with `fifo`, this is what makes `check_cs`'s guard stable |

**Group B — one round at a time.** These rule out a node's own stale request lingering in
a channel, which is what lets `req(S,S)` be read as "the request that is in flight".

```ivy
invariant [rep_le_replied]         rep(S,D) <= replied(D,S)
invariant [idle_no_request]        st(S) = idle -> ~chan(S,D,request,T)
invariant [req_inflight_unreplied] chan(S,D,request,T) -> replied(D,S) < T
invariant [reply_inflight_unheard] chan(D,S,reply,Q) ->
                                     (st(S) = waiting & rep(S,D) < req(S,S)
                                      & rcvd(D,S) >= req(S,S))
invariant [one_reply_inflight]     chan(D,S,reply,Q1) & chan(D,S,reply,Q2) -> Q1 = Q2
invariant [req_is_own]             chan(S,D,request,T) & st(S) ~= idle -> T = req(S,S)
```

None of these is inductive alone; the conjunction is. They were harvested from CTIs, and
the first CTI in the group was a state with two message kinds carrying the same
timestamp — which is what produced `one_kind`.

**Group C — the liveness argument proper.**

| invariant | needed for |
|---|---|
| `aware` | conservation of `[01]` and `[02]` (§5.1) |
| `aware_replied`, `replied_inflight` | case (ii) of S4 |
| `stale_release`, `stale_request` | case (i) of S4 |
| `crit_global_least` | the scheduler of `[02]` |
| `blocked_sound` | `~blocked` really implies the entry test (needed for `mutex`) |
| `front_pending`, `front_exists`, `front_min`, `front_blocked_witness` | S4 |

---

## 10. Non-vacuity

### 10.1 The interesting states are reachable

Each probe was added as a deliberately false invariant and confirmed **violated**:

| probe | result |
|---|---|
| `st(N) ~= critical` | violated — nodes do enter |
| `~(st(X) = waiting & st(Y) = critical & X ~= Y)` | violated — contention is reachable |
| `~(st(X) = waiting & st(Y) = waiting & X ~= Y)` | violated — two waiters at once |
| `~chan(S,D,reply,T)` | violated — replies really fly |
| `req(N,X) = 0 \| N = X` | violated — request queues really fill |

### 10.2 Parameter ablations

Each row mutates one parameter of the verifying file and re-runs `ivy_check`. The intact
file takes **6.3 s**; a mutated one either reports a specific failed check or does not
finish. Note the asymmetry in how the results read: a *failed check* is direct evidence
that the premise is false, whereas a *timeout* only says the proof no longer goes through
(Z3 diverges rather than producing a counterexample on the broken verification
conditions). Where a timeout was uninformative, the run was repeated with
`action=<name>` to shrink the verification condition until the check named itself.

| mutation | result |
|---|---|
| `work_helpful[04] := true` (drop the entry guard from the scheduler) | **`l2s_progress[04] ... FAIL`** |
| `work_needed[01]` without the `T <= _R` bound | **`l2s_needed_preserved[01] ... FAIL`** (`action=request_cs`) |
| `work_progress[02] := false` | **`l2s_progress[02] ... FAIL`** (`action=request_cs`) |
| `work_progress[00] := false` | does not verify (>300 s) |
| `work_progress[01] := false` | does not verify (>300 s) |
| `work_progress[03] := false` | does not verify (>300 s) |
| `work_progress[04] := false` | does not verify (>300 s) |
| `work_helpful[01] := true` | does not verify (>300 s) |
| `work_needed[03]` without the `T <= lastrr(S,D)` bound | does not verify (>240 s; `action=request_cs` only — `exit_cs`, `recv`, `check_cs` all still pass, which localises the break to conservation of `[03]` when a new request arrives) |
| **`l2s_auto5` instead of `ranking`** (Rule 8, i.e. no preemption) | does not verify (>240 s on `request_cs` and `exit_cs`; `check_cs` alone still passes) |

The first row is the decisive one: it is the check that says the *stable scheduler* is
real, not cosmetic — `check_cs(X)` firing only reduces `[04]` when `X` is actually
unblocked, which is the whole reason the `blocked` flag had to be introduced (§7.2).
The second and third confirm that the two devices the ranking is built on — bounding a
message ranking by the tracked request's timestamp, and pointing each ranking at the
rule that actually reduces it — are load-bearing.

The `l2s_auto5` row is the one that says *lexicographic* order is what makes this work:
under Rule 8 every ranking must be conserved by every action, and `[01]`–`[04]` all grow
when a node with a stale clock issues a request.

For the `[delivery]` lemma, run separately:

| mutation | result |
|---|---|
| `work_progress := false` | `l2s_progress ... FAIL` (×5), `l2s_progress_eventually ... FAIL` (×5) |
| `work_needed` without the `T1 <= _T` bound | `l2s_needed_implies_created ... FAIL` (×5), `l2s_needed_preserved ... FAIL` (×3) |

---

## 11. Caveats

1. **Per-channel FIFO is an assumption**, and a load-bearing one: it is what makes
   `check_cs`'s guard stable and hence what makes weak fairness sufficient. It is weaker
   than the global timestamp order `lamport_mutex_man.ivy` assumes, and it is what TCP
   gives, but an unordered network is outside this proof.
2. **`finite type node`.** All the node-sorted rankings rely on it.
3. **The cached `blocked` flag and the `front` variable are part of the model.**
   `blocked` is an implementation detail with no behavioural effect (`blocked_sound`
   pins it to the entry test, and `mutex` is proved against it). `front` is pure ghost
   state — nothing reads it outside the invariants and `work_helpful[04]`. Neither
   changes the set of executions, but both are there for the prover, not for the
   algorithm.
4. **Clients are not forced to request and not forced to be well-behaved beyond the
   protocol**: `request_cs` is guarded by `st(n) = idle`, i.e. a node does not pipeline
   requests. This is how `lamport_mutex_man.ivy` states it too (`require client_state =
   idle`).
5. **Not machine-checked: that the property fails without FIFO.** §4.1 is a hand
   argument. What is machine-checked is that the invariants which encode FIFO
   (`fifo`, `rep_le_rcvd`) are load-bearing in this proof.
