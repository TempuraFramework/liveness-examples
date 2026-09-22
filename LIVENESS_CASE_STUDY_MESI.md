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

## 1. Background: what cache coherence is, for readers with no architecture background

This section assumes you know transition systems, invariants and temporal logic, and
nothing at all about computer architecture. If you already know what MESI is, skip to
§3.

### 1.1 Caches, lines, and why they exist

Main memory (DRAM) is slow: a few hundred processor cycles per access. So each
processor core keeps a small, fast, *private* copy of the memory locations it has been
using recently. That private copy is a **cache**.

Memory is divided into fixed-size blocks — typically 64 bytes — called **cache lines**.
The line is the unit of everything: caches fetch, hold, and give up whole lines. For our
purposes a line is just "one memory location", and since coherence is a per-line
property that loses nothing: the model tracks a single line, and every statement below
is implicitly "for this line".

On a single-core machine a cache is invisible: it is a pure optimisation and no program
can tell it is there.

### 1.2 The problem: caches become visible when there are several of them

Now give each of two cores its own cache, and let both of them cache the same line.

```
memory:  x = 0
core 0's cache:  x = 0          core 1's cache:  x = 0
core 0 writes x := 1  (into its own cache)
core 1 reads x        (from its own cache)  -->  0
```

Core 1 reads 0 after core 0 wrote 1, and will keep doing so forever. No execution of
this program on a machine *without* caches could produce that result. The private
optimisation has become observable, which is a bug — and not a subtle performance bug
but a correctness bug that breaks locks, queues, and every other synchronisation
primitive.

A **cache coherence protocol** is the mechanism that prevents this. It is a distributed
protocol between the cache controllers, and it is exactly the kind of object this
repository verifies: concurrent agents, message channels, a shared arbiter, and both a
safety property and a progress property that are easy to state and hard to prove.

### 1.3 What "coherent" means, precisely

The standard definition (Sorin, Hill & Wood, *A Primer on Memory Consistency and Cache
Coherence*) is stated as two invariants that a protocol must maintain, for each line:

* **SWMR — single writer / multiple reader.** At any moment in time, *either* exactly
  one core may write the line and no other core has any copy, *or* any number of cores
  may read it and none may write.
* **Data value invariant.** When a read-only epoch begins, the value of the line is the
  one produced by the last write epoch.

These two are not a proxy for coherence; they *are* the textbook definition of it. That
matters for reading this case study, because the safety theorem in `mesi.ivy` is
literally these two invariants and nothing else:

| the textbook invariant | the Ivy invariant |
|---|---|
| SWMR | `swmr`: `(s.cache(C1) = modified \| s.cache(C1) = exclusive) & C1 ~= C2 -> s.cache(C2) = invalid` |
| data value | `data_coh`: `(s.cache(C) = shared \| s.cache(C) = exclusive) -> s.cdata(C) = s.mem` |

(`modified` and `exclusive` are the states in which a core may write, or may start
writing without asking anyone; so "an M or E copy is the only copy" is SWMR, and "every
clean valid copy equals memory" is the data invariant, given that a dirty copy is
flushed back before anybody else may observe the line.)

**Coherence is not consistency.** A common confusion worth heading off: *coherence* is
per-location (it makes each single location behave like one variable); *memory
consistency* (sequential consistency, TSO, …) is about how operations to *different*
locations may be ordered relative to each other. MESI is a coherence protocol. It says
nothing about consistency, and neither does this case study.

### 1.4 Invalidation, buses, and snooping

Two families of coherence protocol exist. **Update** protocols broadcast each new value
to every cache holding the line. **Invalidation** protocols instead require a writer to
*destroy* every other copy before writing. Invalidation wins in practice (a burst of
writes by one core costs one invalidation, not one broadcast per write) and MESI is an
invalidation protocol.

That leaves the question of how a cache finds out that it must invalidate. Again two
families:

* **Snooping.** All caches sit on a shared broadcast medium, the **bus**. Only one
  transaction may be in progress at a time, so some **arbiter** decides who goes next.
  Every cache controller watches — *snoops* — every transaction and reacts to it
  according to its own current state. Nobody keeps a list of who has what.
* **Directory.** A central directory records, for each line, which caches hold it, and
  sends point-to-point messages only to those caches. This is what the German protocol
  (`german_3channels_*.ivy`, `LIVENESS_CASE_STUDY_GERMAN.md`) does.

**MESI is a snooping protocol**, and that is the main structural difference between this
case study and the German one. It has a concrete consequence for the proofs: a snooping
controller's per-transaction bookkeeping is created fresh at the start of each
transaction and only shrinks, whereas a directory's sharer list persists across
transactions and can *grow* while a client is waiting. §13 returns to this.

### 1.5 One more piece of vocabulary: dirty lines and flushing

A cache that has written to its copy holds a value that main memory does not have. Such
a copy is **dirty**; memory is stale. If anyone else ever needs that line, the dirty
value must be handed over first — written back to memory (or forwarded directly). That
write-back is called a **flush**, and it is why the M state's snoop rows below say
"Flush" rather than just changing state.

---

## 2. The MESI protocol

### 2.1 The four states, and why exactly four

Each cache tags its copy of the line with one of four states. Read the table as "what
permissions do I hold, and what do I know about everyone else":

| state | may read | may write | others may hold a copy | memory up to date |
|---|---|---|---|---|
| **M** modified | yes | **yes** | **no** | **no** (this copy is dirty) |
| **E** exclusive | yes | not yet — but may upgrade silently | **no** | yes |
| **S** shared | yes | no | yes | yes |
| **I** invalid | no | no | yes | — (no copy held) |

M and E are the *exclusive* states: holding either one means you know for certain that
no other cache has the line. They differ only in whether you have dirtied it.

**Why four and not three.** The minimal invalidation protocol is MSI: M, S, I. It is
correct. Its inefficiency is this extremely common pattern —

```
core 0 reads a line nobody else has, then writes it
```

Under MSI the read lands in S (because S is the only clean state there is), so the
subsequent write must issue a *second* bus transaction to invalidate copies — of which
there are none. Two bus transactions where one would have done, on thread-private data
and on the ubiquitous read-then-modify pattern.

MESI fixes it by splitting the clean states in two according to what the reader learned
during its read: land in **S** if somebody else answered "I have a copy", and in **E**
if nobody did. From E, the write needs no bus transaction at all, because E already
guarantees that nobody else has a copy to invalidate.

**That is the entire content of the "E" in MESI**: one extra state, one extra bit of
information gathered during the read, and one bus transaction saved on a very common
pattern. Everything else is MSI. Both halves of it are modelled here, and §5.3 shows
both are reachable in the model rather than dead code.

### 2.2 The bus transactions

| transaction | issued by | meaning |
|---|---|---|
| **BusRd** | a core with no copy that wants to read | "I want a readable copy" |
| **BusRdX** | a core with no copy that wants to write | "I want a writable copy; everyone else drop yours" |
| **BusUpgr** | a core holding S that wants to write | "everyone else drop yours" (it already has the data) |
| **Flush** | a snooping core holding M | writes the dirty line back so others may use it |

Plus one thing that is not a transaction but a *wire*: the **shared line**. This is a
wired-OR signal that any snooping cache may assert during a BusRd to mean "I have a copy
of this line". The requester samples it at the end of the transaction, and it is
precisely what lets the requester tell E from S. It is the mechanism that makes MESI
possible, and in the Ivy model it is the variable `ctl_shared` (§4.2).

### 2.3 The processor-side table, row by row

This is what a cache does when *its own* core issues a load (PrRd) or a store (PrWr).

| current state | operation | what happens | why |
|---|---|---|---|
| I | PrRd | issue **BusRd**; land in **E** if the shared line stayed low, in **S** if it was asserted | you need a copy; whether others have one decides which clean state you may claim |
| S / E / M | PrRd | **hit** — nothing happens at all | you already have a readable copy |
| I | PrWr | issue **BusRdX**; land in **M** | you need both the data and exclusivity |
| S | PrWr | issue **BusUpgr**; land in **M** | you have the data; you need others' copies gone |
| **E** | **PrWr** | **silent upgrade E → M. No bus transaction whatsoever.** | E already guarantees nobody else has a copy, so there is nothing to invalidate and nobody to tell |
| M | PrWr | **hit** — write into the already-dirty copy | you have write permission |

Three of these rows do nothing observable (the two read hits and the M write hit) and
are therefore not separate actions in the model; §3 explains that choice.

### 2.4 The snoop-side table, row by row

This is what a cache does when it observes *somebody else's* transaction on the bus.

| observed | I am in M | I am in E | I am in S | I am in I |
|---|---|---|---|---|
| **BusRd** | **Flush**, then → S | → S | stay S | stay I |
| **BusRdX** / BusUpgr | **Flush**, then → I | → I | → I | stay I |

and in every row except the last, the snooper asserts the shared line.

The reasoning, row by row:

* *BusRd seen in M.* Someone wants to read; you hold the only, dirty copy. You must
  write it back (Flush) so they get the current value, and you must drop to S because
  you will no longer be the only holder, and S is not writable.
* *BusRd seen in E.* Same, minus the flush: your copy is clean, memory already has the
  value. You drop E → S because your exclusivity claim is about to become false.
* *BusRd seen in S.* Nothing to do but assert the shared line — which is exactly what
  stops the requester from claiming E.
* *BusRd seen in I.* Nothing. Critically, you do **not** assert the shared line, and if
  *no* cache asserts it the requester gets E.
* *BusRdX seen in M.* Flush (they need your dirty value) and go to I (they are taking
  write permission).
* *BusRdX seen in E or S.* Go to I. No flush: your copy was clean.

### 2.5 A complete scenario, end to end

Two cores, memory holding `v0`, both caches invalid. This is the scenario traced
through the actual Ivy code in §4.6.

| # | event | resulting state |
|---|---|---|
| 1 | core 0 issues PrRd, misses, puts **BusRd** on the bus | |
| 2 | core 1 snoops it in state I: no flush, **shared line stays low** | |
| 3 | transaction completes; nobody claimed a copy, so core 0 is granted **E** | `0: E(v0)`, `1: I`, mem `v0` |
| 4 | core 0 issues PrWr. It is in E, so it **silently** becomes M | `0: M(v1)`, `1: I`, mem `v0` |
| 5 | core 1 issues PrRd, misses, puts **BusRd** on the bus | |
| 6 | core 0 snoops it in state M: **Flush** (mem := v1), drop to S, **assert shared** | mem `v1` |
| 7 | transaction completes; shared was asserted, so core 1 is granted **S** | `0: S(v1)`, `1: S(v1)`, mem `v1` |

Note what the trace demonstrates. Step 3 is the E optimisation (one bus transaction, not
the two MSI would need, because step 4 is free). Step 6 is why M needs a flush at all.
And the end state satisfies both coherence invariants: no M or E copy exists, so SWMR is
trivially satisfied, and both clean copies equal memory, so the data invariant holds.

---

## 3. From protocol to transition system: the modelling decisions

Six decisions turn §2 into `mesi.ivy`. Each one is a place where the model could
reasonably have been different, so each is stated with its justification.

**1. A split-transaction bus.** A textbook snooping bus performs a transaction
atomically: request, snoop, response, all in one indivisible step. Modelled that way,
MESI has no concurrency left in it — every safety invariant becomes trivial and the
liveness proof degenerates into "assume the bus is fairly arbitrated", which assumes the
interesting part. Real buses have not worked that way for decades.

So the bus controller is a separate process and a transaction is a *pipeline*:

```
arbitrate -> send a snoop to every other cache -> each cache processes its snoop
          and answers -> the controller collects the answers -> the controller
          grants the line to the requester
```

with each leg in its own unit-capacity channel, as in the German model:

```
chan_req(C)   : cache      -> controller   busrd | busrdx
chan_snoop(C) : controller -> cache        snoops AND grants
chan_resp(C)  : cache      -> controller   snoop responses
```

**2. One downward channel per cache, carrying both snoops and grants.** `chan_snoop(C)`
holds *either* a snoop request for C *or* a grant to C, never both, because it has
capacity one. This models the real constraint that a cache controller has a single
snoop/fill port and processes one downward message at a time; it is not a claim about
how many wires the bus has.

This is the single most load-bearing modelling decision in the file. It is what
serialises the protocol, and the entire exclusivity argument rests on it (§5.2). It also
creates a genuine extra pipeline stage in the liveness proof — a cache sitting on an
unconsumed grant is *blocking* the snoop the controller needs to send it, so draining
that grant is real work that has to be ranked (§9, components [07]–[09]).

**3. No directory.** Being a snooping protocol, the controller keeps no sharer list. It
broadcasts to every cache except the requester and learns who holds a copy from the
responses. `ctl_shared` is the shared line of §2.2: the OR of the responses, and the
thing that decides between granting E and granting S.

**4. BusRdX and BusUpgr are the same message.** They differ only in whether the
requester needs the data transferred; the coherence state machine cannot tell them
apart, and this model puts no data on the bus. So `pr_write_miss` (from I) and
`pr_write_upgrade` (from S) both put `busrdx` in the request channel. Merging them
loses nothing for either theorem.

**5. Caches block.** A ghost bit `waiting(C)` is raised when C issues a request and
lowered exactly when C consumes the grant; the request actions `require ~waiting(cl)`.
Without this a cache could pipeline requests, `waiting` would stop identifying a single
request, and the three-stage decomposition of §6 would collapse. This is the standard
modelling assumption, the same one German makes, and §14 lists it as a caveat.

**6. Data is modelled in `mesi.ivy`, dropped in the liveness files.** `mesi.ivy` carries
`cdata(C)` and `mem` so the safety theorem can include real data coherence. The liveness
files drop them: data appears in no guard, so deleting it is a sound abstraction for a
progress property.

**Hits are not modelled.** PrRd on S/E/M and PrWr on M change no state variable at all,
so they are not separate actions. (`pr_write_modified` exists only because, with data
modelled, a write to an M line does change `cdata`.) This is worth stating explicitly
because it is what makes the liveness property well-posed: a hit is served within the
single atomic step that issues it, never raises `waiting`, and so has nothing to prove.

---

## 4. The Ivy model, line by line

This section maps §2 onto `mesi.ivy` so that the code can be read without guessing.
`mesi_live.ivy` and `mesi_live_compassion.ivy` are the same model plus fairness
instrumentation (§7) and, in the FIFO file, timestamps.

The code below is quoted verbatim except that short `if`/`else` branches are put on one
line and the trailing comments are rewritten to point back at §2.

### 4.0 How to read an Ivy action

Five conventions cover everything in the file.

* **The model is a transition system.** A set of state variables, plus a set of
  parameterized actions. `export foo` declares that the environment may invoke `foo`
  with *arbitrary* arguments at *any* time; the reachable states are those produced by
  any interleaving of exported actions.
* **`require P` is an assumption on the environment,** not a check. In an exported
  action it prunes traces: calls that violate it simply do not happen, so the action is
  *disabled* when `P` is false. This is how the processor-side actions express "a PrRd
  miss only happens when the line is actually invalid".
* **`if G { B }` is a guarded command.** The action is always callable; when `G` is
  false, invoking it is a stutter step that changes nothing. This is how the protocol
  rules are written, and the difference from `require` is *enormous* for fairness — §7
  explains why, and it is the single most dangerous trap in this whole exercise.
* **`var f(C:client) : t` is a function** from `client` to `t` — an array indexed by
  cache. An assignment with a free capital-letter variable, such as
  `s.snoop_todo(C) := (C ~= cl);`, is a *simultaneous* update of the whole array.
* **`if some cl:client. P(cl) { B }`** binds `cl` to an arbitrary witness satisfying `P`
  and runs `B`; if no witness exists, `B` is skipped. This is how the arbiter picks a
  request. (`mesi_live.ivy` adds `minimizing s.reqts(cl)` to make the choice FIFO.)

`invariant` declarations are inductive invariants, checked by `ivy_check` at
initialisation and across every action.

### 4.1 The sorts

```ivy
finite type client                                              # the caches
type value                                                      # data values

type cstate = { invalid , shared , exclusive , modified }       # I, S, E, M  (§2.1)
type creq   = { noreq , busrd , busrdx }                        # bus requests (§2.2)
type dmsg   = { emptyd , snooprd , snooprdx ,                   # controller -> cache
                grantshared , grantexclusive , grantmodified }
type umsg   = { emptyu , acknocopy , ackhadcopy }               # cache -> controller
```

| Ivy value | §2 concept |
|---|---|
| `invalid`, `shared`, `exclusive`, `modified` | the four MESI states I, S, E, M |
| `busrd` | BusRd |
| `busrdx` | BusRdX **and** BusUpgr (decision 4 of §3) |
| `noreq`, `emptyd`, `emptyu` | "this channel is empty" |
| `snooprd`, `snooprdx` | the snoop broadcast of a BusRd / BusRdX reaching one cache |
| `grantshared`, `grantexclusive`, `grantmodified` | the transaction's answer: take the line in S, in E, or in M |
| `ackhadcopy` | the snoop response **asserting the shared line** (§2.2) |
| `acknocopy` | the snoop response leaving the shared line low |

`client` is `finite` because the relational rankings of the liveness proof need a finite
bound (Rule 5 of the method); it is faithful, since a machine has a fixed number of
caches. `value` is left uninterpreted — the proofs never look inside a value.

### 4.2 The state

```ivy
object s = {
    var chan_req(C:client)   : creq       # cache -> controller
    var chan_snoop(C:client) : dmsg       # controller -> cache (snoops AND grants)
    var chan_resp(C:client)  : umsg       # cache -> controller

    var cache(C:client) : cstate          # C's MESI state for the line
    var cdata(C:client) : value           # C's copy of the data
    var mem : value                       # main memory

    var ctl_cmd    : creq                 # noreq  <=>  the bus is idle
    var ctl_client : client               # requester of the current transaction
    var ctl_shared : bool                 # THE SHARED LINE (§2.2)
    var snoop_todo(C:client)  : bool      # C has not been sent its snoop yet
    var snoop_await(C:client) : bool      # C's response has not come back yet

    var waiting(C:client) : bool          # ghost: C has an unanswered request
}
```

The three channels realise decision 1 of §3; `chan_snoop` carrying two different kinds
of message realises decision 2.

The five controller variables are the whole "directory" — and note that they are
entirely *per-transaction*: `arbitrate` overwrites all of them, so nothing about who
holds the line survives from one transaction to the next. That is decision 3, and it is
the concrete sense in which this is a snooping rather than a directory protocol.

`snoop_todo` and `snoop_await` are the two halves of the broadcast:

```
snoop_todo(C)    C still has to be SENT its snoop
snoop_await(C)   C's answer still has to COME BACK     (snoop_todo ⊆ snoop_await)
```

so a cache moves `todo & await` → `await only` → neither as the pipeline advances. The
invariant `todo_sub_await` states the inclusion.

`waiting(C)` is **derived state**, not a real component of the protocol. The invariant
`waiting_stages` pins it as an `<->` to a disjunction over the channels and the
controller, so it carries no information that is not already in the rest of the state.
It earns its place twice over: it is the predicate the liveness property is stated in
terms of (§6), and `require ~s.waiting(cl)` in the three request actions is how
decision 5 of §3 ("caches block") is written. That `require` means `waiting` *is* read
by a guard and so does constrain the model — but only in a way that could equally be
written by inlining the `waiting_stages` disjunction.

### 4.3 The processor actions — §2.3 in code

Each row of the §2.3 table that has an observable effect is one action.

```ivy
# PrRd on I:  issue BusRd.
action pr_read_miss(cl:client) = {
    require ~s.waiting(cl);                 # decision 5: caches block
    require s.cache(cl) = invalid;          # "on I"  -- this is the miss
    require s.chan_req(cl) = noreq;         # the request channel is free
    s.chan_req(cl) := busrd;                # put BusRd on the bus
    s.waiting(cl)  := true;                 # ghost: an access is now outstanding
}
```

`pr_write_miss` is identical but writes `busrdx` (PrWr on I). `pr_write_upgrade` is
identical but requires `s.cache(cl) = shared` and also writes `busrdx` — that is BusUpgr,
merged with BusRdX by decision 4.

The interesting one is the row that makes MESI worth having:

```ivy
# PrWr on E: the SILENT upgrade.  No bus transaction, no waiting, no channel.
action pr_write_exclusive(cl:client, v:value) = {
    require s.cache(cl) = exclusive;
    s.cache(cl) := modified;
    s.cdata(cl) := v;
}
```

Compare it with `pr_write_upgrade` directly above: same intent (a store that needs write
permission), but from E it touches no channel, never sets `waiting`, and completes in
this one atomic step. That contrast *is* the E optimisation of §2.1, and it is why the
liveness property has nothing to say about this action (§6).

```ivy
# A cache may drop a line at any time; a dirty line is written back first.
action evict(cl:client) = {
    require s.cache(cl) ~= invalid;
    if s.cache(cl) = modified { s.mem := s.cdata(cl); };      # Flush (§1.5)
    s.cache(cl) := invalid;
}
```

Eviction is not part of the MESI tables — real caches evict because they are finite —
and it is included to show the results are robust to it. It only ever *removes* copies,
so it can threaten neither invariant, and it touches nothing the liveness ranking looks
at.

### 4.4 The controller actions — the transaction pipeline

```ivy
action arbitrate = {
    if s.ctl_cmd = noreq {                                  # the bus must be idle
        if some cl:client. s.chan_req(cl) ~= noreq {        # pick any queued request
            s.ctl_cmd        := s.chan_req(cl);             # BusRd or BusRdX
            s.ctl_client     := cl;
            s.chan_req(cl)   := noreq;                      # take it off the bus
            s.ctl_shared     := false;                      # shared line starts low
            s.snoop_todo(C)  := (C ~= cl);                  # BROADCAST to everyone
            s.snoop_await(C) := (C ~= cl);                  #   except the requester
        }
    }
}
```

The two array assignments are the broadcast of §1.4: *every* cache but the requester
must be snooped, because with no directory the controller does not know who holds the
line. `s.ctl_shared := false` arms the shared line for this transaction.

```ivy
action send_snoop(cl:client) = {
    if s.ctl_cmd ~= noreq & s.snoop_todo(cl) & s.chan_snoop(cl) = emptyd {
        if s.ctl_cmd = busrd { s.chan_snoop(cl) := snooprd; }
        else                 { s.chan_snoop(cl) := snooprdx; };
        s.snoop_todo(cl) := false;                          # sent; now awaiting
    }
}
```

Note the guard `s.chan_snoop(cl) = emptyd`. This is decision 2 doing its work: if `cl`
is still sitting on an undelivered grant, its downward channel is occupied and the snoop
*cannot* be sent. That single conjunct is what makes the protocol safe (§5.2) and what
creates liveness components [07]–[09] (§9).

```ivy
action recv_resp(cl:client) = {
    if s.ctl_cmd ~= noreq & s.chan_resp(cl) ~= emptyu {
        if s.chan_resp(cl) = ackhadcopy { s.ctl_shared := true; };   # SHARED LINE
        s.chan_resp(cl)   := emptyu;
        s.snoop_await(cl) := false;                         # this cache is done
    }
}
```

`ctl_shared` is thus the OR over all responses, accumulated one at a time — the wired-OR
of §2.2, serialised.

```ivy
action complete_rd = {
    if s.ctl_cmd = busrd
       & (forall I. ~s.snoop_await(I))                      # EVERY cache has answered
       & s.chan_snoop(s.ctl_client) = emptyd {
        if s.ctl_shared { s.chan_snoop(s.ctl_client) := grantshared; }
        else            { s.chan_snoop(s.ctl_client) := grantexclusive; };
        s.ctl_cmd := noreq;                                 # the bus is free again
    }
}
```

**This is the MESI decision** — the code realisation of "land in E if nobody else had a
copy, in S if somebody did" (§2.1, §2.3 row 1). The quantified guard
`forall I. ~s.snoop_await(I)` is what makes the shared-line sample meaningful: the
controller may only look at `ctl_shared` once *every* snooped cache has reported.

`complete_rdx` is the same shape without the choice: after a BusRdX every other cache is
in I, so the requester always gets `grantmodified`.

Two things to notice, both of which matter later. First, `ctl_cmd := noreq` happens in
the *same step* that posts the grant, so the bus becomes idle while the grant is still
in flight — a new transaction can start immediately, which is exactly the window §5.2 is
about. Second, the requester is never in `snoop_await` (it is excluded at `arbitrate`;
the invariant `await_not_req`), so no snoop can be sent down its channel and it stays
free for the grant (the invariant `req_chan_free`).

### 4.5 The cache-side actions — §2.4 in code

```ivy
action snoop_respond(cl:client) = {
    # --- BusRd snooped:  M -> S (Flush), E -> S, S -> S, I -> I ---
    if s.chan_snoop(cl) = snooprd & s.chan_resp(cl) = emptyu {
        if s.cache(cl) = invalid { s.chan_resp(cl) := acknocopy; }      # shared low
        else                     { s.chan_resp(cl) := ackhadcopy; };    # ASSERT shared
        if s.cache(cl) = modified { s.mem := s.cdata(cl); };            # Flush
        if s.cache(cl) ~= invalid { s.cache(cl) := shared; };           # downgrade
        s.chan_snoop(cl) := emptyd;
    };
    # --- BusRdX snooped:  M -> I (Flush), E -> I, S -> I, I -> I ---
    if s.chan_snoop(cl) = snooprdx & s.chan_resp(cl) = emptyu {
        if s.cache(cl) = invalid { s.chan_resp(cl) := acknocopy; }
        else                     { s.chan_resp(cl) := ackhadcopy; };
        if s.cache(cl) = modified { s.mem := s.cdata(cl); };            # Flush
        s.cache(cl)      := invalid;                                    # invalidate
        s.chan_snoop(cl) := emptyd;
    }
}
```

Line for line against the §2.4 table: the first `if` is the BusRd row, the second is the
BusRdX row, and within each, the first statement is "assert the shared line iff I have a
copy", the second is the Flush, and the third is the state change.

Three details worth pausing on:

* **The three inner `if`s must be in this order.** Ivy statements are sequential, so
  `if s.cache(cl) = modified { flush }` reads `cache(cl)` *before* the downgrade
  assignment. Moving the downgrade earlier silently loses every flush. This was
  checked rather than assumed: swapping the two `if`s makes `ivy_check` report exactly
  one failure, `data_coh ... FAIL`, with `swmr` still passing — i.e. the caches stay
  mutually exclusive but a reader can now observe a stale value, which is precisely the
  bug of §1.2 reintroduced.
* **The two outer `if`s are mutually exclusive** even though they are written
  sequentially: the first one sets `chan_snoop(cl) := emptyd`, so the second's guard
  cannot then hold. One action rather than two keeps the fairness instrumentation and
  the ranking components down to one apiece.
* **`s.chan_resp(cl) = emptyu` in both guards** enforces the unit capacity of the
  upward channel.

```ivy
action recv_grant_exclusive(cl:client) = {
    if s.chan_snoop(cl) = grantexclusive {
        s.cache(cl)      := exclusive;      # install the line in E
        s.cdata(cl)      := s.mem;          # take the (flushed) current value
        s.chan_snoop(cl) := emptyd;         # free the channel  <-- unblocks snoops
        s.waiting(cl)    := false;          # ghost: the access is served
    }
}
```

`recv_grant_shared` and `recv_grant_modified` are identical modulo the state installed.
The line `s.waiting(cl) := false` is the *goal* of the liveness property: this is the
one place, together with its two siblings, where an outstanding access is discharged.
And `s.chan_snoop(cl) := emptyd` is why these three actions appear *twice* in the
liveness ranking — once as stage 3 for the tracked cache ([01]–[03]) and once as the
"stale grant drain" that unblocks somebody else's transaction ([07]–[09]).

### 4.6 The §2.5 scenario, traced through the code

Two caches `0` and `1`, both `invalid`, `mem = v0`, bus idle. Each row is one action.

| # | action invoked | effect on the state |
|---|---|---|
| 1 | `pr_read_miss(0)` | `chan_req(0) := busrd`, `waiting(0) := true` |
| 2 | `arbitrate` | picks `cl = 0`: `ctl_cmd := busrd`, `ctl_client := 0`, `chan_req(0) := noreq`, `ctl_shared := false`, `snoop_todo(1) := snoop_await(1) := true` |
| 3 | `send_snoop(1)` | `chan_snoop(1) := snooprd`, `snoop_todo(1) := false` |
| 4 | `snoop_respond(1)` | `cache(1) = invalid`, so `chan_resp(1) := acknocopy`; no flush, no downgrade; `chan_snoop(1) := emptyd` |
| 5 | `recv_resp(1)` | response is `acknocopy`, so **`ctl_shared` stays false**; `snoop_await(1) := false` |
| 6 | `complete_rd` | all answered and `~ctl_shared` ⇒ `chan_snoop(0) := grantexclusive`; `ctl_cmd := noreq` |
| 7 | `recv_grant_exclusive(0)` | `cache(0) := exclusive`, `cdata(0) := v0`, `waiting(0) := false` |
| 8 | `pr_write_exclusive(0, v1)` | `cache(0) := modified`, `cdata(0) := v1` — **no bus transaction** |
| 9 | `pr_read_miss(1)` | `chan_req(1) := busrd`, `waiting(1) := true` |
| 10 | `arbitrate` | picks `cl = 1`: `ctl_client := 1`, `snoop_todo(0) := snoop_await(0) := true` |
| 11 | `send_snoop(0)` | `chan_snoop(0) := snooprd` |
| 12 | `snoop_respond(0)` | `cache(0) = modified`: `chan_resp(0) := ackhadcopy`; **`mem := cdata(0) = v1`** (Flush); `cache(0) := shared` |
| 13 | `recv_resp(0)` | response is `ackhadcopy` ⇒ **`ctl_shared := true`**; `snoop_await(0) := false` |
| 14 | `complete_rd` | `ctl_shared` ⇒ `chan_snoop(1) := grantshared`; `ctl_cmd := noreq` |
| 15 | `recv_grant_shared(1)` | `cache(1) := shared`, `cdata(1) := mem = v1`, `waiting(1) := false` |

Final state: `cache(0) = cache(1) = shared`, `cdata(0) = cdata(1) = mem = v1`. `swmr`
holds vacuously (no M or E copy) and `data_coh` holds (both clean copies equal memory).

Steps 6–8 are the E optimisation: one bus transaction bought a line that was then
written for free. Step 12 is why M needs a flush. Step 13 is the shared line deciding S
over E. Every other action in the file is one of these fifteen with different arguments.

---

## 5. The safety theorem

### 5.1 What is proved

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

### 5.2 The serialisation argument, and why unit-capacity channels are load bearing

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

This is captured by two invariants, and the ablation table (§12.3) confirms both are
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

### 5.3 Non-vacuity: the interesting states are reachable

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
| **a stale grant blocks a snoop** (the §5.2 window) | reachable |
| two clients queued at once, with distinct timestamps | reachable |

---

## 6. Formalising "every memory access is eventually served"

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
which is what the `l2s_not_all_done` machinery needs (German case study §6.5).

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
dropping it breaks 26 checks (§12.3).

---

## 7. Fairness encoding

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
  `l2s_progress` is not discounted by preemption — German case study §6.2.)

---

## 8. The arbiter is the entire difficulty

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

### 8.1 Why weak fairness alone is not enough, with the counterexample

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

## 9. Proof 1 — FIFO arbitration, weak fairness only (`mesi_live.ivy`)

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

By the asymmetry noted in §8 its guard is now stable, so `globally eventually wf_arb`
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
blocks the snoop the controller needs to send it (§5.2), so draining it is real work.
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

a purely first-order consequence of `waiting_stages`. The ablations in §12.2 confirm the
order is load bearing: demoting [00], or any stage-3 component, below the pipeline
breaks `l2s_needed_preserved[04..11]`, and switching to `l2s_auto5` breaks 16 checks.

---

## 10. Proof 2 — arbitrary arbitration under compassion (`mesi_live_compassion.ivy`)

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

## 11. The added safety invariants and where they came from

None were invented up front. The bookkeeping ones (`todo_sub_await` through `one_grant`, section A of `mesi.ivy`)
were written while
hand-checking the "something is always scheduled" premise; the coherence ones were
harvested from the safety CTIs.

| invariant | what it excludes | needed for |
|---|---|---|
| `waiting_stages` | a waiting client in no stage | `l2s_sched_exists`, and conservation for every pipeline ranking |
| `stage1_excl` | a queued request while an older one of the same client is in service | disjointness of the stages |
| `snoop_in_flight` | a snooped client "stuck outside the pipeline" | `l2s_sched_exists` — without it S4 has a hole |
| `grant_blocks` | a transaction completing while an undelivered grant is outstanding | **`swmr`** (§5.2) |
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

## 12. Non-vacuity: full ablation results

Every row below was produced by mutating a verifying file and re-running `ivy_check`.

### 12.1 `mesi_live.ivy` — parameters

| mutation | failing checks |
|---|---|
| `work_progress[i] := false`, each of i = 00…11 | 30–31 each, always including `l2s_progress[i]` and `l2s_progress_eventually[i]` |
| `work_helpful[i] := true`, each of i = 00,01,04,05,06,07,10,11 | `l2s_progress[i]` (1 check each) |
| drop `instantiate wfa_x`, each of the 9 | `l2s_progress[·]`, `l2s_progress_eventually[·]` for the components using it |
| delete component [i], each of i = 00…11 | 15–23 each |

The `work_helpful := true` rows are the decisive ones: they prove the schedulers are
essential rather than cosmetic, because a weak-fairness flag pulses even when its rule
no-ops.

### 12.2 `mesi_live.ivy` — structure

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

### 12.3 `mesi_live.ivy` — invariants

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

### 12.4 `mesi_live_compassion.ivy`

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
| **compassion replaced by weak fairness** | `l2s_sched_stable[01]` — see §8.1 |

---

## 13. What MESI taught that German did not

1. **A snooping protocol is easier to rank than a directory protocol, for a specific
   reason.** German's home carries `homeSharerList` across transactions, and *another
   client's grant grows it* while the tracked client is waiting. That is what forced the
   two-step proof with the `home_idle` lemma in `german_3channels_original.ivy`. Here
   the snoop set is snapshotted per transaction and only shrinks, so the pipeline
   rankings are grown by exactly one rule (`arbitrate`) — and that rule is precisely the
   one the higher components preempt. Both MESI proofs are therefore single `ranking`
   calls with no lemma, and both went through without a pipeline-conservation fight.

2. **Sharing one channel between snoops and grants pays for itself twice.** It is what
   makes safety work (§5.2) and it is what creates components [07]–[09]. A model with
   separate snoop and grant channels would need a different exclusivity argument.

3. **The MESI shared line is the one piece of genuinely new safety reasoning.** Granting
   E requires knowing that *every* other cache answered "no copy" and *stayed* without
   one; that is the chain `nocopy_means_invalid` → `rd_nocopy` → `excl_grant_alone` →
   `swmr`, and it has no analogue in German, which has no E state.

4. **Three grant flavours means three stage-3 components and three drain components.**
   The cost of the E state in the liveness proof is exactly six components rather than
   four; nothing structural changes.

5. **The "weak fairness is not enough" claim can be pinned to a single check.** §8.1.
   Reducing the argument to one failing premise with a two-client CTI is a better
   artifact than a paragraph of prose, and is worth doing for any protocol whose
   liveness rests on an arbitration assumption.

---

## 14. Caveats, stated plainly

1. **The two liveness theorems are incomparable.** `mesi_live.ivy` is about a home that
   implements FIFO arbitration. `mesi_live_compassion.ivy` is about an arbitrary
   arbiter but assumes compassion for it. MESI as literally specified, with an
   arbitrary arbiter and only weak fairness, is not starvation-free — §8.1.
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
8. **§8.1 is an argument, not a mechanical refutation.** The CTI is machine-produced and
   is the inductive step, but Ivy has no LTL model checker, so "the property is false
   under weak fairness alone" is not machine-checked end to end.
9. **Mixed-sort components are untested.** Every component in both proofs is
   `(N:client)`, including ones whose δ ignores `N` (e.g. `work_needed[10](N) =
   ctl_cmd ~= noreq`). [00] in `mesi_live.ivy` was deliberately phrased over clients
   rather than timestamps to avoid mixing sorts in one `ranking` call.
