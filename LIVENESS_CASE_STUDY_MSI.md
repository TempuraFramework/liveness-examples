# Case Study: MSI Cache Coherence — Safety and Liveness in Ivy

*A complete record of modelling the MSI protocol over a split-transaction snooping bus,
proving coherence (SWMR + DVI), and then proving "every processor request eventually
receives a response" under two different fairness assumptions.*

Companion to `LIVENESS_GUIDE.md` (the method) and `LIVENESS_CASE_STUDY_GERMAN.md` (the
first protocol this method was applied to here). Where the German study records what
happened when the method met a directory protocol, this one records what changes when it
meets a **bus** protocol — and which parts of the German recipe turned out to be
protocol-specific rather than general.

---

## 0. Summary of artefacts

| File | What it is | Rule | Components | Fairness assumed | `ivy_check` |
|---|---|---|---|---|---|
| `msi.ivy` | the protocol + coherence (safety only) | — | — | — | OK, 377 checks, 3.7 s |
| `msi_worked_example.ivy` | a four-phase execution of the protocol, replayed against `msi.ivy` and checked step by step (§1.6, §2.7) | — | — | — | OK, 428 checks, 29 s |
| `msi_fifo.ivy` | liveness, **FIFO bus arbiter** | Rule 10 (`ranking`) | 9 | **weak fairness only** | OK, 1663 checks, 7.6 s |
| `msi_lex.ivy` | liveness, **arbitrary bus arbiter** | Rule 10 (`ranking`) | 10 | weak everywhere **+ compassion for the arbiter** | OK, 1771 checks, 9.1 s |

Both liveness files also carry the literal-phrasing corollary `[request_answered]`,
chained off `[live]` with Rule 7.

The two liveness results are **incomparable**, exactly as in the German suite:
`msi_lex.ivy` proves the property for MSI with the arbiter as literally specified
(nondeterministic) and therefore has to assume compassion; `msi_fifo.ivy` proves it for
an MSI whose bus arbiter is FIFO, and needs only weak fairness. Neither implies the
other.

**Toolchain.** `ivy_check` at `/home/ruijie/workplace/venv_ivy/bin/ivy_check`.

```bash
ivy_check msi.ivy                    # or msi_fifo.ivy / msi_lex.ivy
ivy_check msi_worked_example.ivy     # the narrated trace, re-proved
ivy_check debug=true trace=true <f>  # first failing check + its CTI
```

> **Operational note, learned the hard way.** `ivy_check` rewrites a *shared* ply parse
> table (`site-packages/ivy/ivy_parsetab.py`) on **every** invocation. Two concurrent
> `ivy_check` processes — yours, or another user's on the same machine — can therefore
> corrupt each other's parse, producing either `AttributeError: module 'ivy.ivy_parsetab'
> has no attribute '_tabversion'` or, much worse, a *silently truncated* output in which
> failing checks simply do not appear. Two ablation results in the first run of this
> study were wrong for exactly that reason. If you want to run checks in parallel, give
> each worker a private copy of the `ivy` package on `PYTHONPATH`; then nothing is shared.

---

## 1. The MSI protocol from first principles

*This section assumes no computer-architecture background. If you know what a cache
coherence protocol is, skip to §1.8, which is the only place a real modelling decision is
made.*

### 1.1 Why there is a protocol at all

A multiprocessor has several processors and one shared memory. Memory is slow — a few
hundred processor cycles — so each processor keeps a small private copy of the memory
locations it has been using recently. That private copy is a **cache**, and the unit it
copies is a **cache line** (a contiguous block of memory, typically 64 bytes; the size is
irrelevant here).

The moment you allow private copies of shared data, you have a distributed systems
problem:

```
   memory[x] = 0
   P1 caches x  ->  P1 has its own copy, value 0
   P2 caches x  ->  P2 has its own copy, value 0
   P1 writes x = 7 into its own copy
   P2 reads x   ->  reads its own copy, gets 0.    WRONG.
```

Nothing in the hardware forces P2's copy to be updated; the copies are genuinely separate
pieces of state that can silently diverge. A **cache coherence protocol** is the
distributed algorithm that prevents this divergence. MSI is the simplest one that works.

For a verification reader the useful framing is: **MSI is a readers–writers lock over a
broadcast medium, where the lock also carries the data.** Many processes may hold the
"read lock" on a line simultaneously; at most one may hold the "write lock", and it
excludes everybody. The protocol's job is to move permission between processes safely
(safety) and to make sure every process that asks for permission eventually gets it
(liveness). Both halves are exactly the kind of property this repository is about, which
is why MSI is worth doing.

**Scope.** We model **one line at one address**. Coherence is defined per address and the
per-address protocols are independent, so a single-line model is the standard abstraction:
an n-address machine is n independent copies of this state machine. What a single-line
model does *not* capture is capacity pressure between addresses (an eviction forced
because a different address needed the slot); we model eviction as nondeterministic
instead, which is strictly more general.

### 1.2 What "coherent" means, precisely

Coherence is usually defined by two conditions (Sorin, Hill & Wood, *A Primer on Memory
Consistency and Cache Coherence*, §2.3). Both are stated over the lifetime of a single
address, divided into **epochs**: maximal intervals during which the set of processors
with permission does not change.

**(i) Single-Writer / Multiple-Reader (SWMR).** At any point in time, for the address,
*either* exactly one processor may read and write it, *or* some number of processors may
read it and none may write. Never both. This is a mutual-exclusion property and it is what
makes the whole thing tractable: it says the machine is always in either a "one writer"
epoch or a "many readers" epoch.

**(ii) Data-Value Invariant (DVI).** The value of the location at the start of an epoch
equals its value at the end of the previous read–write epoch. In other words, SWMR alone
would let you satisfy the permission bookkeeping while handing out *stale data*; DVI is
what forbids that. Operationally it amounts to: **every valid copy anywhere in the machine
holds the most recently written value**, and that is the form we prove.

**Coherence is not consistency.** A memory *consistency* model (sequential consistency,
TSO, …) constrains the order in which operations to *different* addresses become visible.
Coherence constrains a *single* address. MSI gives coherence; it is a building block for,
not a substitute for, a consistency model. Nothing in this case study is about
consistency.

### 1.3 The three states, and why exactly three

Each cache tags its copy of the line with one of three states. Read them as *permissions*
plus a *cleanliness* bit:

| state | may read? | may write? | other copies may exist? | memory current? |
|---|---|---|---|---|
| **M**odified | yes | yes | **no** | **no** — this cache has the only good copy |
| **S**hared | yes | no | yes | yes |
| **I**nvalid | no | no | yes | — (this cache has nothing) |

Two facts fall straight out and are the safety properties we prove:

- **at most one cache is in M**, and if one is, every other cache is in I — this *is* SWMR;
- **memory is up to date exactly when no cache is in M** — this is what makes DVI
  provable, because it tells you where the good copy is at all times: in memory if nobody
  is in M, in the M cache otherwise.

Why three and not fewer: you need a state meaning "no permission" (I), a state meaning
"read permission, possibly shared" (S), and a state meaning "exclusive write permission"
(M). Why not more: richer protocols add states purely to avoid bus traffic — **E**xclusive
in MESI lets a cache that loaded a line nobody else has jump straight to M without
announcing it; **O**wned in MOESI lets a dirty cache keep serving readers without writing
back to memory. Neither changes what is provable, only how often the bus is used. MSI is
the minimal correct protocol, which is why it is the right one to verify first.

### 1.4 The bus, and snooping

All caches and the memory controller hang off one shared **bus** — a broadcast medium that
carries one transaction at a time. Two consequences do all the work:

1. **The bus serializes.** Because only one transaction is in progress at a time, every
   cache observes the same sequence of transactions in the same order. This global total
   order is what makes a coherence argument possible at all; a protocol without one (a
   directory protocol over a point-to-point network, like German) has to reconstruct the
   ordering itself, which is why German needs a home directory and MSI does not.
2. **Every cache listens to every transaction.** This is called **snooping**. A cache does
   not have to be told it holds a copy — it watches the bus, notices a transaction for an
   address it happens to be caching, and reacts. There is no directory, no sharer list, and
   no per-cache bookkeeping anywhere except in the cache itself.

An **arbiter** decides which waiting cache gets the bus next. The arbiter is where all the
interesting liveness questions live (§6): nothing in the protocol says it has to be fair.

### 1.5 The three bus transactions, and the snoop reactions

A cache that cannot satisfy its processor locally puts a request on the bus. There are
three, distinguished by what permission is being asked for and whether data is needed:

| transaction | issued when | asks for | needs data? |
|---|---|---|---|
| **BusRd** | processor reads, cache is in I | read permission | yes |
| **BusRdX** | processor writes, cache is in I | write permission | yes |
| **BusUpgr** | processor writes, cache is in S | write permission | **no** — it already has the data |

BusUpgr exists purely so an upgrading cache does not have to re-fetch bytes it already
holds. Note also that **BusUpgr can never find a cache in M**: the issuer is in S, so by
SWMR nobody is in M.

Every other cache snoops the transaction and reacts according to its own state:

| snooping cache is in | observes **BusRd** | observes **BusRdX** | observes **BusUpgr** |
|---|---|---|---|
| **M** | **Flush**; M → S | **Flush**; M → I | *(cannot occur)* |
| **S** | S → S (nothing) | S → I | S → I |
| **I** | I → I (nothing) | I → I | I → I |

**Flush** means: write the dirty line back to memory. It is required because the M cache
holds the only good copy — if it went to I (or let a reader proceed) without flushing, the
value would be lost. Flush is the only way dirty data ever reaches memory other than a
writeback eviction (§1.7).

Putting the two tables together gives the whole protocol. A cache's own processor drives
it *up* the permission lattice I < S < M, paying a bus transaction each time; other
caches' transactions drive it *down*, for free.

> Real MSI implementations also have **FlushOpt**, a cache-to-cache transfer that lets a
> snooping cache hand data straight to the requester instead of routing it through memory.
> It is a performance optimization with no effect on what is provable, and we omit it: in
> our model the M cache flushes to memory and the requester then reads memory. The value
> delivered is identical.

### 1.6 A worked example

Three caches `a`, `b`, `c`; memory initially holds `v0`. This trace is not
illustrative-only: it is checked, step by step, against the model in
`msi_worked_example.ivy` (§2.7), so every transition below is a real transition of the Ivy
file and every asserted state is proved by the SMT solver.

| phase | what happens | a | b | c | memory | `dirty` |
|---|---|---|---|---|---|---|
| start | cold | I | I | I | `v0` | false |
| **(1)** | a's processor reads → **BusRd**; b and c snoop, nothing to do | **S** `v0` | I | I | `v0` | false |
| **(2)** | b's processor reads → **BusRd**; a snoops, stays S | S `v0` | **S** `v0` | I | `v0` | false |
| **(3a)** | a's processor writes → **BusUpgr**; b snoops and invalidates | **M** `v0` | **I** | I | `v0` | **true** |
| **(3b)** | a stores `v1` locally — no bus traffic at all | M **`v1`** | I | I | `v0` — **now wrong** | true |
| **(4)** | c's processor reads → **BusRd**; a **Flushes** `v1` and downgrades | **S** `v1` | I | **S** `v1` | **`v1`** | **false** |

Note the gap between the last two columns at phase (3a). Memory still *happens* to hold the
right value there — a has permission to write but has not written yet — while `dirty` is
already true. `dirty` does not mean "memory differs from the truth"; it means "memory is no
longer *guaranteed* to hold the truth, because somebody is in M". That is the honest
invariant (`mem_clean`: `~dirty -> mem_val = last_val`, an implication in one direction
only), and it is what makes the bookkeeping sound: the protocol must be conservative,
because nothing in the bus fabric can observe when a's processor actually stores.

Phase (4) is the one to stare at. The write in (3b) touched nothing but `a`'s own cache —
no bus transaction, no memory update. It becomes visible to the rest of the machine only
because c's later BusRd *forces* a to flush. That is the entire trick of a writeback
coherence protocol, and it is why DVI is a non-trivial property: between (3b) and (4) the
value in memory is simply wrong, and correctness rests on the fact that nobody can read
memory without first making the M cache give up its copy.

Note also what phase (3a) shows about SWMR: a and b were *both* in S and a's transition to
M is precisely the moment the "many readers" epoch ends and a "one writer" epoch begins.
The invalidation of b is not an optimization; it is what makes SWMR true.

### 1.7 Eviction

Caches are finite, so a line eventually gets thrown out to make room. There are two cases,
and the asymmetry matters:

- **S → I is silent.** A shared copy is clean and identical to memory, so dropping it
  loses nothing and needs no announcement.
- **M → I requires a writeback.** A modified copy is the only good copy, so it must be
  written to memory before being dropped.

Eviction is not caused by anything in this protocol — it is caused by pressure from other
addresses, which a single-line model does not represent. We therefore model it as
nondeterministic: a cache may drop its line at any time. That is more permissive than
reality and so a stronger result.

### 1.8 The one substantive modelling decision: a split-transaction bus

Textbook MSI runs on an **atomic** bus: a transaction occupies the bus for one indivisible
cycle, during which every cache snoops and responds. Modelled that way, the entire
transaction is a single Ivy action, and "every request is eventually answered" collapses
into "the arbiter is eventually fair" — a one-line proof about one rule, and nothing to
learn.

That is also not what real machines do. Broadcasting to every cache and waiting for all of
them takes far too long to hold the bus for, so real designs use a **split-transaction**
bus: the request, the snoop responses, and the data response are separate bus events, and
other activity is interleaved between them. This is the model here. A transaction is a
pipeline of separately scheduled steps, with unit-capacity channels between the bus and
each cache:

```
reqchan(C) : cache -> bus    no_req | busrd | busrdx | busupgr        (requests)
snpchan(C) : bus   -> cache  no_snoop | snp_inv | snp_dgrade          (snoops)
                             | dat_shared | dat_modified              (responses)
rspchan(C) : cache -> bus    no_rsp | snp_ack                         (snoop acks)
```

and the bus tracks one transaction:

```
bus_cmd            the transaction in progress (no_req = the bus is idle)
bus_owner          the cache that issued it
pending_snoop(C)   C has not yet completed its snoop of this transaction
to_snoop(C)        the snoop to C has not even been sent yet
```

so a transaction is the following sequence, with arbitrary interleaving between steps:

```
bus_arbitrate     pick a queued request; every other cache now owes a snoop
send_snoop(C)     put the snoop in C's channel                     (once per C)
snoop_respond(C)  C applies the snoop and acknowledges             (once per C)
recv_ack(C)       the bus retires C's obligation                   (once per C)
bus_complete      all retired: send data/permission to the requester
recv_dat_*        the requester installs the line
```

**`snpchan` deliberately carries both the snoop sent to a bystander and the response sent
to the requester.** In real hardware both arrive on the same wires into the cache, and
that sharing is not a modelling convenience — it is what makes an *unconsumed response
block the next transaction's snoop*. If cache C was granted a line and has not yet taken
it, the bus physically cannot deliver C a snoop for the next transaction, so the next
transaction cannot complete until C drains its response. That blocking is a genuine stage
of the liveness argument (components `[06]`/`[07]`), and it is the exact analogue of
German's "a stale grant in `channel2_4` blocks the invalidate the home needs to send".

### 1.9 Two smaller modelling decisions

**Every cache is snooped, including invalid ones.** `bus_arbitrate` sets
`pending_snoop(C) := C ~= cl` — *everybody except the requester*, not "the caches that hold
the line". This is faithful to a broadcast bus: there is no directory, so the bus cannot
know who holds a copy, and a cache in I simply snoops and acks with nothing to do. It is
the main structural difference from German, where the home *does* keep a `homeSharerList`,
and it has a direct consequence for the proof (§8.1).

**A queued BusUpgr whose line is taken away is re-issued as a BusRdX.** A cache in S can
issue BusUpgr and then be invalidated by somebody else's BusRdX *before its own request is
picked*. At that point it no longer holds the data, so completing the upgrade would hand it
write permission over bytes it does not have. `snoop_respond` converts the pending request:

```ivy
if s.snpchan(cl) = snp_inv {
    s.st(cl) := invalid;
    if s.reqchan(cl) = busupgr { s.reqchan(cl) := busrdx; }
}
```

This is what real protocols do (it is the SM<sup>a</sup>d transient state in Sorin–Hill–Wood).
The alternative — blocking the invalidation until the upgrade completes — would be a
`require`-style assumption that quietly removes the interesting interleavings, and is
exactly the kind of thing that makes a liveness proof vacuous.

**Caches block until served** (`require ~s.waiting(cl)` on both request rules). At most one
request per cache is outstanding. This is standard for this class of model and it is
necessary: otherwise `waiting(C)` stops identifying a single request and the three-stage
decomposition of §4.1 collapses. It also corresponds to something real — a cache has a
bounded number of *miss status holding registers*, and one per line is the simplest case.
See §12.2.

### 1.10 Where the nondeterminism is — and therefore where liveness lives

Everything below is chosen adversarially by the environment, and the proofs must hold for
every choice:

| choice | made by |
|---|---|
| which cache issues a request, and when | the processors (`pr_read`, `pr_write`) |
| what value is written | the processor (`pr_store`) |
| when a cache drops its line | the replacement policy (`evict_*`) |
| **which queued request gets the bus next** | **the arbiter** (`bus_arbitrate`) |
| the order in which bystanders are snooped, respond, and are retired | the interleaving |

The fourth row is the one that matters. Every other rule, once enabled, *stays* enabled
until it fires, so ordinary weak fairness ("each rule is offered a turn infinitely often")
is enough to make it happen. The arbiter is different: its guard includes "the bus is
idle", and another cache's pick destroys that. A scheduler can offer cache C its turn
infinitely often and have the bus be busy every single time. This asymmetry is the whole
liveness story, and §6 works it out.

---

## 2. The Ivy model, line by line

This section maps §1 onto `msi.ivy` in full. By the end you should be able to read the
file without guessing.

### 2.1 Enough Ivy to read the file

`msi.ivy` is a **first-order transition system**. There are no processes, no threads and no
message queues in the language — there is a set of interpreted symbols (the state), a
formula describing the initial state, and a set of **actions**, each of which is a guarded
command describing one atomic transition.

| construct | meaning |
|---|---|
| `finite type cache` | an uninterpreted sort, asserted finite. The proofs hold for *every* finite number of caches; finiteness is what makes `work_created = true` a legitimate bound `R` in the ranking rules. |
| `type value` | an uninterpreted sort, no cardinality assumption. Proofs hold for all data. |
| `type busreq = { no_req, busrd, busrdx, busupgr }` | an enumerated sort: exactly these four distinct elements. |
| `var f(C:cache) : t` | a **function symbol** `cache -> t`. Read it as an array indexed by caches; `f(c)` is one cache's entry. |
| `var g : t` | a constant symbol — one global cell. |
| `object s = { ... }` | a namespace, nothing more. Its fields are written `s.f`. |
| `after init { ... }` | the initial state, as a sequence of assignments. |
| `action a(x:t) = { ... }` | one atomic transition, parameterized by `x`. |
| `export a` | the environment may invoke `a` with any arguments. **The system is the interleaving of all exported actions.** |
| `invariant [name] φ` | `φ` must hold in every reachable state; `ivy_check` proves it inductive. |

Four points of syntax and semantics that will otherwise trip you up:

**Free capitals are implicitly universally quantified.** In an invariant, `s.st(C) = modified
& C ~= D -> s.st(D) = invalid` means `forall C, D. …`. In an *assignment*, the same
convention gives a simultaneous update of the whole array: `s.pending_snoop(C) := C ~= cl;`
sets the entry of every cache at once — true for everyone except `cl`. That single line is
the "everybody else now owes this transaction a snoop" step of §1.8.

**Operators.** `~` is negation, `&` conjunction, `|` disjunction, `->` implication, `~=`
disequality.

**Statements are sequential.** `;` sequences, and later statements see the effect of earlier
ones. This matters in exactly two places in the file, both flagged below.

**`require` means two different things depending on who calls.** In an action invoked by the
environment (i.e. an `export`ed one, called from outside), `require` is an **assumption**:
traces that violate it are simply not considered. In an action invoked by another action
(`call foo(x)`), it is a **guarantee**: a proof obligation that the caller had better
establish. `msi.ivy` uses only the first sense — every `require` is a rule guard, and the
transition system is "any enabled rule may fire". `msi_worked_example.ivy` (§2.7) exploits
the second sense to prove a specific trace is executable.

### 2.2 The types

```ivy
finite type cache
type value

type busreq   = { no_req, busrd, busrdx, busupgr }
type snoopmsg = { no_snoop, snp_inv, snp_dgrade, dat_shared, dat_modified }
type rspmsg   = { no_rsp, snp_ack }
type cstate   = { invalid, shared, modified }
```

| sort | §1 concept |
|---|---|
| `cache` | the caches of §1.1; arbitrary finite number |
| `value` | the contents of the line; uninterpreted, so nothing depends on what values are |
| `busreq` | the three bus transactions of §1.5, plus `no_req` = "channel empty" / "bus idle" |
| `snoopmsg` | what the bus can send *into* a cache: a snoop (`snp_inv` = invalidate, `snp_dgrade` = downgrade), or a response (`dat_shared` = data + read permission, `dat_modified` = data + write permission), or nothing |
| `rspmsg` | the snoop acknowledgement, or nothing |
| `cstate` | the three MSI states of §1.3 |

Two things to notice. First, the "empty" element of each channel sort (`no_req`,
`no_snoop`, `no_rsp`) is what makes each channel **unit capacity**: a channel holds at most
one message because it is a single variable, and the empty value is how you say it holds
none. Second, there is no separate `snp_upgr`: BusRdX and BusUpgr both need bystanders to
invalidate, so they produce the same snoop (`snp_inv`) and differ only in what the
requester gets back.

### 2.3 The state

```ivy
object s = {
    var reqchan(C:cache) : busreq
    var snpchan(C:cache) : snoopmsg
    var snpval(C:cache)  : value
    var rspchan(C:cache) : rspmsg

    var st(C:cache)  : cstate
    var val(C:cache) : value

    var bus_cmd   : busreq
    var bus_owner : cache
    var pending_snoop(C:cache) : bool
    var to_snoop(C:cache) : bool

    var mem_val : value
    var dirty   : bool

    var waiting(C:cache) : bool
}

var owner    : cache
var last_val : value
```

| symbol | §1 concept | written by | in a guard? |
|---|---|---|---|
| `s.reqchan(C)` | C's outbound request slot (§1.8) | `pr_read`, `pr_write`, `bus_arbitrate`, `snoop_respond` | yes |
| `s.snpchan(C)` | the bus's channel *into* C — snoop **or** response (§1.8) | `send_snoop`, `snoop_respond`, `bus_complete`, `recv_dat_*` | yes |
| `s.snpval(C)` | the data riding with a `dat_*` message | `bus_complete` | no |
| `s.rspchan(C)` | C's snoop-acknowledgement slot | `snoop_respond`, `recv_ack` | yes |
| `s.st(C)` | C's MSI state (§1.3) | `snoop_respond`, `recv_dat_*`, `evict_*` | yes |
| `s.val(C)` | C's copy of the line | `pr_store`, `recv_dat_*` | no |
| `s.bus_cmd` | the transaction in progress; `no_req` = idle | `bus_arbitrate`, `bus_complete` | yes |
| `s.bus_owner` | who issued it | `bus_arbitrate` | yes |
| `s.pending_snoop(C)` | C still owes this transaction a snoop | `bus_arbitrate`, `recv_ack` | yes |
| `s.to_snoop(C)` | the snoop to C has not been *sent* yet | `bus_arbitrate`, `send_snoop` | yes |
| `s.mem_val` | memory (§1.1) | `snoop_respond` (Flush), `evict_modified` | no |
| `s.dirty` | memory is stale, i.e. somebody is in M | `snoop_respond`, `evict_modified`, `recv_dat_modified` | **no** |
| `s.waiting(C)` | C has an outstanding request (the MSHR of §1.9) | `pr_read`, `pr_write`, `recv_dat_*` | yes |
| `owner` | ghost witness: *which* cache is in M | `recv_dat_modified` | **no** |
| `last_val` | ghost: the most recently written value | `pr_store` | **no** |

`to_snoop` ⊆ `pending_snoop`: a cache that has not been sent its snoop certainly has not
completed it. Splitting the two is what gives the sweep three distinct stages (send →
respond → retire) rather than one, and therefore three ranking components.

**Three planes.** It is worth separating the state into three groups, because the proofs
treat them completely differently:

1. **Transport/control plane** — `reqchan`, `snpchan`, `rspchan`, `bus_cmd`, `bus_owner`,
   `pending_snoop`, `to_snoop`, `waiting`, `st`. These are read by guards; they decide what
   happens next.
2. **Data plane** — `val`, `snpval`, `mem_val`. These are carried around but **no guard ever
   branches on them**. The protocol moves data without ever looking at it.
3. **Auxiliary (proof-only)** — `dirty`, `owner`, `last_val`. Never read by any guard;
   present solely so the invariants can be written without quantifier alternation (§3.1).

A consequence worth stating because it is checkable: **no `work_needed`, `work_helpful` or
`work_progress` definition in either liveness proof mentions plane 2 or plane 3, or even
`st`.** The entire liveness argument lives in the transport plane. (The one occurrence of
the string `owner` inside a ranking is `s.bus_owner`, plane 1, not the ghost `owner`.) That
is why adding the data-value machinery to the model cost essentially nothing in the
liveness proofs.

### 2.4 The initial state

```ivy
after init {
    s.reqchan(C) := no_req;  s.snpchan(C) := no_snoop;  s.rspchan(C) := no_rsp;
    s.st(C) := invalid;
    s.bus_cmd := no_req;
    s.pending_snoop(C) := false;  s.to_snoop(C) := false;
    s.waiting(C) := false;
    s.dirty := false;
    s.mem_val := last_val;  s.val(C) := last_val;  s.snpval(C) := last_val;
}
```

Cold start: every cache invalid, all channels empty, the bus idle, memory clean. `last_val`
is an ordinary (ghost) variable that is never initialized to a specific element, so it
holds an arbitrary value of the uninterpreted sort `value`; assigning `s.mem_val :=
last_val` makes memory agree with it without committing to *which* value it is. That is how
you say "memory starts out holding some value, and that value is the latest write so far".

### 2.5 The processor-side actions

These four are the **environment**: they are the demand on the protocol. They keep `require`
guards and — in the liveness files — get no fairness flag, because we never want to force a
processor to issue a request.

**`pr_read` — the I + PrRd row of §1.5.**

```ivy
action pr_read(cl:cache) = {
    require ~s.waiting(cl);                                    # no outstanding miss
    require s.st(cl) = invalid & s.reqchan(cl) = no_req;       # a genuine read miss
    s.reqchan(cl) := busrd;                                    # queue a BusRd
    s.waiting(cl) := true;
}
```

Only the *miss* is modelled. A PrRd in S or M is a hit: it changes nothing, needs no bus
transaction, and is therefore not a transition of this system at all. Omitting hits is not
an abstraction — there is literally nothing to model.

**`pr_write` — the I + PrWr and S + PrWr rows.**

```ivy
action pr_write(cl:cache) = {
    require ~s.waiting(cl);
    require s.st(cl) ~= modified & s.reqchan(cl) = no_req;
    if s.st(cl) = shared { s.reqchan(cl) := busupgr; }         # S: has data, wants permission
    else                 { s.reqchan(cl) := busrdx;  };        # I: wants data and permission
    s.waiting(cl) := true;
}
```

The `if` is exactly the BusUpgr-vs-BusRdX distinction of §1.5, and it is the only place the
choice is made. `s.st(cl) ~= modified` is "this is a write miss": a write in M is a hit,
handled by `pr_store`.

**`pr_store` — the M + PrWr hit, and the only writer of data.**

```ivy
action pr_store(cl:cache, v:value) = {
    require s.st(cl) = modified;
    s.val(cl) := v;
    last_val := v;                                             # ghost
}
```

This is phase (3b) of the §1.6 trace: a write that touches nothing but the cache's own
copy — no bus traffic, no memory update. `last_val` is updated in the same atomic step so
that "the most recently written value" is always well defined; it is the right-hand side of
the DVI invariant and is never read by the protocol.

**`evict_shared` / `evict_modified` — §1.7.**

```ivy
action evict_shared(cl:cache) = {
    require ~s.waiting(cl) & s.st(cl) = shared;
    s.st(cl) := invalid;                                       # silent: clean copy
}

action evict_modified(cl:cache) = {
    require ~s.waiting(cl) & s.st(cl) = modified;
    s.mem_val := s.val(cl);                                    # writeback
    s.dirty := false;
    s.st(cl) := invalid;
}
```

The asymmetry of §1.7 in three lines: dropping S writes nothing; dropping M writes memory
first. `require ~s.waiting(cl)` says a cache does not drop a line it has an outstanding
request for — in real terms, the MSHR holds the line down until the miss completes.

### 2.6 The bus-side actions

These seven are the protocol proper, and they are the ones that get fairness flags in
`msi_fifo.ivy` / `msi_lex.ivy` (§5).

**`bus_arbitrate` — start a transaction.** This is the arbiter of §1.4 and §1.10.

```ivy
action bus_arbitrate(cl:cache) = {
    require s.bus_cmd = no_req & s.reqchan(cl) ~= no_req;      # bus idle, cl is queued
    s.bus_cmd := s.reqchan(cl);                                # the bus adopts cl's request
    s.reqchan(cl) := no_req;                                   # ... and cl's slot frees up
    s.bus_owner := cl;
    s.pending_snoop(C) := C ~= cl;                             # everybody else owes a snoop
    s.to_snoop(C) := C ~= cl;                                  # ... and none has been sent
}
```

Sequencing matters here: `s.bus_cmd := s.reqchan(cl)` must precede `s.reqchan(cl) :=
no_req`, or the bus would adopt an empty request. The last two lines are the broadcast of
§1.9: *every* cache except the requester is enrolled, regardless of what state it is in.

Note the shape of the guard: `bus_cmd = no_req` is the part another cache's pick can
falsify, and it is the single reason this rule is not weakly-fair-schedulable (§1.10, §6.1).

**`send_snoop` — deliver one snoop.**

```ivy
action send_snoop(cl:cache) = {
    require s.bus_cmd ~= no_req & s.to_snoop(cl) & s.snpchan(cl) = no_snoop;
    if s.bus_cmd = busrd { s.snpchan(cl) := snp_dgrade; }      # BusRd  -> downgrade
    else                 { s.snpchan(cl) := snp_inv;    };     # BusRdX/BusUpgr -> invalidate
    s.to_snoop(cl) := false;
}
```

The `if` is the column selector of the snoop table in §1.5. The guard conjunct
`s.snpchan(cl) = no_snoop` is where the shared-channel decision of §1.8 bites: if `cl` is
still sitting on an undelivered response, **this rule is disabled** and the whole
transaction waits. That is the stall that components `[06]`/`[07]` of the liveness proof
exist to break.

**`snoop_respond` — a bystander applies the snoop.** The busiest rule in the file; it is the
*row* selector of the §1.5 table.

```ivy
action snoop_respond(cl:cache) = {
    require (s.snpchan(cl) = snp_inv | s.snpchan(cl) = snp_dgrade) & s.rspchan(cl) = no_rsp;

    if s.st(cl) = modified {              # (a) Flush, for either kind of snoop
        s.mem_val := s.val(cl);
        s.dirty := false;
    };

    if s.snpchan(cl) = snp_inv {          # (b) invalidate
        s.st(cl) := invalid;
        if s.reqchan(cl) = busupgr {      #     ... and demote a queued upgrade (§1.9)
            s.reqchan(cl) := busrdx;
        }
    } else {                              # (c) downgrade
        if s.st(cl) = modified { s.st(cl) := shared; }
    };

    s.snpchan(cl) := no_snoop;            # (d) consume the snoop, emit the ack
    s.rspchan(cl) := snp_ack;
}
```

Reading it against the table:

- **(a)** covers both M rows at once — M must Flush whether it is being invalidated or
  merely downgraded. This is the *only* Flush in the protocol besides `evict_modified`.
- **(b)** is the BusRdX/BusUpgr column: M → I and S → I, and I → I falls out because
  assigning `invalid` to a cache already in I changes nothing. The nested `if` is the
  BusUpgr→BusRdX conversion of §1.9.
- **(c)** is the BusRd column: M → S, and S and I are left alone — which is why the
  assignment is guarded by `s.st(cl) = modified` rather than being unconditional.
- **(d)** is the same in all cases.

**Sequencing subtlety, and the second of the two places it matters:** block (c) tests
`s.st(cl) = modified` *after* block (a) has run. That is correct only because (a) writes
`mem_val` and `dirty` but deliberately does **not** write `st` — so (c) still sees the
original state. If (a) had cleared `st`, (c) would silently never fire.

**`recv_ack` — the bus retires one obligation.**

```ivy
action recv_ack(cl:cache) = {
    require s.bus_cmd ~= no_req & s.rspchan(cl) = snp_ack;
    s.pending_snoop(cl) := false;
    s.rspchan(cl) := no_rsp;
}
```

**`bus_complete` — everybody has acked; answer the requester and release the bus.**

```ivy
action bus_complete = {
    require s.bus_cmd ~= no_req
            & (forall I. ~s.pending_snoop(I))                  # the sweep is finished
            & s.snpchan(s.bus_owner) = no_snoop;               # the requester's channel is free
    s.snpval(s.bus_owner) := s.mem_val;                        # memory is current here -- see §3.2
    if s.bus_cmd = busrd { s.snpchan(s.bus_owner) := dat_shared; }
    else                 { s.snpchan(s.bus_owner) := dat_modified; };
    s.bus_cmd := no_req;
}
```

`forall I. ~s.pending_snoop(I)` is the synchronization point of the whole protocol: it is
what guarantees that by the time permission is handed out, every other cache has given up
whatever it had. The `if` maps BusRd to read permission and BusRdX/BusUpgr to write
permission. `s.bus_cmd := no_req` comes last, so the `if` still sees the transaction type.

Reading `s.mem_val` here is sound because of `mod_snooped` (§3.2): a cache in M always still
owes the current transaction a snoop, so the guard's `forall` implies nobody is in M, so
memory is current. BusUpgr is the interesting case — the requester already has the data, so
`snpval` is redundant for it, but harmless and correct: a cache in S holds exactly
`mem_val`.

**`recv_dat_shared` / `recv_dat_modified` — the requester installs the line.**

```ivy
action recv_dat_shared(cl:cache) = {
    require s.snpchan(cl) = dat_shared;
    s.st(cl) := shared;
    s.val(cl) := s.snpval(cl);
    s.snpchan(cl) := no_snoop;
    s.waiting(cl) := false;                                    # <- the liveness goal
}

action recv_dat_modified(cl:cache) = {
    require s.snpchan(cl) = dat_modified;
    s.st(cl) := modified;
    s.val(cl) := s.snpval(cl);
    s.snpchan(cl) := no_snoop;
    s.dirty := true;                                           # memory may now be stale
    owner := cl;                                               # ghost witness (§3.1)
    s.waiting(cl) := false;                                    # <- the liveness goal
}
```

These are the only two rules that lower `waiting`, so `~waiting(C)` becoming true *is* "C's
request has been answered" — which is what makes the liveness property of §4 well posed.
They are also the two rules that free `snpchan(cl)`, which is why they double as the
unblocking step for a stalled snoop (§1.8) and therefore appear **twice** in the ranking:
once as stage 3 for the tracked cache, once as the stale-response drain for everybody else.

### 2.7 The worked example, mechanically checked

`msi_worked_example.ivy` replays the §1.6 trace against this model:

```ivy
include msi

action worked_example(a:cache, b:cache, c:cache, v1:value) = {
    require a ~= b & b ~= c & a ~= c;
    require forall C. C = a | C = b | C = c;   # exactly three caches
    require v1 ~= last_val;
    require ...                                # and the state is the initial state
    var v0 := last_val;

    # ---- (1) a reads a cold line ----
    call pr_read(a);
    call bus_arbitrate(a);
    call send_snoop(b); call snoop_respond(b); call recv_ack(b);
    call send_snoop(c); call snoop_respond(c); call recv_ack(c);
    call bus_complete;
    call recv_dat_shared(a);
    ensure s.st(a) = shared & s.val(a) = v0 & ~s.dirty & s.mem_val = v0;
    ...
```

Because these are `call`s rather than environment invocations, every `require` inside the
called rules becomes a **proof obligation** (§2.1): Ivy re-proves at each step that the rule
was genuinely enabled. The `ensure`s are checked too. The file verifies `OK`, so the trace
in §1.6 is a real execution of the protocol, for every three-element `cache` type and every
pair of distinct values.

Three details the file makes concrete that the prose glosses over:

- **`require forall C. C = a | C = b | C = c`** is needed. Without it `cache` may have a
  fourth element `d`, `pending_snoop(d)` is never retired, and `bus_complete` is never
  enabled — `ivy_check` reports exactly that. A nice illustration that the model really is
  parameterized in the number of caches.
- **Each transaction costs three steps per bystander** (`send_snoop`, `snoop_respond`,
  `recv_ack`), so a four-phase trace on three caches is 41 `call`s: four transactions of
  ten steps each (1 request + 1 arbitration + 3 steps for each of the 2 bystanders +
  1 completion + 1 install), plus the one local store of phase (3b). On an
  atomic bus it would be five steps. That factor is the split-transaction decision of §1.8,
  and it is precisely the room in which the liveness argument has to work.
- **`ensure s.val(a) = v1 & s.mem_val = v0 & s.dirty`** after phase (3b) is the formal
  statement that memory is stale — and `ensure s.st(a) = shared & s.mem_val = v1 & ~s.dirty`
  immediately after `snoop_respond(a)` in phase (4) is the formal statement that the Flush
  repaired it.

---

## 3. The safety properties

The two halves of the definition of coherence set out in §1.2 are stated directly as Ivy
invariants:

```ivy
invariant [swmr] s.st(C) = modified & C ~= D -> s.st(D) = invalid
invariant [dvi]  s.st(C) ~= invalid -> s.val(C) = last_val
```

`last_val` is a ghost variable holding the most recently written value; it is written only
by `pr_store` (a write hit in M) and never read by the protocol. `[dvi]` is the pleasant
form — *every valid copy holds the latest value* — and it is worth noting that getting it
into that form is a modelling choice, not a given: the usual phrasing needs a case split
on whether memory is current.

### 3.1 The witness trick, and why it is not optional

The naive supporting invariant is

```
(forall C. s.st(C) ~= modified) -> s.mem_val = last_val
```

whose antecedent is a `forall` — i.e. an **existential in positive position**. That breaks
stratification and is precisely the shape `LIVENESS_GUIDE.md` §4.5 warns about. The fix is
the German `owner` idiom: carry an explicit witness.

```ivy
var owner : cache                       # ghost: the cache in state M, if any
invariant [mod_dirty]    s.st(C) = modified -> s.dirty & C = owner
invariant [dirty_owner]  s.dirty -> s.st(owner) = modified
invariant [shared_clean] s.st(C) = shared -> ~s.dirty
invariant [mem_clean]    ~s.dirty -> s.mem_val = last_val
```

Now "some cache is modified" is the *ground* term `s.dirty`, and every invariant in the
file is quantifier-alternation-free. `[swmr]` then follows from `mod_dirty` (uniqueness of
the M cache) plus `shared_clean` (no S alongside an M).

### 3.2 The invariants that make `bus_complete` correct

`bus_complete` writes `snpval(bus_owner) := mem_val`, so it needs `mem_val = last_val`,
i.e. `~dirty`, at that instant. The chain is:

```
mod_snooped:  bus_cmd ~= no_req & st(C) = modified
                -> C ~= bus_owner & pending_snoop(C) & rspchan(C) ~= snp_ack
```

so if the machine were dirty, `dirty_owner` would give `st(owner) = modified`, hence
`pending_snoop(owner)` — contradicting `bus_complete`'s guard `forall I. ~pending_snoop(I)`.
A modified cache always still owes the transaction in progress a snoop, therefore the
machine is clean by the time the response is assembled. This is the one place where a
safety argument and the liveness pipeline talk about the same fact.

Two more carry real weight:

| invariant | what it excludes |
|---|---|
| `one_grant` | two responses in flight at once (needed so `last_val` cannot move under an in-flight response) |
| `grant_clean` | a response in flight while some cache is in M (same reason: `pr_store` needs an M cache, so it is disabled exactly when a response is in flight) |

`msi.ivy` verified **on the first run**, 377 checks. Its 29 invariants are all inductive as
written; none were harvested from CTIs, because the split-transaction structure was
designed with the stage decomposition of §5 already in mind.

### 3.3 The states really are reachable

A safety proof about an unreachable state space proves nothing, so each interesting state
was probed by adding a deliberately false invariant and confirming it is *violated*:

| probe | result |
|---|---|
| a cache is waiting | reachable |
| a cache is in M / in S | reachable |
| two caches in S simultaneously | reachable |
| BusRd / BusRdX / BusUpgr on the bus | all reachable |
| `snp_dgrade` / `snp_inv` / `snp_ack` in flight | all reachable |
| memory dirty | reachable |
| **a cache queued while the bus serves someone else** | reachable — *the starvation scenario* |
| **a stale response in flight during another transaction** | reachable — *the blocking scenario* |
| **a queued BusUpgr with an invalidate in flight** | reachable — *the BusUpgr→BusRdX conversion of §1.9 really fires* |
| a modified cache being downgraded by a BusRd | reachable |
| a dirty cache whose value differs from memory | reachable — *`pr_store` really writes* |

The last three matter most: they are the states the liveness argument is *about*.

---

## 4. Formalizing "every request receives a response"

Same shape as German, and for the same reasons (`LIVENESS_CASE_STUDY_GERMAN.md` §2.1
explains why the obvious phrasings are vacuous for upgrades or stop short of delivery):

```ivy
explicit temporal property [live]
  forall C. globally (s.waiting(C) -> eventually ~s.waiting(C))
```

`waiting(C)` is a ghost bit raised exactly where a request is issued and lowered exactly
where the cache installs the line it asked for, so `~waiting(C)` is precisely "the access
completed". Both files also carry the literal phrasing as a corollary:

```ivy
explicit temporal property [request_answered]
  forall C. globally (s.reqchan(C) ~= no_req -> eventually ~s.waiting(C))
```

### 4.1 The three-stage decomposition

Everything rests on this, captured by the added invariant

```ivy
invariant [waiting_stages]
    s.waiting(C) <-> (s.reqchan(C) ~= no_req                              # stage 1
                      | (s.bus_cmd ~= no_req & s.bus_owner = C)           # stage 2
                      | s.snpchan(C) = dat_shared                         # stage 3
                      | s.snpchan(C) = dat_modified)
```

`waiting_stages` is what discharges "something is always scheduled" (S4 /
`l2s_sched_exists`): one scheduler family per stage, and the invariant says a waiting cache
is always in one of them. `stage1_excl` makes stages 1 and 3 disjoint; `owner_free` does
the same job for stage 2 and is also what makes `bus_complete` enabled the instant the last
ack arrives.

---

## 5. Fairness encoding

Every bus-side rule is a **guarded command** with its flag pulsed *before* the guard:

```ivy
action recv_ack(cl:cache) = {
    wf_ack(cl) := true;
    wf_ack(cl) := false;
    if s.bus_cmd ~= no_req & s.rspchan(cl) = snp_ack { ... }
}
invariant ~wf_ack(C)
```

so a turn offered to a disabled rule is a stutter step and `globally eventually wf_ack(C)`
is a satisfiable statement about the *scheduler*. The alternative — pulse, then `require`
the guard — is the vacuity trap of `LIVENESS_CASE_STUDY_GERMAN.md` §3.1: in an exported
action `require` prunes the trace, so the assumption silently strengthens into "this rule
*successfully executes* infinitely often", which can be unsatisfiable, and `ivy_check` will
happily report `OK`.

Seven `wf_*` flags, one per bus-side rule. The five processor-side actions
(`pr_read`, `pr_write`, `pr_store`, `evict_shared`, `evict_modified`) keep `require` guards
and get **no** fairness flag: they are the demand on the protocol, and we never want to
force them to happen. A `require` with no flag attached is harmless.

**Consequence used throughout:** a weak-fairness flag is not usable as a ranking's progress
condition on its own, because it pulses even when the rule no-ops. Every `work_helpful`
below therefore implies its rule's enabling guard — literally *is* the guard, in almost
every component.

---

## 6. Why the arbiter needs compassion (and the FIFO way out)

### 6.1 The stability audit

A rule needs only weak fairness if its guard, once true, stays true until the rule itself
fires. Checked by hand for all seven bus rules before writing any proof:

| rule | guard stable once enabled? | why |
|---|---|---|
| `bus_arbitrate(cl)` | **no** | another cache's pick falsifies `bus_cmd = no_req` |
| `send_snoop(C)` | yes | `to_snoop(C)` is cleared only here; a response occupying `snpchan(C)` is drained by `[06]`/`[07]` |
| `snoop_respond(C)` | yes | a snoop in `snpchan(C)` is consumed only here |
| `recv_ack(C)` | yes | an ack in `rspchan(C)` is consumed only here |
| `bus_complete` | yes | nothing re-arms `pending_snoop` while the bus is busy |
| `recv_dat_shared(C)` / `recv_dat_modified(C)` | yes | a response in `snpchan(C)` is consumed only here |

Exactly one row says "no", and it is the same row as in German. Under weak fairness the
scheduler must offer `bus_arbitrate(_C)` a turn infinitely often, but it may offer every
one of those turns while the bus is busy with somebody else; other caches cycle request →
service → request forever and the adversary never schedules `_C`'s turn in one of the
instants between transactions. **The property is false under weak fairness alone** — a
property of an arbiter that does not remember who is waiting, not an artefact of the
encoding. (See the caveat in §12.5: this is a hand argument, not machine-checked.)

`msi_lex.ivy` therefore assumes compassion, for the arbiter and nothing else:

```ivy
explicit temporal axiom [sf_arb]
  forall C. (globally eventually (s.bus_cmd = no_req & s.reqchan(C) ~= no_req))
            -> (globally eventually f_arb(C))
```

Abbreviate the antecedent `E(C)`. This does **not** assume the conclusion: `globally
eventually E(_C)` still has to be discharged, and that is the entire content of the
stage-1 argument.

### 6.2 The asymmetry, and `msi_fifo.ivy`

The instability is caused by the rule being *parameterized by the cache*. The guard of an
**unparameterized** arbiter — "the bus is idle and somebody is queued" — is stable, because
only a pick can falsify it. So `msi_fifo.ivy` timestamps requests and serves the oldest:

```ivy
action bus_arbitrate = {
    wf_arb := true; wf_arb := false;
    if s.bus_cmd = no_req {
        if some cl:cache. s.reqchan(cl) ~= no_req minimizing s.reqts(cl) { ... }
    }
}
```

and plain `globally eventually wf_arb` suffices. The price is paid in the model rather
than in the assumption.

---

## 7. The proofs

### 7.1 `msi_fifo.ivy` — nine components, no temporal operator anywhere

```
[00]       stage 1: queued requests at least as old as _C's           (highest)
[01],[02]  stage 3: _C installs the line it was sent
[03]..[08] stage 2: the bus's snoop sweep                             (lowest)
```

`[00]` is the CAV'24 "pending timestamps ≤ mine" ranking, carried over **caches** rather
than over timestamps:

```ivy
definition work_needed[00](N:cache)  = s.reqchan(N) ~= no_req & s.reqts(N) <= s.reqts(_C)
definition work_helpful[00](N:cache) = s.bus_cmd = no_req & s.reqchan(_C) ~= no_req
definition work_progress[00](N:cache)= wf_arb
```

Two payoffs from carrying it on caches: `work_created = true` stays a legitimate finite
bound (`finite type cache`, no `T <= clock` needed), and every component in the file has
the same sort, avoiding the untested mixed-sort case. The single supporting invariant is

```ivy
invariant [ts_below_clock] s.reqts(C) < clock
```

which is what makes the ranking shrink: a newly issued request gets `reqts = clock >
reqts(_C)` and can never join the set. Ablations confirm both halves are load-bearing —
dropping the `reqts(N) <= reqts(_C)` conjunct breaks conservation, and tightening it to
`<` breaks reduction (the arbiter may pick `_C` itself, which is then not in δ).

The sweep components `[03]`..`[08]` are a nested chain, each ranking on a superset of the
stages still to come:

| # | δ | ψ (= the rule's guard) | r |
|---|---|---|---|
| 03 | `pending_snoop(N)` | `rspchan(N) = snp_ack` | `wf_ack(N)` |
| 04 | `... & rspchan(N) ~= snp_ack` | snoop in `snpchan(N)`, `rspchan(N)` free | `wf_snoop(N)` |
| 05 | `to_snoop(N)` | `to_snoop(N) & snpchan(N) = no_snoop` | `wf_send(N)` |
| 06 | `pending_snoop(N) & snpchan(N) = dat_shared` | same | `wf_rds(N)` |
| 07 | `pending_snoop(N) & snpchan(N) = dat_modified` | same | `wf_rdm(N)` |
| 08 | `bus_cmd ~= no_req` | guard of `bus_complete` | `wf_cmpl` |

(all conjoined with `bus_cmd ~= no_req`; see §8.1 for why that conjunct is *not* doing the
work it does in German). Components `[06]`/`[07]` are easy to miss: a cache still holding
an unconsumed response **blocks the snoop the bus needs to send it**, so draining the stale
response is a genuine sweep stage.

### 7.2 Why it must be lexicographic

The sweep rankings are *grown* by `bus_arbitrate`, which starts a fresh transaction with
every other cache owing it a snoop — and that happens freely while `_C` sits in stage 1 or
stage 3. Under Rule 8 (`l2s_auto5`) there is no way to say "this ranking is allowed to grow
right now", which is what forced German's original proof to lift the pipeline out into a
separate `home_idle` lemma. Under Rule 10 it is legal: `bus_arbitrate` needs an idle bus,
and an idle bus plus `waiting(_C)` means — by `waiting_stages`, whose stage-2 disjunct
requires a busy bus — that `_C` is in stage 1 or stage 3, where `[00]` or `[01]`/`[02]` is
scheduled and preempts the sweep. Spelled out:

```
~pre([03]..[08])  /\  waiting(_C)   ==>   bus_cmd ~= no_req
```

The ablations confirm this is the load-bearing structure, not decoration: switching to
`l2s_auto5` fails 12 checks, demoting stage 1 fails 6, demoting stage 3 fails 6 — all of
them `l2s_needed_preserved` / `l2s_progress_made` on the sweep components.

### 7.3 `msi_lex.ivy` — ten components, with the tableau case split

Identical except that stage 1 splits into two components, following McMillan's
`strongfair.ivy` idiom for the symbolic tableau of `E`:

| # | case | δ | ψ | r |
|---|---|---|---|---|
| 00 | `E` finitely often, not finished | `eventually E` | `~(globally eventually E) & (eventually E)` | `~(eventually E)` |
| 01 | `E` infinitely often | `reqchan(_C) ~= no_req` | `(globally eventually E) & reqchan(_C) ~= no_req` | `f_arb(_C)` |

The third case — `E` never again — is handled by the sweep itself, and this is where the
auxiliary lemma would otherwise be needed. It comes out free: if `E` never happens again
while `_C`'s request is queued, then the bus is never idle again, so `[04]`..`[09]` are
*required*, and they drive the bus to `bus_complete` — which makes it idle. Contradiction.

Two idioms are mandatory here and both are easy to get wrong:

1. **`instantiate sf_arb with C = _C`**, not a bare `instantiate`. A temporal atom is
   created per *syntactic* formula, so `□◇f_arb(_C)` and `□◇f_arb(C)` are different
   propositions and Z3 will not equate them (German §6.7).
2. **The compassion axiom must be re-stated as an `invariant` inside the tactic block.**
   `instantiate` pins it at the *initial* state, but `l2s_progress_eventually[01]` is a
   postcondition checked at every state, and Ivy does not promote premises to invariants.
   The lift is sound (`□◇p` is insensitive to finite prefixes) and inductive from the local
   tableau constraints. Dropping that one line fails `l2s_progress[01]` and
   `l2s_progress_eventually[01]`.

---

## 8. What differed from German

This is the part worth carrying forward, because it shows which bits of the German recipe
were general and which were about that protocol.

### 8.1 The `bus_cmd ~= no_req` conjunct is redundant here — and the ablation said so

German's pipeline rankings all carry `homeCurrentCommand ~= empty1`, and removing it fails
6 checks. The same conjunct is written into the MSI sweep rankings, for the same stated
reason — but the ablation reports **STILL OK**. That is not a defect in the ablation; it is
a real structural difference, and it is worth being precise about:

- German's pipeline ranks on `homeSharerList(N)`, which is *directory state that persists
  across commands*. A sharer stays a sharer when the home goes idle, so without the
  conjunct the ranking is genuinely non-empty between commands and genuinely grows.
- MSI's sweep ranks on `pending_snoop(N)` / `to_snoop(N)`, which are *per-transaction*
  state. The invariant `pending_busy` (`pending_snoop(C) -> bus_cmd ~= no_req`) already
  makes the conjunct derivable, so writing it changes nothing.

The conjunct is kept in the files anyway, because it states the intent (these rankings are
about the transaction in progress) and because `[08]`'s ranking *is* `bus_cmd ~= no_req` and
cannot be dropped. But it is documented as redundant rather than claimed as load-bearing —
and `no_inv_pending_busy` failing `l2s_progress[04]` is the check that pins down *why* it
is redundant.

**General lesson:** when you copy a ranking from a previous proof, the ablation is what
tells you whether the conjunct you copied is doing work in the new setting. Two of this
study's conclusions changed after the ablations were re-run correctly.

### 8.2 No directory means no sharer list, and a shorter sweep

German needs seven pipeline components; MSI needs six, and they are simpler, because there
is nothing corresponding to `homeSharerList` to invalidate — `bus_arbitrate` snapshots
"everyone else owes me a snoop" and that set only shrinks. Correspondingly German needs
`excl_owner_is_sharer` and `inv_in_flight` to stop a sharer being "stuck outside the
pipeline"; MSI needs only

```ivy
invariant [not_stuck]
    s.pending_snoop(C) & ~s.to_snoop(C)
    -> s.snpchan(C) = snp_inv | s.snpchan(C) = snp_dgrade | s.rspchan(C) = snp_ack
```

which is the single fact that discharges S4 inside the sweep. Dropping it fails 13 ×
`l2s_sched_exists` and nothing else — the cleanest ablation in the study, and a good
illustration that `l2s_sched_exists` failures mean "a state of the pipeline is uncovered",
essentially always a missing safety invariant rather than a ranking bug.

### 8.3 Two grant messages, not two grant rules

German has `grantsharedRule` and `grantexclusiveRule` with *different* guards, so it needs
two components (`[09]`,`[10]`). MSI's `bus_complete` has one guard for all three
transaction types and only branches on the message it emits, so it needs **one** component.
The branch reappears one stage later, in the two stale-response drains `[06]`/`[07]` and the
two stage-3 components `[01]`/`[02]`, because `recv_dat_shared` and `recv_dat_modified` are
genuinely different rules with different fairness flags.

### 8.4 The data-value invariant is new

German's proof is about control state only. Carrying values costs a `type value`, four
extra state variables (`val`, `snpval`, `mem_val`, `dirty`), a ghost `last_val` and about
six invariants — and it is nearly free for the liveness proof, because no ranking mentions
a value and no scheduler mentions `st`. It buys the actual definition of coherence rather
than just mutual exclusion on the M state. Recommended.

---

## 9. Non-vacuity: full results

Every row below was produced by mutating a verifying file and re-running `ivy_check`.
"STILL OK" would mean the mutated parameter was not load-bearing.

### 9.1 `msi_fifo.ivy`

| mutation | failing checks |
|---|---|
| **arbitrary arbiter instead of `minimizing s.reqts(cl)`** | `l2s_progress[00]` — *the starvation scenario, caught by the checker* |
| `[00]` without the `reqts(N) <= reqts(_C)` bound | 2 × `l2s_needed_preserved[00]` |
| `[00]` with `<` instead of `<=` | `l2s_progress[00]` |
| `ts_below_clock` removed | 2 × `l2s_needed_preserved[00]` |
| **`l2s_auto5` instead of `ranking`** | 12 × `l2s_progress_made[03..08]` |
| **stage 1 demoted to lowest order** | 6 × `l2s_needed_preserved[03..08]` |
| **stage 3 demoted below the sweep** | 6 × `l2s_needed_preserved[03..08]` |
| `not_stuck` removed | 13 × `l2s_sched_exists` |
| `waiting_stages` removed | 23 (`l2s_needed_preserved[03..08]`, …) |
| `pending_busy` removed | 8 (incl. `l2s_progress[04]`) |
| `stage1_excl` / `owner_free` / `grant_pending` / `mod_snooped` removed | 8 / 6 / 4 / 2 — *safety* invariants fail first |
| `work_progress[i] := false`, each `i` in 00..08 | 20–27 checks each |
| `work_helpful[i] := true`, each `i` in 00..08 | exactly 1 each: `l2s_progress[i]` |
| sweep δ without `bus_cmd ~= no_req` | **still OK** — see §8.1 |

### 9.2 `msi_lex.ivy`

| mutation | failing checks |
|---|---|
| **weak fairness for the arbiter instead of compassion** | `l2s_progress[01]` — *the starvation scenario, caught by the checker* |
| drop `instantiate sf_arb with C = _C` | 1 — the compassion `invariant` inside the block is no longer provable |
| **drop the compassion `invariant` inside the block** | 26 × `l2s_progress[01]`, `l2s_progress_eventually[01]` |
| delete the tableau component `[00]` | 19 (`l2s_needed_preserved[04..09]`, …) |
| **`l2s_auto5` instead of `ranking`** | 12 × `l2s_progress_made[04..09]` |
| **stage 1 demoted to lowest order** | 6 × `l2s_needed_preserved[04..09]` |
| **stage 3 demoted below the sweep** | 6 × `l2s_needed_preserved[04..09]` |
| `not_stuck` removed | 13 × `l2s_sched_exists` |
| `waiting_stages` removed | 23 (`l2s_needed_preserved[04..09]`, …) |
| `pending_busy` removed | 8 (incl. `l2s_progress[05]`) |
| `stage1_excl` / `owner_free` / `grant_pending` / `mod_snooped` removed | 8 / 6 / 4 / 2 — *safety* invariants fail first |
| `work_progress[i] := false`, each `i` in 00..09 | 20–27 checks each |
| `work_helpful[i] := true`, `i` in 02..09 | exactly 1 each: `l2s_progress[i]` |
| `work_helpful[i] := true`, `i` in 00..01 (the tableau pair) | 26 each: `l2s_progress[i]`, `l2s_progress_eventually[i]` |
| sweep δ without `bus_cmd ~= no_req` | **still OK** — see §8.1 |

---

## 10. Reproducing

```bash
ivy_check msi.ivy                 # safety: SWMR + DVI, 377 checks
ivy_check msi_worked_example.ivy  # the §1.6 trace, re-proved step by step
ivy_check msi_fifo.ivy            # liveness under weak fairness, FIFO arbiter
ivy_check msi_lex.ivy             # liveness under compassion, arbitrary arbiter
```

To run many checks in parallel, isolate each worker (see the note in §0):

```bash
cp -a <venv>/lib/python3.*/site-packages/ivy  $WORK/pylib1/ivy
PYTHONPATH=$WORK/pylib1 ivy_check file.ivy
```

---

## 11. Cheat sheet delta

Everything in `LIVENESS_CASE_STUDY_GERMAN.md` §12 applies unchanged. Additions from this
study:

- **Model the bus as split-transaction, not atomic**, or there is no liveness argument to
  make. Share one channel between snoops and responses: the resulting blocking is a real
  pipeline stage and it is where the interesting components come from.
- **Carry the data.** The data-value invariant costs ~6 invariants and a witness variable,
  is free for the liveness proof, and is the difference between proving coherence and
  proving mutual exclusion.
- **Use a ground witness (`owner`, `dirty`) for "some cache is in state X".** Writing it as
  `forall C. st(C) ~= modified` in an antecedent is an existential in positive position and
  will take you out of EPR.
- **Re-run ablations after fixing the ablation script.** A mutation that silently fails to
  apply reads exactly like "not load bearing".
- **Isolate `ivy_check` before running it concurrently.** It rewrites a shared parse table
  every run; racing it can silently swallow failing checks.

---

## 12. Caveats, stated plainly

1. **The two liveness results are incomparable.** `msi_lex.ivy` is conditional on
   compassion for the bus arbiter. `msi_fifo.ivy` is unconditional but only about a bus
   that implements FIFO arbitration. Neither implies the other.
2. **Cache blocking is a modelling assumption.** `require ~s.waiting(cl)` on the request
   rules is standard, but it is an assumption about the processor side, not something the
   protocol enforces. A cache that can pipeline requests is outside both proofs.
3. **`finite type cache`.** Both proofs rely on the cache universe being finite, which is
   what makes `work_created = true` a legitimate finite bound `R` (Rule 5). Unbounded
   caches would need timestamp-based rankings with `work_created(T) = T < clock`.
4. **Unit-capacity channels, one address.** This is the single-line model; a multi-address
   model would need the whole argument repeated per address, and a model with deeper
   channels would need per-message timestamps and a stage decomposition over messages
   rather than over caches.
5. **Not machine-checked: the claim that the property is false under weak fairness alone**
   for the arbitrary arbiter (§6.1). The ablation evidence shows the compassion assumption
   is *load-bearing in this proof*, which is weaker than showing the property is false.
   Ivy has no LTL model checker to settle it; bounded model checking on a 2- or 3-cache
   instance would be the way to confirm it.
6. **`~waiting(C)` means "served", not "served correctly".** The liveness property says the
   request completes; that the line it installs is coherent is what `[swmr]` and `[dvi]`
   say, and they are ordinary safety invariants proved separately.
7. **Mixed-sort ranking components are still untested.** As in the German study, every
   component here is `(N:cache)`, including ones whose δ ignores `N` (e.g.
   `work_needed[08](N) = bus_cmd ~= no_req`). `[00]` in `msi_fifo.ivy` was deliberately
   phrased over caches rather than timestamps to keep it that way.
