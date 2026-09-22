# Case Study: Modelling MOESI in Ivy and Proving It Live

*A directory-based MOESI cache coherence protocol, its safety (the state
compatibility table), and two liveness theorems — "every memory access is
eventually served" — proved with McMillan's relational lexicographic rankings.*

Companion to `LIVENESS_GUIDE.md` (the method) and
`LIVENESS_CASE_STUDY_GERMAN.md` (the same exercise for the German protocol).

**Who this is written for.** Someone who is comfortable with transition
systems, inductive invariants, EPR and temporal logic, and who has never
looked at a cache coherence protocol. Sections 1 and 2 assume no hardware
background at all: §1 explains MOESI from scratch, §2 maps every line of the
Ivy model onto §1. Sections 3–9 are the verification proper. A reader who
already knows MOESI can start at §2.2; a reader who already knows both MOESI
and the German case study can start at §3.

---

## 0. Artefacts

| File | What it proves | Rule | Components | Fairness assumed | `ivy_check` |
|---|---|---|---|---|---|
| `moesi.ivy` | safety: the MOESI compatibility table | — | — | — | OK, 289 checks, 2.2 s |
| `moesi_live.ivy` | `forall C. □(waiting(C) → ◇¬waiting(C))`, **FIFO arbiter** | Rule 10 (`ranking`) | 16 | weak fairness only | OK, 2867 checks, 8.8 s |
| `moesi_live_compassion.ivy` | same, **arbitrary arbiter** (MOESI as specified) | Rule 10 (`ranking`) | 17 | weak fairness + compassion for the arbiter | OK, 3011 checks, 8.4 s |
| `gen_moesi_compassion.py` | generates the third file from the second | — | — | — | — |

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

# Part I — The protocol

## 1. MOESI from first principles

### 1.1 The setting: a replicated store with a lock manager

Forget hardware for a moment. The system is a **replicated data store**:

* There is one data item — in hardware terms, one *cache line*, i.e. the
  contents of one aligned block of memory addresses.
* There is a **backing store** that always exists and always holds *some*
  value for the item: main memory.
* There are `n` **replica sites** — the caches. Each site may or may not
  currently hold a replica. Each site has a client attached to it (a CPU core)
  that issues reads and writes and expects them to be answered *locally*,
  because going to the backing store is two orders of magnitude slower.

The whole difficulty is the obvious one for any replicated store: if two sites
hold replicas and one of them writes, the other must not go on serving the old
value. A **cache coherence protocol** is the replication protocol that prevents
this. It works by handing out and revoking *permissions* — think leases — and
by tracking which replica, if any, is fresher than the backing store.

Here is the whole hardware vocabulary you need, translated:

| hardware term | what it means here |
|---|---|
| cache line | the one replicated data item |
| main memory / the backing store | the durable copy of last resort |
| cache / client / core | a replica site |
| cache state (M/O/E/S/I) | what permission this replica holds, and how it relates to the backing store |
| home directory | the coordinator / lock manager |
| probe | a message from the coordinator revoking or reducing a permission |
| **dirty** | this replica differs from the backing store — the backing store is stale |
| **clean** | this replica equals the backing store |
| write-back | pushing a dirty replica down to the backing store |
| read miss / write miss | the client wants to read/write and the local replica does not permit it |
| snooping bus | a broadcast medium on which every site sees every request |
| coherence | the consistency property of the replicated store |

### 1.2 What "coherence" means, and what we actually verify

The textbook definition of coherence is a statement about the *values* read:
every read of the item returns the value of the last write to it in some
global serialization of all accesses.

Protocols never enforce that directly. They enforce a much more structural
property, from which the value property follows, called the
**single-writer / multiple-reader (SWMR)** invariant:

> At every instant, *either* exactly one site has write permission and no other
> site holds a replica at all, *or* no site has write permission and any number
> of sites hold read-only replicas.

Plus a data invariant ("every valid replica holds the value of the most recent
write"). MOESI refines SWMR by distinguishing, among the read-only replicas,
which one — if any — is the *authority* whose value the backing store does not
have.

**What is verified in `moesi.ivy` is the permission half**: SWMR plus the
MOESI refinement, which together are exactly the compatibility table of §1.5.
The data half would need a value sort carried in the messages; it is not done
here (see §9, caveat 6). This is the standard division: the permission
invariant is the hard, protocol-specific part, and the data invariant is a
routine consequence of it once values are added.

### 1.3 A cache state records three facts

The five MOESI states are not five arbitrary labels. Each one is a conjunction
of answers to three questions:

1. **Permission** — may this site read? may it write? (`none`, `read`,
   `read+write`)
2. **Exclusivity** — is this site the only one holding a replica?
3. **Freshness** — is the backing store up to date, or is this replica dirty?
   And if it is dirty, whose job is the write-back?

| state | permission | other replicas? | backing store | who owes the write-back |
|---|---|---|---|---|
| **M** odified | read + write | none | **stale** | this site |
| **O** wned | read | possibly, all in S | **stale** | this site |
| **E** xclusive | read + write | none | up to date | nobody |
| **S** hared | read | possibly | up to date **unless** some site holds O | nobody |
| **I** nvalid | none | — | — | — |

The subtle row is **S**. In the simpler MSI and MESI protocols, "S" implies the
backing store is up to date. In MOESI that is no longer true: an S replica may
be stale with respect to memory, and that is *legal* precisely because some
other site holds O and has taken responsibility for the value. This single
relaxation is what MOESI buys and what its extra state pays for.

### 1.4 The five states, as assertions

Written as the assertion each state makes about the global configuration
(`C` is the site in that state, `D` ranges over the other sites):

```
M(C)  ≜  C may read and write     ∧  ∀D≠C. I(D)            ∧  memory is stale
O(C)  ≜  C may read               ∧  ∀D≠C. S(D) ∨ I(D)     ∧  memory is stale
                                  ∧  C is the authority for the value
E(C)  ≜  C may read and write     ∧  ∀D≠C. I(D)            ∧  memory is current
S(C)  ≜  C may read               ∧  ∀D≠C. ¬M(D) ∧ ¬E(D)
I(C)  ≜  C holds nothing
```

Two consequences worth stating explicitly, because they are what the proof
turns on:

* **M and E both assert sole ownership**, so a site in M or E excludes every
  other state except I. They differ only in freshness — and therefore only in
  what must happen when the permission is given up.
* **O is unique.** Two sites in O would be two authorities for one value; the
  protocol never creates a second one, because O is only ever produced by
  downgrading the unique M.

### 1.5 The compatibility table, and why it is *the* safety property

Collecting §1.4 gives the table on the MOESI Wikipedia page — which pairs of
states two *different* sites may hold simultaneously:

|  | M | O | E | S | I |
|---|---|---|---|---|---|
| **M** | — | — | — | — | ✓ |
| **O** | — | — | — | ✓ | ✓ |
| **E** | — | — | — | — | ✓ |
| **S** | — | ✓ | — | ✓ | ✓ |
| **I** | ✓ | ✓ | ✓ | ✓ | ✓ |

Reading the table back out: the only legal global configurations are

```
all I                         nobody has a copy
one E   + the rest I          one clean sole copy
one M   + the rest I          one dirty sole copy
k ≥ 1 S + the rest I          clean sharing (memory is current)
one O + k ≥ 0 S + the rest I  dirty sharing (memory is stale; O is the authority)
```

That last line is the MOESI-only configuration. Everything else MESI has too.

This table *is* the safety property: it is equivalent to SWMR plus O-uniqueness,
and everything a coherence protocol is for follows from it. It is stated
verbatim as four Ivy invariants in §3.1.

### 1.6 Why O exists, and why E exists

Both extra states over the minimal MSI protocol exist to remove a message
round-trip from a common access pattern.

**E removes the upgrade round-trip (MSI → MESI).** The commonest thing a
program does with a private variable is read it and then write it. In MSI, the
read miss is answered with S, and the subsequent write then needs a *second*
transaction to upgrade S → M, even though no other cache ever had a copy. MESI
notices at the time of the read that nobody else has the line and answers with
**E** instead: same read permission, but it also records "you are alone". The
later write is then a purely local `E → M` transition with **no messages at
all**. §2.5.1 shows exactly this trace in the model.

**O removes the write-back (MESI → MOESI).** Now the producer–consumer
pattern: site A writes the line (so A is in M and memory is stale), then site B
reads it. In MESI, A cannot simply become S, because "S" promises that memory
is current — so the line must be written back to memory as part of the
downgrade. That write-back is expensive, and on a multi-socket machine memory
may be several hops away. MOESI instead lets A go to **O**: A keeps the dirty
data, is marked as the authority, supplies the value to B directly
(cache-to-cache), and memory is simply left stale. The write-back is deferred
until the O line is finally evicted — and if the line keeps being handed
around, it may never happen at all. §2.5.2 shows this trace in the model.

So the one-line summary is: **MOESI = MESI + the ability to share a dirty
line**, and the O state is the bookkeeping that makes that safe by naming who
is responsible for it.

### 1.7 Keeping the states consistent: snooping vs directory, and probes

There are two implementation families.

* **Snooping.** All sites sit on a broadcast medium. Every request is seen by
  everybody, and each site reacts to other sites' requests by changing its own
  state. Simple, but every request costs a broadcast; it does not scale past a
  handful of sites. (`msi.ivy` in this repo is a snooping protocol, for
  contrast.)
* **Directory-based.** A coordinator — the **home directory** — keeps a
  *sharer list*: which sites currently hold a replica. A request goes to the
  home; the home sends point-to-point **probes** only to the sites that
  actually need to change state, waits for their acknowledgements, and then
  answers the requester. This is what real multi-socket machines do, and it is
  what we model.

A directory-based MOESI uses exactly two kinds of probe ("probe" is AMD's
term for these messages, and AMD's Opteron is the best-known MOESI
implementation):

| probe | means | effect at the target | acknowledgement |
|---|---|---|---|
| `invalidate` | "drop the line entirely" | M/O/E/S → **I** | `invalidateAck` |
| `downgrade` | "give up write permission, keep the data" | M → **O**, E → **S** | `downgradeAck` |

And the home answers a request with one of three **grants**, which is where
the requester's new state comes from:

| grant | new state at the requester | when the home issues it |
|---|---|---|
| `grantshared` | S | read request, some other replica exists |
| `grantexclusive` | E | read request, **no** replica anywhere |
| `grantmodified` | M | write request, after every replica has been invalidated |

Serving one request is therefore always the same three-phase pipeline:

```
   pick a queued request
     ↓
   probe everybody who has to change state        (invalidate, or downgrade)
     ↓
   collect their acknowledgements
     ↓
   grant
```

and which probe is used is determined by the request kind:

| request | what must change | probe | grant |
|---|---|---|---|
| write (`reqexclusive`) | every replica must go away | `invalidate` to every sharer | `grantmodified` → M |
| read (`reqshared`), line is writable somewhere | the writer must stop being a writer, but may keep the data | `downgrade` to the owner | `grantshared` → S |
| read, line is read-only-shared somewhere | nothing | — | `grantshared` → S |
| read, no replica anywhere | nothing | — | `grantexclusive` → E |

Note the asymmetry that makes MOESI interesting: a **write** request destroys
every replica, whereas a **read** request against a written line destroys
nothing — it converts M into O and leaves the data where it is.

### 1.8 The complete per-cache state machine

Every transition any single cache can make, and the rule in the Ivy model that
implements it:

| from | event | to | Ivy rule |
|---|---|---|---|
| I | this site's read served, no other replica existed | **E** | `receiveexclusiveGrantRule` |
| I | this site's read served, other replicas existed | **S** | `receivesharedGrantRule` |
| I | this site's write served | **M** | `receivemodifiedGrantRule` |
| **E** | this site's CPU writes | **M** | `writeExclusiveRule` — *silent, no messages* |
| **M** | `downgrade` probe (someone else is reading) | **O** | `clientdowngradesRule` |
| **E** | `downgrade` probe | **S** | `clientdowngradesRule` |
| M, O, E, S | `invalidate` probe (someone else is writing) | **I** | `clientinvalidatesRule` |

Two remarks.

* **S → M and O → M go through I in this model**, which is why the M row of
  the table above says only `I`. A cache in S or O *may* ask to write
  (`reqexclusiveRule` allows it), but the home then invalidates everybody on
  the sharer list — the requester included — before granting M, so the
  requester passes through I on the way. A real directory would answer an
  upgrade from a current sharer without invalidating it. Ours is simpler,
  still correct, and it is what the German model does; see §2.6.
* **There is no eviction and no write-back transition** (no `M → E`,
  no `O → S`, no silent `S → I`). Those are invisible in a model with no data
  values; see §9, caveat 6.

---

## 2. Reading the Ivy model

Everything in this section refers to `moesi.ivy`. The two liveness files
contain the same protocol verbatim, plus instrumentation described in §4.

### 2.1 Ivy in ten minutes, as used in these files

Ivy 1.8 describes a **first-order transition system**: a vocabulary of mutable
function and relation symbols, an initial-state constraint, and a set of
actions whose disjunction is the transition relation. `ivy_check` proves
invariants by ordinary induction (initiation + consecution), discharging each
verification condition with Z3 inside a decidable fragment.

| construct | meaning |
|---|---|
| `type client` | an **uninterpreted sort** — an arbitrary non-empty set. Everything proved holds for *any* number of caches. `finite type client` (in the liveness files) additionally asserts finiteness, which the ranking rule needs. |
| `type message1 = { empty1, reqshared, reqexclusive }` | an **enumerated sort**: exactly these three distinct elements, with the obvious disequalities available to the solver. |
| `object s = { ... }` | just a namespace. `s.cache`, `s.channel1`, … are the qualified names. |
| `var cache(C:client) : cachestate` | a mutable **function symbol** `client → cachestate`, i.e. a per-cache state variable. |
| `var homeSharerList(C:client) : bool` | a mutable **relation** on `client` — a set of caches. |
| `var homeexclusiveGranted : bool` | a mutable nullary symbol — a single global bit. |
| `after init { … }` | the initial-state assignment. Anything not assigned is arbitrary. |
| `s.channel1(C) := empty1` | in an assignment, a **capital free variable is implicitly universally quantified**: this sets `channel1` to `empty1` at *every* argument, simultaneously. |
| `action foo(cl:client) = { require G; body }` | a transition, parameterised by `cl`. |
| `require G` | in an **exported** action, an *assumption*: transitions where `G` is false simply do not exist. So `require` is how a guard is written in the safety model. |
| `export foo` | makes `foo` an environment-callable transition. The system's transition relation is "nondeterministically pick an exported action and arbitrary arguments, and run it". |
| `invariant [name] φ` | a candidate inductive invariant. Free capitals in `φ` are universally quantified. `ivy_check` proves the *conjunction* of all of them is inductive. |
| `exists I. …`, `forall I. …` | explicit quantifiers, used in guards. |

A worked example of the reading rules, `pickNewRequestRule`:

```ivy
action pickNewRequestRule(cl:client) = {
    require s.homeCurrentCommand = empty1 & s.channel1(cl) ~= empty1;
    s.homeCurrentCommand := s.channel1(cl);
    s.channel1(cl) := empty1;
    s.homeCurrentclient := cl;
    s.homeprobeList(C) := s.homeSharerList(C);
}
```

reads as: *for any `cl` such that the home is idle and `cl` has a request
queued, atomically — copy that request into the home's command register, clear
`cl`'s request slot, record `cl` as the client being served, and set the probe
list to the sharer list.*

Two reading rules are doing work there. Statements inside an action body run
**sequentially** — the whole body is one atomic transition, but the order of
the statements matters, which is why `homeCurrentCommand := s.channel1(cl)`
must come before the line that clears `channel1(cl)`. And within a *single*
assignment a capital free variable is universally quantified, so
`s.homeprobeList(C) := s.homeSharerList(C)` copies the whole relation at once.

The liveness files add temporal syntax (`globally`, `eventually`,
`explicit temporal axiom`, `explicit temporal property`, `proof { tactic … }`);
those are explained in §4 and in `LIVENESS_GUIDE.md`.

### 2.2 The sorts

```ivy
type client

type message1    = { empty1 , reqshared , reqexclusive }
type message2_4  = { empty2_4 , invalidate , downgrade ,
                     grantshared , grantexclusive , grantmodified }
type message3    = { empty3 , invalidateAck , downgradeAck }
type cachestate  = { invalid , shared , owned , exclusive , modified }
```

* `client` — the replica sites of §1.1. Uninterpreted, so the theorems are for
  an arbitrary number of caches.
* `cachestate` — the five states of §1.4, in that order. `owned` is the MOESI
  addition. Since the model carries permissions but no data values (§9,
  caveat 6), the clean/dirty distinction of §1.3 survives *only* as this
  label: `modified`/`owned` are the dirty states and `exclusive`/`shared` the
  clean ones, and nothing in the model can observe the difference. It still
  matters, because it is what decides the target of a downgrade.
* The three `message*` sorts are the contents of the three channels described
  next. Each has a distinguished `empty…` element meaning "this channel slot is
  free", which is how a **unit-capacity channel** is encoded: a channel is a
  single variable holding either a message or the empty marker.
* The name `message2_4` is inherited from the German benchmark, where the home
  has a separate channel 2 for invalidates and channel 4 for grants. Here they
  are merged into one unit-capacity channel per cache, so a grant in flight
  occupies the same slot a probe would need — which turns out to matter a great
  deal for liveness (§5, components [10]–[12]).

### 2.3 The state variables

```ivy
object s = {
    var channel1(C:client)   : message1      # cache -> home : requests
    var channel2_4(C:client) : message2_4    # home  -> cache : probes and grants
    var channel3(C:client)   : message3      # cache -> home : probe acks
    var cache(C:client)      : cachestate    # the MOESI state of each cache

    var homeSharerList(C:client)  : bool
    var homeprobeList(C:client)   : bool
    var homeexclusiveGranted      : bool
    var homeCurrentCommand        : message1
    var homeCurrentclient         : client
}
var owner : client
```

**The network.** Three unit-capacity, per-cache channels. `channel1(C)` is
`C`'s outstanding request, `channel2_4(C)` is the one message the home has in
flight towards `C`, `channel3(C)` is `C`'s outstanding acknowledgement. Unit
capacity is a real modelling restriction (§9, caveat 5) and it is also the
source of most of the protocol's blocking behaviour: the home cannot send a
probe to `C` while `C` still has an unconsumed grant sitting in
`channel2_4(C)`.

**The cache side.** `cache(C)` is literally the state machine of §1.8.

**The directory side**, item by item:

| variable | §1 meaning |
|---|---|
| `homeSharerList(C)` | the **sharer list**: the home believes `C` holds a replica (in any of S, O, E, M) |
| `homeexclusiveGranted` | the home has handed out **write permission** and has not yet been told it was surrendered |
| `owner` | *which* cache that is — and, after a downgrade, which cache holds the line in O |
| `homeCurrentCommand` | the request the home is serving right now; `empty1` means **idle**. Note it reuses the request sort `message1` as a register. |
| `homeCurrentclient` | who issued the request being served. Written `hcc` below. |
| `homeprobeList(C)` | `C` still has to be probed for the current command — the home's to-do list, re-snapshotted at every pick |

Two things about this encoding are worth dwelling on.

**`owner` is a witness variable, and that is a deliberate EPR move.** The
natural way to say "the writer is unique" is `∀C₁ C₂. writable(C₁) ∧
writable(C₂) → C₁ = C₂`, and the natural way to say "the writer is still a
sharer" is `∃C. writable(C) ∧ homeSharerList(C)`. Existentials inside
invariants create ∀∃ alternation, which is exactly what breaks stratification
and sends Z3 into non-termination (`LIVENESS_GUIDE.md` §4.5). Instead, `owner`
is an ordinary state variable, updated in the two rules that hand out write
permission, and every invariant that would have needed the existential
mentions the *ground term* `owner` instead — `excl_owner_is_sharer`,
`writable_is_owner`, `owned_is_owner`. `owner` is never read by a guard, only
by invariants, so it is a ghost variable in the usual sense.

**`owner` and `homeCurrentclient` are uninitialised.** `after init` does not
assign them, so they start as arbitrary clients. This is sound because every
invariant mentioning them is guarded by something false in the initial state
(`homeexclusiveGranted`, `cache(C) ≠ invalid`, `homeCurrentCommand ≠ empty1`).

**`homeexclusiveGranted` is *not* exactly "some cache is in E or M".** It is
"the home has not yet processed the surrender of write permission". The proved
direction is one-way (`writable_is_owner`): a cache in E or M implies the bit
is set. The converse fails in one window — after the owner has executed
`M → O` but before the home has consumed the `downgradeAck`. That window is
real and it is what forces the one awkward safety invariant in §3.3.

Likewise, `homeSharerList` **over-approximates** the set of caches actually
holding a replica. The proved direction is `valid_implies_sharer`
(`cache(C) ≠ invalid → homeSharerList(C)`); the converse fails transiently,
e.g. between a cache invalidating itself and the home consuming its ack. That
is normal for a directory and is exactly why probes must be acknowledged.

**Initial state.** All channels empty, all caches `invalid`, both lists empty,
no write permission, the home idle. Nothing is in flight and nobody has a copy
— the `all I` row of §1.5.

### 2.4 The rules, one group at a time

Sixteen actions, all exported. They divide into the seven groups of the
pipeline in §1.7.

#### (a) The client asks for something — §1.7 "request"

```ivy
action reqsharedRule(cl:client) = {                      # read miss
    require s.cache(cl) = invalid & s.channel1(cl) = empty1;
    s.channel1(cl) := reqshared;
}

action reqexclusiveRule(cl:client) = {                   # write miss or upgrade
    require (s.cache(cl) = invalid | s.cache(cl) = shared | s.cache(cl) = owned)
            & s.channel1(cl) = empty1;
    s.channel1(cl) := reqexclusive;
}
```

These model the *CPU*, not the protocol: they are where demand enters the
system, and they are deliberately unconstrained beyond what the states allow.
A read request is only issued from `invalid` (a cache in S, O, E or M can
already read locally — that is the point of those states). A write request is
issued from `invalid`, `shared` or `owned` — the three states that permit
reading but not writing. From `exclusive` no request is needed, which is the
next rule, and from `modified` nothing is needed at all.

`require … channel1(cl) = empty1` is unit-capacity flow control: one
outstanding request per cache.

#### (b) The E optimisation — §1.6

```ivy
action writeExclusiveRule(cl:client) = {
    require s.cache(cl) = exclusive;
    s.cache(cl) := modified;
}
```

The entire payoff of the E state, in three lines. **No channel is touched and
the directory is not informed** — `homeexclusiveGranted` already says this
cache may write, and `owner` already names it, so nothing the directory knows
becomes wrong. This is what "silent upgrade" means, and it is why a read miss
that finds no other copy is answered with E rather than S.

#### (c) The home accepts a request — §1.7 "pick"

```ivy
action pickNewRequestRule(cl:client) = {
    require s.homeCurrentCommand = empty1 & s.channel1(cl) ~= empty1;
    s.homeCurrentCommand := s.channel1(cl);
    s.channel1(cl) := empty1;
    s.homeCurrentclient := cl;
    s.homeprobeList(C) := s.homeSharerList(C);
}
```

The home serves **one request at a time**: the guard requires it to be idle,
and only the three grant rules set `homeCurrentCommand` back to `empty1`. The
last line computes the to-do list for this command by copying the whole sharer
list.

Why copying the whole sharer list is enough for *both* probe kinds: the probe
rules below filter it by the command type, and — crucially — when
`homeexclusiveGranted` holds, the invariant `excl_unique` says the sharer list
is the singleton `{owner}`, so for a read command the copied list *is* exactly
"the one cache that must be downgraded". One relation serves both phases.

Why the snapshot stays valid for the whole command: `homeSharerList` can only
*grow* in the three grant rules, and all three set `homeCurrentCommand :=
empty1` in the same step. So no cache can join the sharer list mid-command and
escape being probed. This fact is load-bearing for both safety and liveness.

*In the FIFO variant this rule becomes unparameterised and picks the oldest
queued request; see §6.1.*

#### (d) The home sends probes — §1.7 "probe"

```ivy
action sendinvalidateRule(cl:client) = {
    require s.channel2_4(cl) = empty2_4 & s.homeprobeList(cl)
            & s.homeCurrentCommand = reqexclusive;
    s.channel2_4(cl) := invalidate;
    s.homeprobeList(cl) := false;
}

action senddowngradeRule(cl:client) = {
    require s.channel2_4(cl) = empty2_4 & s.homeprobeList(cl)
            & s.homeCurrentCommand = reqshared & s.homeexclusiveGranted;
    s.channel2_4(cl) := downgrade;
    s.homeprobeList(cl) := false;
}
```

The two rows of the probe table in §1.7. They have identical shape and differ
only in the command they fire under and the message they send:

* a **write** command (`reqexclusive`) invalidates *everybody* on the list;
* a **read** command (`reqshared`) downgrades, and only when
  `homeexclusiveGranted` — i.e. only when somebody actually holds write
  permission. A read against a line that is merely shared needs no probe at
  all, which is the common case and the reason reads are cheap.

`require s.channel2_4(cl) = empty2_4` is the unit-capacity constraint again,
and it is the protocol's main source of *blocking*: if `cl` has not yet
consumed a grant from an earlier command, the home must wait. Taking that
constraint seriously is what forces ranking components [10]–[12] in §5.

Removing `cl` from `homeprobeList` in the same step is what makes "the home
has finished probing" expressible as `∀C. ¬homeprobeList(C)`, and what makes
the pipeline rankings shrink.

#### (e) The cache reacts to a probe — §1.8, the two probe rows

```ivy
action clientinvalidatesRule(cl:client) = {
    require s.channel2_4(cl) = invalidate & s.channel3(cl) = empty3;
    s.channel2_4(cl) := empty2_4;
    s.channel3(cl)   := invalidateAck;
    s.cache(cl)      := invalid;
}

action clientdowngradesRule(cl:client) = {
    require s.channel2_4(cl) = downgrade & s.channel3(cl) = empty3;
    s.channel2_4(cl) := empty2_4;
    s.channel3(cl)   := downgradeAck;
    if s.cache(cl) = modified {
        s.cache(cl) := owned;          # dirty sharing: no writeback
    } else if s.cache(cl) = exclusive {
        s.cache(cl) := shared;         # clean
    }
}
```

**`clientdowngradesRule` is the MOESI protocol.** Everything else in this file
is machinery that MESI would also need. The three-way case is exactly §1.6:

* from `modified` — the data is dirty, so it cannot become S (S promises
  memory is current). It becomes **`owned`**: keep the dirty value, keep read
  permission, become the named authority. *No write-back is performed.*
* from `exclusive` — the data is clean, so plain `shared` is correct and the
  O state is not needed.
* otherwise the cache state is left alone. This branch is reachable: the
  directory can be probing a cache whose copy has already gone (the directory
  over-approximates, §2.3), and silently "restoring" it to `shared` would be
  wrong — the cache does not have the data.

Both rules consume the probe and post an acknowledgement in the same atomic
step; the guard `channel3(cl) = empty3` is unit capacity on the ack channel,
and it is always satisfiable here thanks to the invariant `no_overlap`
("a cache never has a probe pending *and* an ack outstanding").

#### (f) The home collects acknowledgements — §1.7 "collect"

```ivy
action receiveinvalidateAckRule(cl:client) = {
    require s.homeCurrentCommand ~= empty1 & s.channel3(cl) = invalidateAck;
    s.homeSharerList(cl) := false;
    s.homeexclusiveGranted := false;
    s.channel3(cl) := empty3;
}

action receivedowngradeAckRule(cl:client) = {
    require s.homeCurrentCommand ~= empty1 & s.channel3(cl) = downgradeAck;
    s.homeexclusiveGranted := false;
    s.channel3(cl) := empty3;
}
```

The difference between the two is the whole reason MOESI needs two pipelines
in the liveness proof:

* an **invalidate** ack removes `cl` from the sharer list *and* clears write
  permission;
* a **downgrade** ack clears write permission and **leaves `cl` on the sharer
  list** — because `cl` still has the data, now in O (or S). That is the point
  of the O state, and it means the "sharer list shrinks" ranking cannot
  possibly measure progress of a downgrade. Hence a second ranking chain
  measuring `homeexclusiveGranted` instead (§5, components [07]–[09]).

Clearing `homeexclusiveGranted` unconditionally in the invalidate case is
sound because when an `invalidateAck` is outstanding and write permission is
held, the acknowledging cache must be the owner — that is what
`invalidateAck_in_channel` together with `excl_unique` gives.

#### (g) The home grants — §1.7 "grant"; each of these ends the command

```ivy
action grantsharedRule = {                              # read, others have it -> S
    require s.homeCurrentCommand = reqshared
            & ~s.homeexclusiveGranted
            & (exists I. s.homeSharerList(I))
            & s.channel2_4(s.homeCurrentclient) = empty2_4;
    s.homeSharerList(s.homeCurrentclient) := true;
    s.homeCurrentCommand := empty1;
    s.channel2_4(s.homeCurrentclient) := grantshared;
}

action grantexclusiveRule = {                           # read, nobody has it -> E
    require s.homeCurrentCommand = reqshared
            & (forall I. ~s.homeSharerList(I))
            & s.channel2_4(s.homeCurrentclient) = empty2_4;
    s.homeSharerList(s.homeCurrentclient) := true;
    s.homeexclusiveGranted := true;
    s.homeCurrentCommand := empty1;
    s.channel2_4(s.homeCurrentclient) := grantexclusive;
    owner := s.homeCurrentclient;
}

action grantmodifiedRule = {                            # write, all invalidated -> M
    require s.homeCurrentCommand = reqexclusive
            & (forall I. ~s.homeSharerList(I))
            & s.channel2_4(s.homeCurrentclient) = empty2_4;
    s.homeSharerList(s.homeCurrentclient) := true;
    s.homeexclusiveGranted := true;
    s.homeCurrentCommand := empty1;
    s.channel2_4(s.homeCurrentclient) := grantmodified;
    owner := s.homeCurrentclient;
}
```

These are the three rows of the grant table in §1.7, and their guards encode
"the probing phase is over":

* `grantsharedRule` — the read case with other replicas around. `~homeexclusiveGranted`
  is the "downgrade completed" condition: either nobody held write permission
  to begin with, or the downgrade ack has been processed. `exists I.
  homeSharerList(I)` distinguishes it from the next rule. The requester joins
  the sharer list and gets S.
* `grantexclusiveRule` — the read case with **no** replica anywhere, so E is
  handed out: write permission is recorded (`homeexclusiveGranted := true`,
  `owner := hcc`) even though the requester only asked to read. That is the
  whole E optimisation, made concrete: the directory pre-authorises the write
  so that `writeExclusiveRule` can later be silent.
* `grantmodifiedRule` — the write case. `forall I. ~homeSharerList(I)` is
  "every replica has been invalidated and every ack collected". Only then is
  M handed out.

The two `grant*` rules that hand out write permission are the only writers of
`owner`, which is what makes the witness discipline of §2.3 work.

`channel2_4(hcc) = empty2_4` in all three is, once more, unit capacity: the
home cannot deliver the grant until the requester's inbound slot is free.

#### (h) The requester consumes the grant — §1.8, the three grant rows

```ivy
action receivesharedGrantRule(cl:client) = {
    require s.channel2_4(cl) = grantshared;
    s.cache(cl) := shared;
    s.channel2_4(cl) := empty2_4;
}

action receiveexclusiveGrantRule(cl:client) = {
    require s.channel2_4(cl) = grantexclusive;
    s.cache(cl) := exclusive;
    s.channel2_4(cl) := empty2_4;
}

action receivemodifiedGrantRule(cl:client) = {
    require s.channel2_4(cl) = grantmodified;
    s.cache(cl) := modified;
    s.channel2_4(cl) := empty2_4;
}
```

The access is complete exactly here. In the liveness files these three rules
additionally lower the ghost bit `waiting(cl)` — that is the "response" the
liveness property is about (§4).

### 2.5 Three complete executions

The first two were produced by `ivy_check`'s bounded model checker — append
`attribute method = bmc[k]` and assert the target configuration as a false
invariant, and the counterexample *is* the trace. The third is constructed by
hand, with each step's guard checked against §2.4; it is marked as such. Two
caches, `0` and `1`.

#### 2.5.1 The E optimisation: a read miss that costs one round trip and a free write

```
call reqsharedRule(0)              channel1(0) := reqshared
call pickNewRequestRule(0)         cmd := reqshared, hcc := 0, probeList := {} (no sharers)
call grantexclusiveRule            forall I. ~sharerList(I) holds  ->  E, not S
                                   sharerList(0) := true, eG := true, owner := 0
                                   channel2_4(0) := grantexclusive, cmd := empty1
call receiveexclusiveGrantRule(0)  cache(0) := exclusive
```

Four steps, no probes — nobody had a copy, so there was nobody to probe. Now
`writeExclusiveRule(0)`'s guard `cache(0) = exclusive` holds, so cache 0 can
move to `modified` **with no further messages of any kind**. Under MSI the
same sequence would have ended in S and the write would have needed a second
full request/grant round trip.

#### 2.5.2 Dirty sharing: M → O, and the write-back that does not happen

The eleven-step trace `bmc[14]` produces for the assertion
`~(C1 ≠ C2 ∧ cache(C1) = owned ∧ cache(C2) = shared)`:

| # | step | what changes |
|---|---|---|
| 1 | `reqexclusiveRule(1)` | `channel1(1) := reqexclusive` |
| 2 | `pickNewRequestRule(1)` | `cmd := reqexclusive`, `hcc := 1`, probe list empty (no sharers yet) |
| 3 | `reqsharedRule(0)` | `channel1(0) := reqshared` — **queued while the home is busy** |
| 4 | `grantmodifiedRule` | no sharers to invalidate, so straight to the grant: `sharerList(1) := true`, `eG := true`, `owner := 1`, `channel2_4(1) := grantmodified`, `cmd := empty1` |
| 5 | `pickNewRequestRule(0)` | `cmd := reqshared`, `hcc := 0`, `probeList := sharerList = {1}` |
| 6 | `receivemodifiedGrantRule(1)` | `cache(1) := modified` — cache 1 is now the sole dirty copy |
| 7 | `senddowngradeRule(1)` | read command + `eG` ⇒ downgrade, not invalidate: `channel2_4(1) := downgrade`, `probeList(1) := false` |
| 8 | `clientdowngradesRule(1)` | `cache(1) = modified` ⇒ **`cache(1) := owned`**, `channel3(1) := downgradeAck`. *No write-back.* |
| 9 | `receivedowngradeAckRule(1)` | `eG := false`; **cache 1 stays on the sharer list** |
| 10 | `grantsharedRule` | `~eG` and `∃I. sharerList(I)` (namely 1) ⇒ S: `sharerList(0) := true`, `channel2_4(0) := grantshared`, `cmd := empty1` |
| 11 | `receivesharedGrantRule(0)` | `cache(0) := shared` |

Final configuration: `cache(1) = owned`, `cache(0) = shared`, memory never
touched. This is the `one O + k S` row of §1.5 — the configuration MESI cannot
produce — and steps 7–9 are precisely where MESI would have written the line
back to memory instead.

Step 3 is also worth noticing on its own: cache 0's request sits in
`channel1(0)` across four steps while the home finishes cache 1's command.
That is the starvation shape the whole liveness half of this case study is
about (§4).

#### 2.5.3 A write destroys every replica, O included *(hand-constructed)*

Continuing from the configuration above (`cache(1) = owned`,
`cache(0) = shared`, `sharerList = {0,1}`, `eG = false`, home idle), cache 0
now wants to write. This one is not a BMC output — it is written out by hand
from the rules, with each guard checked against §2.4:

| # | step | what changes |
|---|---|---|
| 1 | `reqexclusiveRule(0)` | allowed from `shared`; `channel1(0) := reqexclusive` |
| 2 | `pickNewRequestRule(0)` | `cmd := reqexclusive`, `hcc := 0`, `probeList := {0,1}` |
| 3 | `sendinvalidateRule(1)` | write command ⇒ invalidate: `channel2_4(1) := invalidate` |
| 4 | `clientinvalidatesRule(1)` | `cache(1) := invalid`, `channel3(1) := invalidateAck` |
| 5 | `receiveinvalidateAckRule(1)` | `sharerList(1) := false` |
| 6 | `sendinvalidateRule(0)` | **the requester invalidates itself** (§1.8, §2.6) |
| 7 | `clientinvalidatesRule(0)` | `cache(0) := invalid`, `channel3(0) := invalidateAck` |
| 8 | `receiveinvalidateAckRule(0)` | `sharerList(0) := false` — the list is now empty |
| 9 | `grantmodifiedRule` | `sharerList(0) := true`, `eG := true`, `owner := 0`, `channel2_4(0) := grantmodified`, `cmd := empty1` |
| 10 | `receivemodifiedGrantRule(0)` | `cache(0) := modified` |

Note step 4: the O holder's dirty value is simply dropped. In a real machine
that value would have to reach the new writer (cache-to-cache transfer) or be
written back first. Because this model carries **permissions but no values**,
the distinction is invisible here — see §9, caveat 6. This is the clearest
single example of where the abstraction stops.

Steps 3–5 and 6–8 are the invalidation pipeline that ranking components
[04]–[06] measure; steps 1–2 and 9–10 are stages 1 and 3 of §4.1.

### 2.6 Modelling choices, and what each one costs

Three choices are inherited from `german_3channels_*.ivy` so the proofs can be
compared line by line.

1. **`homeprobeList := homeSharerList` at every pick**, rather than an
   incremental work list. Justified in §2.4(c). Cost: none; it is what makes
   the "no sharer escapes the probe" argument a one-liner.
2. **A write request invalidates the requester too** if it was a sharer, so
   S → M and O → M go through I. A real directory would not do this. Cost:
   one extra probe round trip on an upgrade, and nothing at all for the
   proofs — the requester's own invalidation is just another element of the
   same pipeline.
3. **Clients block**: in the liveness files, `require ~s.waiting(cl)` on the
   two request rules, so at most one access per cache is in flight. Cost: this
   is an assumption about *clients*, not something the protocol enforces
   (§9, caveat 3). Without it, `waiting(C)` stops identifying a single request
   and the three-stage decomposition of §4.1 collapses.

---

# Part II — The verification

## 3. Safety: the compatibility table

### 3.1 The four headline invariants

The table of §1.5, transcribed:

```ivy
invariant [moesi_M_is_exclusive]
    forall C1, C2. C1 ~= C2 & s.cache(C1) = modified -> s.cache(C2) = invalid

invariant [moesi_E_is_exclusive]
    forall C1, C2. C1 ~= C2 & s.cache(C1) = exclusive -> s.cache(C2) = invalid

invariant [moesi_O_compatible_with_S_only]
    forall C1, C2. C1 ~= C2 & s.cache(C1) = owned
        -> s.cache(C2) = shared | s.cache(C2) = invalid

invariant [moesi_O_is_unique]
    forall C1, C2. s.cache(C1) = owned & s.cache(C2) = owned -> C1 = C2
```

The first two are SWMR (§1.2); the third and fourth are the MOESI refinement.
The fourth is implied by the third but is stated separately because it is the
property one actually wants to quote. All four are in the ∀∀ fragment, so they
cost the solver nothing.

### 3.2 The twelve supporting invariants

The four above are not inductive on their own — they talk only about `cache`,
while the protocol's real state is the directory plus the channels. These
twelve carry the induction, and each corresponds to a sentence one would say
when explaining why the protocol works:

| invariant | in words |
|---|---|
| `excl_unique` | if write permission is out, the sharer list is the singleton `{owner}` |
| `excl_owner_is_sharer` | …and `owner` really is on it |
| `shared_implies_no_writer` | a shared copy, or a shared grant in flight, means no writer — modulo the window of §3.3 |
| `writable_is_owner` | a cache in E or M, or with an E/M grant in flight, is the `owner` and the directory records write permission |
| `owned_is_owner` | a cache in O is the `owner` and is on the sharer list |
| `owned_not_writable` | a cache in O coexists with write permission only while its downgrade ack is still in flight |
| `probe_implies_sharer` | the probe to-do list is a subset of the sharer list |
| `invalidate_in_channel` | an `invalidate` in flight ⇒ a write command is in progress, the target is a sharer, and it has been struck off the to-do list |
| `downgrade_in_channel` | a `downgrade` in flight ⇒ a read command is in progress, write permission is out, and the target is `owner` |
| `invalidateAck_in_channel` | an `invalidateAck` in flight ⇒ the sender's cache is already `invalid`, and the same directory facts |
| `downgradeAck_in_channel` | a `downgradeAck` in flight ⇒ a read command is in progress, write permission is still recorded, the sender is `owner`, is still a sharer, is off the to-do list, and its cache is no longer E or M |
| `no_overlap` | anything in flight from the home to `C` (probe *or* grant) ⇒ no acknowledgement outstanding from `C` — unit capacity coupling the two directions |
| `valid_implies_sharer` | a cache holding any replica is on the sharer list |

The four `*_in_channel` invariants are the workhorses. Each says "a message of
this kind can only exist in a state of this shape", and together they are what
lets the solver rule out the impossible interleavings — a `downgrade` arriving
during a write command, an `invalidateAck` from a cache that is not a sharer,
and so on.

`no_overlap` is more load-bearing than it looks: removing it fails twelve
checks, including four of the ordinary safety invariants, because without it
the two probe-handling rules can no longer be shown to fire.

### 3.3 The one invariant that MOESI forces to be ugly

Eleven of the twelve are the German invariants transposed. This one is not:

```ivy
invariant [shared_implies_no_writer]
    (s.cache(C) = shared | s.channel2_4(C) = grantshared)
        -> s.homeSharerList(C)
           & (~s.homeexclusiveGranted | s.channel3(C) = downgradeAck)
```

German's corresponding invariant ends with a clean `& ~homeexclusiveGranted`.
In MOESI that is **false**, and the reason is the `E → S` half of
`clientdowngradesRule`: between the cache performing that transition and the
home consuming the resulting `downgradeAck`, the cache reads `shared` while the
directory still reads "writable". The escape clause
`| s.channel3(C) = downgradeAck` names the window exactly.
`owned_not_writable` carries the same clause for the `M → O` half.

This was the **only** failing check on the first run of the safety model, and
`ivy_check debug=true trace=true` named the transition directly:

```
s.cache(0) = exclusive, s.channel2_4(0) = downgrade, s.homeexclusiveGranted = true
call clientdowngradesRule   ->   s.cache(0) := shared
```

It is a good illustration of the general point that a new protocol feature
shows up in the proof not as a new invariant but as a *weakening* of an old
one, at exactly the place where the new feature introduces a transient
disagreement.

### 3.4 Evidence that the model really does what MOESI says

An inductive invariant proof says nothing is *violated*; it does not say
anything interesting is *reachable*. Two independent checks:

**Bounded model checking** produced the traces of §2.5.1 and §2.5.2 — i.e.
concrete runs into the E state and into MOESI dirty sharing.

**Violability probes**: add a deliberately false invariant and confirm
`ivy_check` reports it FAIL. (If it *passes*, the state is unreachable and the
property is about nothing.)

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

## 4. The liveness property

```ivy
explicit temporal property [live]
  forall C. globally (s.waiting(C) -> eventually ~s.waiting(C))
```

`waiting(C)` is a ghost bit raised exactly where C issues a request
(`reqsharedRule` / `reqexclusiveRule`) and lowered exactly where C consumes the
corresponding grant (the three `receive*GrantRule`s), so `~waiting(C)` is
precisely "the access completed". The goal is a **state predicate** and
`work_invar` is its negation, which is what the `l2s_not_all_done` and
`l2s_invar` premises need (`LIVENESS_GUIDE.md` §6.5/§6.6).

Fairness is encoded in the guarded-command discipline of the German case study
(§3 there): every rule pulses a boolean `wf_*` flag *before* testing its guard,
and the body becomes an `if`, never a `require`. So the liveness files replace

```ivy
action sendinvalidateRule(cl:client) = {
    require <guard>;
    <body>
}
```

with

```ivy
action sendinvalidateRule(cl:client) = {
    wf_sendinv(cl) := true;
    wf_sendinv(cl) := false;         # a one-step pulse; invariant ~wf_sendinv(C)
    if <guard> { <body> }
}
```

so that `globally eventually wf_sendinv(C)` is a statement about the
*scheduler* ("this rule is offered a turn infinitely often"; a turn on a
disabled rule is a stutter step) rather than about the protocol ("this rule
successfully executes infinitely often"), which would be unsatisfiable in some
runs and would make the theorem vacuous. The two request rules keep `require`
and get no flag — they are environment actions and we never want to force a
cache to issue a request.

### 4.1 The three stages

```
stage 1   channel1(C) ~= empty1                              request queued
stage 2   homeCurrentCommand ~= empty1 & hcc = C             the home is serving C
stage 3   channel2_4(C) = grantshared | grantexclusive | grantmodified
```

`[waiting_stages]` says a waiting client is in one of them, `[stage1_excl]` and
`[stage2_excl]` make them disjoint. Stage 3 has **three** cases here where
German has two, because MOESI has three grant kinds. These are the stages of
§1.7's pipeline, seen from the requester's side rather than the home's.

---

## 5. The lexicographic ranking

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
home is in a probing phase". `_C` is the Skolem constant the `skolemizenp`
tactic produces from the outermost `forall C`; `N` is each component's own
bound variable, ranging over the elements of that component's ranking set.

How to read one row, say [04]: *the set of caches still on the sharer list
while the home is busy shrinks every time the home consumes an invalidate
acknowledgement, and consuming one is guaranteed to shrink it exactly when
some cache has an `invalidateAck` outstanding.* Components [05] and [06] then
rank on successively smaller supersets of the same set, so that the rule
advancing a cache from one pipeline position to the next **conserves** the
lower-order ranking rather than growing it — the union trick of
`LIVENESS_GUIDE.md` §8.3.

Three MOESI-specific observations.

**MOESI has two probe pipelines where German has one.** [04]–[06] is German's
invalidation chain. [07]–[09] is its MOESI twin for the *downgrade* path, and
it is structurally identical but ranks on a different quantity: not "N is still
a sharer" but "write permission is still outstanding for this read command".
This is forced by §2.4(f): a downgrade ack does **not** remove anyone from the
sharer list, so δ[04] does not move when a downgrade completes and cannot
measure its progress. Note that δ[07]–δ[09] do not use `N` in their leading
conjuncts at all — a ranking that is either the whole client set or empty,
which is the `german [08]/[09]` idiom.

**Three grant kinds mean three of everything on the requester's side.** Three
stage-3 components [01]–[03], and three stale-grant drains [10]–[12]. The
drains exist because of the unit-capacity `channel2_4` (§2.2): a cache that has
not yet consumed its own grant blocks the probe the home needs to send it, so
draining a stale grant is a genuine pipeline stage rather than a technicality.

**Every scheduler is literally the enabling guard of its rule.**
`l2s_progress` is *not* discounted by preemption (`LIVENESS_GUIDE.md` §6.2), so
each component must reduce its own ranking whenever its scheduler is on,
preempted or not; a loose "this stage is non-empty" scheduler that is true in
states where the rule is disabled fails immediately. Compare rows 06, 09, 13,
14, 15 against the corresponding `require`/`if` guards in §2.4 — they are the
same formulas.

### 5.1 Why it must be lexicographic

While `_C` sits in stage 1 or stage 3, the home runs *whole commands for other
clients*: a grant grows δ[04] (it adds a sharer) and a pick grows δ[13] (it
makes the home busy). Rule 8 requires every ranking to be conserved by every
action, so under `l2s_auto5` the pipeline would have to be lifted into a
separate lemma — exactly what `german_3channels_original.ivy` does. Rule 10
lets a *preempted* component grow. The load-bearing fact is

```
~pre([04]..[15])  /\  waiting(_C)   ==>   homeCurrentCommand ~= empty1
```

a first-order consequence of `[waiting_stages]`: if no stage-1 and no stage-3
scheduler is on and `_C` is waiting, then either the home is serving `_C`, or
`_C`'s request is queued and — since ψ[00] is off — the home is busy. A busy
home cannot pick, so nothing grows the pipeline in the non-preempted region.
That is why every pipeline ranking carries a "the home is busy" conjunct.

### 5.2 Exactly one cut in the order is load-bearing — a new finding

The German case study reports that demoting stage 1 or stage 3 breaks the
proof, and leaves it there. Permuting the MOESI hierarchy systematically shows
the constraint is *only* the cut between the two blocks:

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
pipeline components fails `l2s_sched_exists` (§7) — but their *relative* order
is not. The sixteen-deep hierarchy in the file is a presentation choice; the
theorem needs a two-deep one.

(This was worth checking because a plausible-looking argument said otherwise:
`receivedowngradeAckRule` falsifies `PROBE`, which is a conjunct of ψ[10]–ψ[12],
so [07] "must" preempt [10] for `l2s_sched_stable[10]` to hold. Swapping them
verifies anyway — Z3 finds another route, presumably because a pending
`downgradeAck` and a grant in `channel2_4` for the same client are excluded by
`[no_overlap]`. Predicted ordering constraints are worth testing, not asserting.)

---

## 6. Two arbiters, two theorems

### 6.1 `moesi_live.ivy` — FIFO arbiter, weak fairness only

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

(`if some x. P(x) minimizing f(x) { … }` is Ivy's sanctioned way to say "choose
a minimal element of a non-empty set" without an induction axiom.)

Its guard — "the home is idle and somebody is queued" — is then stable, so
`globally eventually wf_pick` suffices. Component [00] is the CAV'24 "pending
timestamps ≤ mine" ranking carried over *clients* rather than timestamps, so
`work_created = true` stays valid (finite type) and every component in the file
has the same sort. The one supporting invariant is `[ts_below_clock]
reqts(C) < clock`: a newly issued request is younger than `_C`'s and so can
never join δ[00].

### 6.2 `moesi_live_compassion.ivy` — MOESI as specified

`pickNewRequestRule(cl)` picks an arbitrary queued client. Under weak fairness
the scheduler must offer `_C`'s pick a turn infinitely often but may offer every
one of those turns while the home is busy, so `_C` starves. The assumption is
compassion, and only for the arbiter:

```ivy
explicit temporal axiom [sf_pick]
  forall C. (globally eventually (s.homeCurrentCommand = empty1 & s.channel1(C) ~= empty1))
            -> (globally eventually f_pick(C))
```

Stage 1 then splits into the three tableau cases of `strongfair.ivy`: E
infinitely often (→ [01], compassion delivers the pick), E finitely often but
not finished (→ [00], the tableau bit is itself the ranking), and E never again
(→ the home is never idle again, so the pipeline is required and drives it to a
grant, which makes it idle — contradiction). The compassion axiom also has to
be re-stated as an `invariant` inside the ranking block, because
`instantiate sf_pick` only pins it at time 0 while `l2s_progress_eventually[01]`
is checked at every state (`LIVENESS_GUIDE.md` §6.8).

Everything below stage 1 is identical to `moesi_live.ivy` with the components
shifted by one. The file is *generated* from it by
`gen_moesi_compassion.py` (every edit is a `rep(old, new)` that asserts its
pattern is present), so the two models cannot silently drift apart:

```bash
python3 gen_moesi_compassion.py && ivy_check moesi_live_compassion.ivy
```

---

## 7. Non-vacuity: every ablation, actually run

A liveness proof that still passes with a broken parameter proves nothing.

### 7.1 `moesi_live.ivy`

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
probe kind. They are the liveness counterpart of the `*_in_channel` safety
invariants of §3.2, read in the opposite direction: those say "a message in
flight implies a directory state", these say "a directory state implies a
message in flight".

### 7.2 `moesi_live_compassion.ivy`

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

## 8. What was new relative to the German case study

1. **A second probe pipeline.** The O state means a read request is served by
   *downgrading* rather than invalidating, and a downgrade removes nobody from
   the sharer list. It therefore needs its own three-stage ranking chain whose
   base quantity is "write permission is still outstanding", not "N is still a
   sharer". Nothing in the German proof generalises to it automatically.
2. **A safety invariant with a real exception window** (§3.3).
   `shared_implies_no_writer` cannot be stated cleanly because `E → S` makes
   the cache and the directory disagree until the ack lands. German has no such
   window, because it has no downgrade.
3. **Three grant kinds propagate everywhere**: three stage-3 components, three
   stale-grant drains, three grant-issuing components, three disjuncts in
   `[waiting_stages]`.
4. **The lexicographic order is two-level, not n-level** (§5.2). Measured, not
   assumed.
5. **The whole thing verified on the first `ivy_check` run** — 2867 checks, no
   CTI debugging — once the ranking was designed on paper by the guide's recipe
   and the German template. The one iteration needed anywhere in this exercise
   was the single safety invariant in §3.3. That is the method working as
   advertised: the hard part is the ranking design, and the tool is a decision
   procedure that either confirms it or hands you a counterexample.

---

## 9. Caveats

1. **Compassion is an assumption, not a theorem.** `moesi_live_compassion.ivy`
   is a conditional result. `moesi_live.ivy` is unconditional but only for a
   FIFO home.
2. **Not machine-checked: the claim that the arbitrary-arbiter property is
   false under weak fairness alone.** The argument in §6.2 is by hand. The
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
   about coherence *permissions*, so O's writeback duty and the `M → E` /
   `O → S` writeback transitions are unobservable and omitted, as is silent
   eviction of a clean line. The concrete consequence is visible in §2.5.3
   step 4, where the O holder's dirty value is simply dropped. Adding a `value`
   sort carried in the grant messages would let one state the stronger property
   "every valid copy holds the current value", with the O state as the unique
   authority when memory is stale. That is the natural next extension and it is
   not done here.
7. **`~waiting(C)` is "served", not "served correctly".** Liveness only; the
   coherence guarantees are the §3 invariants.
