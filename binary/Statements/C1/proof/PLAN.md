# C1 proof plan: the invariant, the cut, four packages

2026-11-10, branch `task/binary-c1`. Nothing of `Signed` is proved here. What
exists: the invariant and two executable models (`binary/C1Invariant.lean`,
`binary/C1Step.lean`), the interface propositions (`binary/C1Interfaces.lean`),
and the assembly, proved (`binary/C1Assembly.lean`: `signed_of_parts`). The
statement files are untouched. Every judgement here is the architect's
[AGENT 2026-11-10].

## 0. Read this first: one hypothesis nobody owns

`signed_of_parts` has one hypothesis that is **not derivable from the signed
text**: `NodeBelowTop` (a node the service hands out ends strictly below
2^64). The landed interpretation check `Trie.validate` (inside `assertAt`,
hence inside any invariant built on the landed relation) demands
`a + 72 < 2^64` of every node. The signed `AllocResult` promises
`a + 72 ≤ span.1 + span.2`, and the caller's conditions bound an arena span by
`≤ 2^64` (`spansApart`). A conforming service may hand out the 72 bytes ending
at the top of the address space; the mirror accepts the insertion; the landed
relation cannot hold afterwards. Executed:
`binary/Statements/C1/proof/TopOfMemory.lean` (the arena passes the
statements' checks, the object meets `AllocResult`'s decidable clauses,
`validate` refuses it and accepts the object eight bytes lower).

`Headline` itself is not refuted: by argument (not executed), the compiled
code does not wrap inside such an object, so an invariant with the bound
relaxed would do. It is not provable
with the landed relation and the landed component theorems, which take
`address + nodeSize < 2^64` (`validate_allocate`, `Root.initialization_checked`
through `allocated_facts`). Three ways out, for the owner:

1. add `a + nodeSize < 2^64` to `AllocResult`'s success clause (one conjunct of
   assumed text, true of any real allocator); `NodeBelowTop` is then one line;
2. make `emptyTable` bound arena spans strictly; then `Inv` gains a static
   conjunct and `NodeBelowTop` is restated per layout (small change to
   `C1Invariant` and to the hypothesis, none to the packages' work);
3. relax `Trie.validate` to `≤` and repair the landed proofs that use the
   strict bound (a change to a landed definition in the printed surface of
   the landed lookup results; cost not measured: 37 modules of `binary/`
   carry the bound as a hypothesis named `extent`).

The packages are unaffected by which is chosen: the paths that keep an
allocated node take `NodeBelowTop` as a hypothesis. The result cannot close
until one is chosen.

## 1. The invariant

`Inv L A := Related L A` (`StatementC1Headline.Related`, the landed relation,
unchanged): for some interpretation whose table and peers are the layout's,
`assertAt` holds against the mirror's world, the three sites are armed, the
mirror's pending records are allocation records of the three sites, the table
and peers are apart from the arena, every named node lies in an arena span,
and the allocator is idle with exactly the named nodes handed out and the
mirror's pending records as its answers.

It is not strengthened. The ordering facts the trials assumed are derivable,
and the plan states them as two executable predicates, proved by package 1:

| Fact | Where it comes from | Which case needs it |
| --- | --- | --- |
| `ordered d`: per node, family 32 or 128, `cidr ≤ bitlen`, `bits < 2^bitlen`; per child edge, same family, strictly longer prefix, the parent's prefix shared, the child on the side of the parent's branching bit; each root of its slot's family | `Inv` alone: `Trie.decodeNode`'s checks, `Trie.heap`'s `trie.measure` / `trie.prefix` / `trie.branch`, `heap.root-family` | the walk facts below; restoring `Trie.heap` in every case that adds an edge |
| placed node `p`: `p.bitlen = bits`, `p.cidr ≤ cidr`, the key shares `p`'s prefix, `exact ↔ p.cidr = cidr` | the accepted `nodePlacement` run (each iteration's `placementCidrLe` and `placementPrefixMatches`), `ordered` for the family along the walk | child, cover, split: the edge `p → new` (measure, prefix, branch) |
| node below `down` (the root if nothing placed, else `p.bit[choose p key]`): `min cidr common < down.cidr` | the walk stopped above `down`: `down.cidr > cidr` or `common < down.cidr`; not exact | cover (`new → down` measure), split (`mid → down` measure) |
| `p.cidr < min cidr common` | `ordered`'s edge `p → down` (prefix and branch) and the key's prefix and side at `p`: key and `down` agree on `p.cidr + 1` bits | cover, split: the edge `p → new` or `p → mid` |
| `down` and the key agree on the top `min cidr common` bits; when `common < cidr`, `common < bits` and they differ at bit `common` | arithmetic of `common_bits` (`fls`) on keys within the family width | cover (`new → down` prefix), split (`mid → down`, `mid → new` prefix; the two sides differ) |

Preservation per case, all from the above: `tooLong`, the three `NoMem`
cases and `exact` add no edge (`exact` changes a peer and two lists; the
rollback restores the peer's list and drops the name of the released node);
`root` adds a root of the slot's family; `child`, `cover`, `split` add edges
whose three checks are the rows above. `Framed` holds because reconstruction
reads only the table words, the peer words (`Layout.fixed` is `tableFields`
and `peerFields`) and named nodes, which lie in the arena, and `Idle` by the
contract's `frame` clause. `Initial`: `emptyTable`'s checks are those of
`validate` and `reconstruct` for the empty interpretation.

The owner's open question on references moved between peers: `Inv` compares
each peer's count with the mirror's, so a clause beside `Framed` would be one
more proposition for package 1 and changes nothing else.

**Checked by execution** (`C1Invariant.invCheck`, `walkCheck`,
`C1Step.stepCheck`, added to the packet's test and the capture's check):

- capture, 5 traces, 20 calls under two seeds (40 evaluations): the decidable
  part of `Inv`, the node bound and `ordered` after every call; the walk facts
  before every call: all hold. `stepCheck` on the grid (26) and the split
  rollback trace (4): the mirror's answer, device up to `target`, and pending
  records are `step`'s; cases seen: root, exact, child, cover, split,
  splitNoMem.
- the packet's test (`run-tests.sh`: 23 families, 900 insertions, every case
  of `step` including `tooLong`): `PASS` with the four checks added. After
  every insertion `invCheck`; before it `walkCheck`; `stepCheck` against the
  mirror's run; `cutCheck` on the machine states (section 2). The packet's
  own lines are unchanged (every family `holds`, the five refusals, H1 and H2
  under both contracts).
- `Initial`: the decidable part of `Inv` for the empty interpretation at the
  first captured state of each trace, 10 of 10.
- `Idle` is abstract and is not evaluated; the test's concrete model of it is
  the packet's.

## 2. The cut

`C1Assembly.signed_of_parts` proves `Signed` from: the open hypothesis, and
19 propositions, each one package's acceptance theorem.

```
                 C1Invariant, C1Step, C1Interfaces (fixed)
                                  |
   WP1 Source ---------+----------+-----------+----------- WP4 Service
   RunIsStep           |                      |            AllocRule, FreeRule
   InitialHolds        |                      |            Cmp1FromImage, Cmp8FromImage
   FramedHolds         v                      v            PremisesMet
   LookupHolds     WP2 Trunk  --TrunkToNode--> WP3 Below   WitnessHolds
   ExclusionOne    PathTooLong, PathRootNoMem  PathCover
   ExclusionTwo    PathRoot, PathExact         PathSplitNoMem
                   PathNodeNoMem, PathChild    PathSplit
                   TrunkHolds
```

Dependencies are hypotheses of the propositions, never imports between
packages: WP2 and WP3 take `StepFacts` (what WP1's `RunIsStep` produces) and
the service rules (WP4) as hypotheses; WP2 takes `FramedHolds` (WP1), since
every path ends by carrying `Inv` across the epilogues' writes; WP3 takes
`TrunkToNode` (WP2), whose `Exits` carries `Inv` for it; the exclusions and
the witness take `HeadlineFor`. All four start at once.

| Proposition | One line | Package |
| --- | --- | --- |
| `NodeBelowTop` | a handed-out node ends below 2^64 | none: section 0 |
| `RunIsStep` | every accepted insertion under `Inv` is the pure `step`, with the walk facts | 1 |
| `InitialHolds`, `FramedHolds` | the two clauses for `Inv` | 1 |
| `LookupHolds` | `LookupStep` for `Inv` from the landed `lookup_checked` | 1 |
| `ExclusionOne`, `ExclusionTwo` | the exclusions from `HeadlineFor` | 1 |
| `PathTooLong` | `-EINVAL` for an over-long prefix, both wrappers | 2 |
| `PathRootNoMem`, `PathRoot` | empty root: refused; installed | 2 |
| `PathExact` | exact match | 2 |
| `PathNodeNoMem`, `PathChild` | first allocation on a nonempty trie refused; child attachment | 2 |
| `TrunkHolds` (`TrunkToNode`) | wrapper entry to `add+0x156` with `NodeCut` | 2, for 3 |
| `PathCover` | covering node, root and parent | 3 |
| `PathSplit` | intermediate node, two allocations, root and parent | 3 |
| `PathSplitNoMem` | second allocation refused: unlink, release, `-ENOMEM` | 3 |
| `AllocRule`, `FreeRule` | the service call inside an insertion, derived once from the contract | 4, for 2 and 3 |
| `Cmp1FromImage`, `Cmp8FromImage` | the two unproved callback contracts from the image's ten instructions | 4 |
| `PremisesMet` | a stub service in instruction terms and a common `fetch` meet `Premises` | 4 |
| `WitnessHolds` | `Witness` from `HeadlineFor` | 4 |

The NULL-peer exit is outside the statement (`insertReady` demands a peer) and
has no proposition.

**What the assembly checks and what it does not.** Checked by proof: the case
split is exhaustive, the nine paths with the trunk, the two rules and the open
hypothesis give `InsertStep` for `Inv`, and with package 1's clauses `Headline`
and `Signed`. Not checked: that `StepFacts`, the service rules and `NodeCut`
give the path packages enough. `StepFacts` is tested against the mirror
(`stepCheck`). The cut's decidable part is tested (`cutCheck` in the packet's
test: at `add+0x156` the landed `NodeInit.boundary` against the mirror's
device with the sequence incremented, the object in the arena, `rbx` the
placed node, the stack pointer within the window; at `add+0x549`, reached
once on every path, `ebx` the answer, the cut's stack pointer, and the cut's
bytes from `rsp+48` to the wrapper's return word). Not tested: `Idle` at the
cut, `Exits` as a universal statement, the two service rules. Each path
package's first task is to list what it needs at its incoming interface
beyond this and report a gap before proving against it.

## 3. Rules for every package

- Files: only `binary/<prefix>*.lean` with the package's prefix, imported from
  the package's root module (already a root in `binary/lakefile.toml`). Do not
  edit the lake file, the statement files, `C1Invariant`, `C1Step`,
  `C1Interfaces`, `C1Assembly`, landed modules or another package's files. A
  landed lemma that needs generalising is copied under the package's prefix
  with an origin comment, or reported.
- An interface that cannot be met as stated, or that is too weak to use, is a
  report to the coordinator with the evidence. It is not weakened, strengthened
  or worked around locally, and no hypothesis is added to an acceptance
  theorem.
- No `sorry`, axiom or escape; resource limits per `AGENTS.md` (one
  declaration, with the reason). `binary/` imports nothing from
  `Leanux/Proofs`: source-side facts are re-proved locally.
- Acceptance: the named theorems with exactly the stated propositions as their
  types, `#print axioms` on each showing only the three standard axioms,
  `lake -d binary build` and `scripts/binary-proof-gate` passing, both through
  `scripts/in-bundle` and `capped`.
- Work on a branch of `task/binary-c1` in its own worktree; local commits; no
  push.

## 4. Order of integration

1. Owner: section 0. Does not block the packages.
2. WP1 and WP4's two rules land first (no dependency on others). WP2 next,
   then WP3 (its theorems only mention `TrunkToNode` as a hypothesis, so it can
   land before WP2 as well). WP4's witness last: it may use `HeadlineFor`.
3. Integration pass (not in any package): `C1Signed.lean` applying
   `signed_of_parts` to the acceptance theorems; `NodeBelowTop` per the owner's
   choice; `#print axioms`; the headline in `binary/surface.py` and
   `TrustSurface.expected.txt`; the register entry with the wording in the
   comment on `Signed`; the packet's tests and the capture's check rerun; the
   independent review; `lake check` outside the sandbox, by the owner. Also
   there: the count-move clause if the owner chooses it, and any change of form
   to the callback listing (only package 4's three propositions mention it).

## 5. Risks, ranked

1. **`NodeBelowTop`** (section 0): the result cannot close as signed with the
   landed relation.
2. **The machine cut is tested, not proved sufficient.** `NodeCut` and
   `Exits` were designed from the landed boundary and the trials' hypothesis
   lists; their decidable part holds on the test's states (`cutCheck`). If
   package 3 finds the cut short (a register or a stack word it needs and
   cannot recover from `NodeInit.boundary`), the cut changes and package 2
   re-proves its last step. Mitigation: the first task of packages 2 and 3.
3. **The witness.** No stub service exists in instruction terms; the joint
   decoder agreements have never been met by one `fetch` (the October review's
   N4); `Witness` wants actual finite histories (`Ran`), with a service entry
   and return inside one of them, where the headline gives `Eventually`.
4. **Package 3's size.** The intermediate node's 45 instructions and the
   rollback have no trial; T5's capstone has 48 hypotheses to be derived from
   the cut. It is the package most likely to overrun; the split case can be
   handed to a fifth worker without touching the interfaces.
5. **Entry to the placement header** (package 2): open since October, no
   trial; the landed executable boundaries (`Placement.header`,
   `Root.boundary`, `NodeInit.boundary`) must be established from `Inv` and
   `insertReady`, where so far tests established them.
6. **The service rules' side conditions** (package 4): the contract's
   `Returned` says nothing of the mapping or the direction flag after a
   service body, and the second allocation's `ServiceReady` needs both. The
   landed `MemoryInvariant.eventually_mapped` and `SystemInvariant.eventually`
   carry such properties through any `Eventually` of executed instructions,
   which is what the rules must use; `Protected` must follow from
   `insertReady`'s separations and the two static hypotheses. If either cannot
   be carried, that is a second statement finding.
7. **`RunIsStep`'s loop** (package 1): the walk facts need an induction over
   `nodePlacement`'s bounded loop with its recorded decisions; the proof tree
   has the like (about 1,600 lines) and it may not be imported.
8. **Total cost.** The four estimates sum to 52 to 78 worker-hours, above the
   packet's 40 to 70; the difference is the witness and the source side.
