# C1 work package 2: the trunk and the paths that end above the placement

Prefix `binary/C1Trunk*.lean`, root `binary/C1Trunk.lean`. Read `PLAN.md`
(sections 1 to 3) first; its rules apply.

## To prove (acceptance theorems, in `Binary.Statements.C1.Proof`)

| Theorem | Type (`C1Interfaces`) | Path |
| --- | --- | --- |
| `pathTooLong` | `PathTooLong` | wrapper, increment, `add`'s first guard, `-EINVAL`, return; both wrappers |
| `pathRootNoMem` | `PathRootNoMem` | empty root, the service returns NULL, `-ENOMEM` |
| `pathRoot` | `PathRoot` | empty root, node installed |
| `pathExact` | `PathExact` | placement loop to its exact exit, reassignment |
| `pathNodeNoMem` | `PathNodeNoMem` | loop to its other exit, the service returns NULL |
| `pathChild` | `PathChild` | loop, allocation, initialization, child attachment |
| `trunkHolds` | `TrunkHolds` | wrapper entry to `add+0x156` with `NodeCut`, for package 3 |

Each `Path k` runs from the wrapper's entry (`insertReady`) to the caller's
return address with `InsertPost`: `Returned`, `eax`, `SeqAdvanced`, `Inv` for
the mirror's final world, and the write frame.

## Start from

- Landed: `increment_region` (`AllowedipsCounterRegion`);
  `Placement.loop_checked` and its `header` assertion
  (`AllowedipsPlacementChecked`, `AllowedipsPlacementCheck`); `common_checked`;
  `Root.initialization_checked` and `Root.boundary` (`AllowedipsRootChecked`);
  `Exact.assignment_from_relation` (`AllowedipsExactTotal`);
  `NodeInit.boundary` (`PairAllowedipsNodeBoundary`),
  `ChildFinish.initialization_child_checked` (`AllowedipsChildChecked`) and
  `ChildResources.resources`; `Return.add_checked`, `Return.wrapper_checked`
  (`AllowedipsReturnChecked`), `Return.finish_checked`
  (`AllowedipsReturnFrame`); the callback contracts in `Premises`;
  `SystemInvariant`, `MemoryInvariant`, `PairStackBytes`. The landed index
  insertion (`PairInsert*`) is the model of a finished function joined from
  such segments.
- Trial T4 (`task/binary-trials:binary-trials/t4`, unreviewed): `T4Prologue`,
  `T4Entry`, `T4Stack`, `T4Reach`, `T4Regions`, `T4Return`, `T4Fail`,
  `T4Tail`, `T4Main`: `add`'s entry to the return for the empty root and its
  two failures. **Its allocator contract and its entry assertion are
  superseded**: use `AllocRule` and `insertReady` with `Inv`. T4 starts at
  `add`'s entry; the wrappers (increment, address copy and byte swap, call,
  epilogue) are not in it.

## Depends on

- `StepFacts` (hypothesis of every `Path`; package 1 produces it).
- `AllocRule` (package 4), as a hypothesis of the propositions that allocate.
  Its two static hypotheses (table and peers apart from the arena, handed-out
  nodes inside it) are conjuncts of `Inv`.
- `FramedHolds` (package 1), as a hypothesis of every proposition here: the
  last step of each path, and `Exits`' last clause, carry `Inv` across the
  epilogues' stack and coverage writes.
- `NodeBelowTop` (open; `PLAN.md` section 0), as a hypothesis where a node is
  kept.

## What `TrunkToNode` must deliver

For the cases `cover`, `split`, `splitNoMem` (the same code path as `child`
up to `add+0x156`): a state `e` and an interpretation with every field of
`NodeCut`: the landed `NodeInit.boundary` against `bumped w d`; the
interpretation is the layout's and in the arena; the new object in the arena;
`Idle` with the object handed out and the first record consumed; `rbx` the
placed node's address or NULL; `InFlight`, `CallsReady`, `SeqAdvanced`; and
`Exits`: from `add+0x549` with `e`'s stack pointer and the words from
`rsp+48` to the wrapper's return word intact, the machine returns to the
insertion's caller with `ebx` in `eax`, writing only the stack window and the
coverage buffer, the heap unchanged and `Inv` carried.

**First task (before proving):** `cutCheck` in the packet's test
(`Statements/C1/Test.lean`) already evaluates `NodeCut`'s decidable fields at
`add+0x156` and the hypotheses of `Exits` at `add+0x549` on every insertion.
Read what it does not cover (`Idle`, `CallsReady`, the frame clause of
`InFlight`), and agree with package 3 that the cut suffices. Report a gap to
the coordinator; do not change `C1Interfaces`.

## Estimate and risk

12 to 18 worker-hours. Main risk: wrapper entry to the placement header has
been open since October and has no trial; the landed executable boundaries
were established by tests and must now be derived from `Inv` and
`insertReady` (stack readability, separations, saved registers). Second: the
IPv6 wrapper's address copy and byte swap (the deepest stack use, 200 bytes).

## Acceptance

The seven theorems with exactly those types; `#print axioms` on each;
`lake -d binary build` and `scripts/binary-proof-gate` pass.
