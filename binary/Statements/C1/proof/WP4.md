# C1 work package 4: the service rules and the witness

Prefix `binary/C1Service*.lean`, root `binary/C1Service.lean`. Read `PLAN.md`
(sections 1 to 3) first; its rules apply.

## To prove (acceptance theorems, in `Binary.Statements.C1.Proof`)

| Theorem | Type (`C1Interfaces`) |
| --- | --- |
| `allocRule` | `AllocRule` |
| `freeRule` | `FreeRule` |
| `cmp1FromImage` | `Cmp1FromImage` |
| `cmp8FromImage` | `Cmp8FromImage` |
| `premisesMet` | `PremisesMet` |
| `witnessHolds` | `WitnessHolds` |

Do the two rules first: packages 2 and 3 take them as hypotheses and want to
know early that they are provable as stated.

## The rules

`AllocRule`: at `allocEntry` inside an insertion (`insertReady` at the
wrapper's entry `s`, `InFlight L A c s e`, a return word, the cache in `rdi`,
`0xdc0` in `esi`, a return site paired with the pending record's site, `Idle`,
and two static facts a caller has from `Inv`: the table and peers apart from
the arena, the handed-out nodes inside it),
the service returns with `AllocResult`, `InFlight` again, and every
`Protected` byte unchanged. To derive from `AllocatorContract.alloc`:

- `ServiceReady`: coverage and capacity from `InFlight.coverage` and
  `insertReady`'s `c1.coverage-capacity`; the direction flag from
  `InFlight.forward`; `stackMapped` from `insertReady`'s `c1.stack-mapping`
  (window `insertWindow + A.depth`), `InFlight.low` and `InFlight.mapped`.
- `InFlight` afterwards: `ServiceWrites ⊆ InsertWrites` (the scratch by
  `InFlight.low`); the mapping and the direction flag across the service body
  by `MemoryInvariant.eventually_mapped` and `SystemInvariant.eventually` (the
  contract's `Returned` says nothing of either: they hold of any executed
  instruction); coverage from the contract.
- `Protected`: the scratch lies below `e`'s stack pointer; the arena and the
  coverage writes are apart from the stack window, the table and peer words
  and the `node_cache` word by `insertReady`'s separations; kept nodes are
  excluded by `ServiceWrites` itself.

`FreeRule` likewise. If a side condition cannot be derived from the signed
text (the mapping across the body is the candidate), that is a statement
finding: report it with the evidence.

## The witness

`Cmp1FromImage`, `Cmp8FromImage`: the two five-instruction callbacks of
`StatementC1CallbackImage`, both a tail jump into `write_comp_data`; the
pattern is `CallbackCmp`, `CallbackWrappers`, `CallbackAgreement` and
`Callback.cmp4_contract`. `PremisesMet`: one `fetch` returning the committed
terms of the six functions (`AllowedipsMutationImage`, `AllowedipsImage`,
`Image`), the landed `ServiceImage`, the ten callback terms, and a stub at
`allocEntry` and `freeEntry` written as instruction terms; a concrete `Idle`
(the packet's test has a model: a bump pointer, a free list and the pending
answers held in arena memory, `Statements/C1/Test.lean`, `idle` and
`service`); the stub must use a nonempty scratch and append to the coverage
buffer when it is in use. `WitnessHolds`: the four calls of `Witness` from a
concrete empty table, with actual histories (`Ran`), and the service entry and
return inside the second history.

Models: the landed random provider of the index insertion (the
`RandomProvider` namespace in `PairInsertProvider*`, `RandomImage`,
`RandomService`, `RandomState*`, `RandomReadyCheck`, and `RandomInputCoupling`
in the trust base: a service with a recorded hidden input and its contract), `PairInsertWitness*`, `LookupWitness*`, `LookupHitWitness*`
(witnesses by execution), `FiniteExecution` (`ActualHistory`).

The owner has not decided whether the callback listing keeps its present
form. Only `Cmp1FromImage`, `Cmp8FromImage` and `PremisesMet` mention
`CallbacksFromImage`; keep everything that depends on its form in modules
named `C1ServiceCallback*`.

## Depends on

Nothing for the rules and the callbacks. `WitnessHolds` takes `HeadlineFor`
as its hypothesis: the four calls may be run through `InsertStep` and
`LookupStep` at the witness's own `fetch`, or executed directly.

## Estimate and risk

12 to 18 worker-hours: rules 3 to 5, callbacks 2 to 3, the stub and
`PremisesMet` 4 to 6, the four-call witness 3 to 4. Main risk: nobody has
written the stub; the joint decoder agreements have never been met by one
`fetch`; and `Witness` wants `Ran` (an actual finite history through a
service entry) where the headline yields `Eventually`. If `Eventually` cannot
be turned into a history, execute the calls directly as the landed witnesses
do.

## Acceptance

The six theorems with exactly those types; `#print axioms` on each;
`lake -d binary build` and `scripts/binary-proof-gate` pass.
