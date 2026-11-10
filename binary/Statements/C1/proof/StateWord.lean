import StatementC1Vacuity

/-! The service-contract finding, kept as a regression test. Not part of the
package build; from `binary/`:

    ../scripts/in-bundle lake env lean Statements/C1/proof/StateWord.lean

Under revision 2 `ServiceReady` did not say where the coverage context's
bytes are. The service package's `word_kept` (branch `task/binary-c1-wp4`,
`C1ServiceContractFinding`) took any admissible entry state, moved the
current-task word so that the task's mode field was an arbitrary four-byte
`word`, showed the moved state admissible for that context, and concluded
from the contract's `c.At` after the call that a conforming service returns
with `word` unchanged; `no_state_word` followed: no allocator with a state
word in the arena met the contract.

Revision 3 adds `ServiceReady.separated`. Two kernel-checked facts about the
revised text, proved here from the statement files alone:

- `mode_apart`: a context admitted at a service entry does not have its mode
  word (or any byte it reads) in the arena or in the service's stack. So the
  moved state of `word_kept` is not admissible when `word` is an arena or a
  scratch byte: its step `readyMoved` has no proof, and its conclusion is no
  longer forced for the allocator's own state.
- `metadata_kept`: whatever a conforming service writes (`ServiceWrites`),
  every metadata byte of the admitted context and the preemption count are
  unchanged. So the `c.At` the contract demands after the call asks of the
  service only that the buffer stay valid: a service may change its scratch,
  free arena bytes and the buffer without being refuted through an aliased
  context. That is what lets a stub in instruction terms use its stack and
  append to the buffer (`Witness`'s `ServiceActive`).

The executable counterpart (a service with an index word in the arena, at an
aliased state, judged by both revisions) is in `Statements/C1/Test.lean`. -/
namespace Binary.Statements.C1.Regression
open Binary Binary.Pair Binary.TrustBase Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- An admitted context's mode word is neither in the arena nor in the
service's stack. -/
theorem mode_apart {L : Layout} {A : Allocator} {c : Context} {s : MachineState}
    (ready : ServiceReady L A c s) (gate : LookupModeRead c.coverage c.preempt)
    (a : BitVec 64) (inside : InRange (c.coverage.task+0x6e0) 4 a) :
    ¬L.Arena a ∧ ¬Scratch s A.depth a ∧ ¬InRange s.data.regs.rsp.toBitVec 8 a := by
  have read : c.bytes a := .inl (.inr (.inr (.inl ⟨gate,inside⟩)))
  exact ⟨ready.separated.coverageArena a read,
    fun scratch => ready.separated.stackCoverage a (.inl scratch) read,
    fun word => ready.separated.stackCoverage a (.inr word) read⟩

/-- A conforming service leaves the admitted context's metadata and the
preemption count alone, whatever it does inside its write set. -/
theorem metadata_kept {L : Layout} {A : Allocator} {c : Context} {s : MachineState} {kept : List Nat}
    {m : Mem 64} (ready : ServiceReady L A c s)
    (frame : EqualOutside (ServiceWrites L A c s kept) s.data.dmem m)
    (a : BitVec 64) (metadata : c.metadataBytes a ∨ InRange preemptCountAddress 4 a) :
    s.data.dmem.get? a = m.get? a := by
  have read : c.bytes a := metadata.elim .inl (fun count => .inr (.inl count))
  refine frame a ?_
  rintro (scratch | ⟨arena,-⟩ | write)
  · exact ready.separated.stackCoverage a (.inl scratch) read
  · exact ready.separated.coverageArena a read arena
  · exact metadata.elim (ready.separated.bufferMetadata a write).1 (ready.separated.bufferMetadata a write).2

#print axioms mode_apart
#print axioms metadata_kept
end Binary.Statements.C1.Regression
