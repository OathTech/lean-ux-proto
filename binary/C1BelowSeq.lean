import C1BelowExit
import C1BelowInv
import AllowedipsInternalFrame
import AllowedipsNodeBoundaryFields

/-! Result C1, work package 3: the sequence word at the exit. The relation
reads the sequence word, so two related memories whose devices have the same
sequence hold the same word: `AtExit.seq` follows from the relation at the
cut and the relation at the exit, with no frame argument. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

theorem readNat_memory (x : MachineState) (a n : Nat) :
    readNat x a n = readNat ⟨{dmem := x.data.dmem},0⟩ a n := rfl

/-- A related memory holds the device's sequence in the table's sequence word. -/
theorem seq_of_related {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {x : MachineState}
    {d : Device} (related : Allowedips.Corresponds names o x.data.dmem d) :
    readNat x (names.table+AllowedipsMutationLayout.seq) 8 = .ok d.peerAllowedips.seq.toNat := by
  rw [readNat_memory]
  exact readNat_of_word (reconstruct_fields related).seq

/-- The sequence word at the exit is the cut's: both memories are related to
devices with the same sequence. -/
theorem seq_kept {L : Layout} {names names' : Allowedips.Names} {o : AllowedipsProbe.Offsets}
    {e x : MachineState} {d dev : Device}
    (atCut : Allowedips.Corresponds names o e.data.dmem d)
    (atExit : Allowedips.Corresponds names' o x.data.dmem dev)
    (table : names.table = L.table) (table' : names'.table = L.table)
    (same : dev.peerAllowedips.seq = d.peerAllowedips.seq) :
    readNat x (L.table+AllowedipsMutationLayout.seq) 8 = readNat e (L.table+AllowedipsMutationLayout.seq) 8 := by
  have first := seq_of_related atCut
  have second := seq_of_related atExit
  rw [table] at first
  rw [table',same] at second
  exact second.trans first.symm

/-- The cut's relation: the old interpretation against the mirror's device
with the sequence incremented, and the structural check. -/
theorem NodeCut.related {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
    {s : MachineState} {ra : UInt64} {w : World} {d : Device} {key cidr pid : Nat}
    {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
    {e : MachineState}
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e) :
    Allowedips.Corresponds names Root.nodeOffsets e.data.dmem (bump d) ∧
      Allowedips.heap names (Allowedips.target (bump d)) e.data.dmem = .ok () := by
  obtain ⟨d',device,related,shape⟩ := assertAt_ok (NodeInit.boundary_fields cut.boundary).asserted
  change some (bump d) = some d' at device
  cases Option.some.inj device
  exact ⟨related,shape⟩

#print axioms seq_kept
#print axioms NodeCut.related
end Binary.Statements.C1.Proof
