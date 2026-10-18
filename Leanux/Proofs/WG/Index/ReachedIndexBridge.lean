import Leanux.Proofs.WG.Index.ReachedIndexModel
import Leanux.Proofs.WG.Index.InitializedBoundsFrames
import Leanux.Proofs.WG.Queues.HolderInitial

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

namespace Reached
open Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

/-- Native transport domain for the projected index facts. -/
def Core (w : WGWorld) : Prop :=
  ∀ d, w.dev = some d → DeviceIndexCore d

/-- The ledger is the existing source-selected ledger, not an index ghost. -/
def Entry (cs : Ledger) (loans : Reservations)
    (history : List RxHistory.Event) (w : World) : Prop :=
  HolderEntry.Inv cs loans history w ∧ Core w.wg

/-- Base coherence is retained separately: it is not a field of the landed
fixed-cut auxiliary invariant. -/
def Aux (initial : Ledger) (loans : Reservations)
    (before history : List RxHistory.Event) (w : World) : Prop :=
  HolderAuxiliary.Inv initial loans before history w ∧
    BaseCoherence.Inv w.wg ∧ Core w.wg

/-- Admission may choose a new actual ledger. This domain does not require
the pre-admission ledger to survive unchanged. -/
def AnyAux (loans : Reservations) (history : List RxHistory.Event) (w : World) : Prop :=
  ∃ cs, Aux cs loans history history w

theorem core_projection (w : WGWorld) (ambient : Ambient) :
    Core w ↔ View.IndexCore (Campaign2.snapshot w ambient) := Iff.rfl

theorem entry_to_aux {cs : Ledger} {loans : Reservations}
    {history : List RxHistory.Event} {w : World}
    (entry : Entry cs loans history w) (present : w.wg.dev.isSome = true) :
    Aux cs loans history history w :=
  ⟨HolderEntry.to_aux entry.1 present,entry.1.1.1.2.1,entry.2⟩

/-- Recover exactly the source removal suffix and its remaining ledger. -/
theorem aux_to_entry {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w : World}
    (entry : Aux initial loans before history w) :
    ∃ suffix, history = before ++ suffix ∧
      Entry (remaining initial (NapiCarrier.removedPackets suffix)) loans history w := by
  obtain ⟨suffix,historyEq,account⟩ := HolderEntry.of_aux entry.1 entry.2.1
  exact ⟨suffix,historyEq,account,entry.2.2⟩

/-- Rebase at the actual current journal only after accounting for removals. -/
theorem aux_rebase {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w : World}
    (entry : Aux initial loans before history w) :
    ∃ suffix, history = before ++ suffix ∧
      Aux (remaining initial (NapiCarrier.removedPackets suffix)) loans history history w := by
  obtain ⟨suffix,historyEq,account⟩ := HolderInitial.rebase entry.1
  exact ⟨suffix,historyEq,account,entry.2⟩

theorem aux_any {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w : World}
    (entry : Aux initial loans before history w) : AnyAux loans history w := by
  obtain ⟨suffix,_,rebased⟩ := aux_rebase entry
  exact ⟨remaining initial (NapiCarrier.removedPackets suffix),rebased⟩

theorem entry_projection {cs : Ledger} {loans : Reservations}
    {history : List RxHistory.Event} {w : World}
    (entry : Entry cs loans history w) :
    InitializedBounds.EndpointSafe (Campaign2.snapshot w.wg w.ambient) ∧
      View.IndexCore (Campaign2.snapshot w.wg w.ambient) :=
  ⟨InitializedBounds.holder_entry_projection cs loans history w entry.1,entry.2⟩

/-- These are bounds at this actual cut, extracted from its current slot and
allocation components. No final-run theorem is used backwards. -/
theorem aux_bounds {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w : World}
    (entry : Aux initial loans before history w) :
    InitializedBounds.EndpointSafe (Campaign2.snapshot w.wg w.ambient) := by
  intro d device
  change w.wg.dev = some d at device
  have allocation := entry.1.2.1.allocation
  exact ⟨entry.1.2.2 (Affiliation.state d) (by simp [Affiliation.view,device]),
    allocation.peerSlots d device,allocation.keySlots d device⟩

theorem aux_projection {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w : World}
    (entry : Aux initial loans before history w) :
    InitializedBounds.EndpointSafe (Campaign2.snapshot w.wg w.ambient) ∧
      View.IndexCore (Campaign2.snapshot w.wg w.ambient) :=
  ⟨aux_bounds entry,entry.2.2⟩

/-- The current source ledger and charged holder occurrences are retained,
including multiplicities and any incoming loans. -/
theorem aux_funded {initial : Ledger} {loans : Reservations}
    {before history : List RxHistory.Event} {w : World}
    (entry : Aux initial loans before history w) :
    ∃ (suffix : List RxHistory.Event) (holders : DurableHolders), history = before ++ suffix ∧
      holders.Funded (remaining initial (NapiCarrier.removedPackets suffix)) loans w.wg ∧
      StableRx (remaining initial (NapiCarrier.removedPackets suffix)) w.wg := by
  obtain ⟨suffix,historyEq,holders,funded,stable⟩ := entry.1.1.1
  exact ⟨suffix,holders,historyEq,funded,stable⟩
end Reached
end Leanux.Proofs.WG.Index
