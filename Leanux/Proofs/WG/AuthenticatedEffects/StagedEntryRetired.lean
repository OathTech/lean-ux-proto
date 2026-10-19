import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueuedCarrier

/-! Device replacement must preserve the old ledger. Empty live queues and
cells prove its pending part empty; reset itself is never a disposal event.
The native lifecycle caller must establish these premises before resetting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Retired
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open RetirementSecurity AllocatedObligation CausalJournal

def NoPending (ledger : Ledger) : Prop :=
  ∀ ticket location, (ticket,Status.pending location) ∉ ledger

/-- Logical ownership has no resident packet when both caller locals and all
peer queues are empty. Ring aliases cannot supply an owner. -/
theorem cells_empty (coverage : TxCoverage [] w)
    (queues : txQueueContents w = fun _ => []) : TxDisposition.txPackets w = fun _ => none := by
  funext skb
  cases cell : TxDisposition.txPackets w skb with
  | none => rfl
  | some packet =>
    rcases coverage skb packet cell with held | ⟨pid,queued⟩
    · simp [txLocalItems] at held
    · simp [queues] at queued

/-- Every old ticket is already terminal before a quiescent reset. Exact
queue alignment rules out stranded staged tokens, and allocated backing rules
out ghost pending cells. No terminal is invented by this theorem. -/
theorem no_pending (before : Inv history ledger debts locals w)
    (staged : ∀ epoch pid stamp, stagedPackets epoch pid stamp w = [])
    (cells : TxDisposition.txPackets w = fun _ => none) : NoPending ledger := by
  intro ticket location member
  cases location with
  | staged epoch pid stamp =>
    have aligned := before.core.queues epoch pid stamp
    rw [staged epoch pid stamp] at aligned
    have present := mem_pendingAt.mpr member
    have empty := List.eq_nil_of_length_eq_zero (HandshakeSecurity.StagedConservation.aligned_length aligned)
    rw [empty] at present
    cases present
  | selected position =>
    have present := mem_pendingAt.mpr member
    rw [before.noSelected position] at present
    cases present
  | allocated batch ordinal =>
    obtain ⟨generation,skb,material,_,_,cell⟩ := before.core.physical.resident ticket batch ordinal member
    simp [PacketMaterial.view,cells] at cell

theorem pending_empty (settled : NoPending ledger) (location : Pending) :
    pendingAt location ledger = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro ticket member
  exact settled ticket location (mem_pendingAt.mp member)

/-- An empty replacement state retains the same historical terminals and
birth domain. The caller supplies its actual empty geometry and bounds. -/
theorem empty_replacement (before : Inv history ledger [] [] w) (settled : NoPending ledger)
    (staged : ∀ epoch pid stamp, stagedPackets epoch pid stamp v = [])
    (cells : TxDisposition.txPackets v = fun _ => none)
    (bounds : Packets.Inv v) (coverage : TxCoverage [] v) (inventory : TxInventory [] v) :
    Inv history ledger [] [] v := by
  have impossibleTracked : ∀ ticket batch ordinal, ¬ Tracked ledger [] ticket batch ordinal := by
    intro ticket batch ordinal tracked
    rcases tracked with pending | ⟨_,debt,_⟩
    · exact settled ticket _ pending
    · cases debt
  refine ⟨⟨before.core.valid,?_,before.core.selected,?_,?_,?_,?_⟩,
    before.justified,before.allocationLinks,before.noSelected,bounds,coverage,inventory⟩
  · intro epoch pid stamp
    rw [pending_empty settled _,staged]
    exact .nil
  · intro ticket batch ordinal pending
    exact False.elim (settled ticket _ pending)
  · intro skb material cell
    simp [PacketMaterial.view,cells] at cell
  · exact debts_empty _ _ _
  · intro ticket batch ordinal tracked
    exact False.elim (impossibleTracked ticket batch ordinal tracked)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Retired
