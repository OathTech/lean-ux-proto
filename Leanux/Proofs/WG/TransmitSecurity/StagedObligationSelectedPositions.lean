import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTake
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestore
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionLedger

/-! Actual take positions back all selected locations. Their strict history bound
derives the freshness needed by the next take; an arbitrary unused-location
hypothesis is unnecessary once this carrier has been transported. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

def SelectedRecorded (history : List Event) (ledger : Ledger) : Prop :=
  ∀ ticket position, ticket ∈ pendingAt (.selected position) ledger →
    ∃ receipt, history[position]? = some (.stagingTaken receipt)

theorem SelectedRecorded.append (before : SelectedRecorded history ledger) (suffix : List Event) :
    SelectedRecorded (history ++ suffix) ledger := by
  intro ticket position member
  obtain ⟨receipt,atPosition⟩ := before ticket position member
  have earlier := List.getElem?_eq_some_iff.mp atPosition |>.1
  exact ⟨receipt,by simpa [List.getElem?_append_left earlier] using atPosition⟩

theorem SelectedRecorded.fresh (before : SelectedRecorded history ledger) :
    pendingAt (.selected history.length) ledger = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro ticket member
  obtain ⟨receipt,atPosition⟩ := before ticket history.length member
  simp at atPosition

theorem SelectedRecorded.taken (before : SelectedRecorded history ledger)
    (receipt : HandshakeSecurity.StagedConservation.Take.Receipt) (generation stamp : Nat) :
    SelectedRecorded (history ++ [.stagingTaken receipt])
      (transferLocation (.staged generation receipt.pid stamp) (.selected history.length) ledger) := by
  intro ticket position member
  by_cases same : position = history.length
  · subst position
    exact ⟨receipt,by simp⟩
  · have prior : ticket ∈ pendingAt (.selected position) ledger := by
      rw [pendingAt_transfer_other (by simp) (by intro equal; exact same (Pending.selected.inj equal))] at member
      exact member
    exact before.append [.stagingTaken receipt] ticket position prior

theorem SelectedRecorded.restored (before : SelectedRecorded history ledger)
    (position generation pid stamp : Nat) :
    SelectedRecorded history (transferLocation (.selected position) (.staged generation pid stamp) ledger) := by
  intro ticket selected member
  by_cases same : selected = position
  · subst selected
    rw [pendingAt_transfer_source (by simp)] at member
    cases member
  · rw [pendingAt_transfer_other (by simp [same]) (by simp)] at member
    exact before ticket selected member

theorem SelectedRecorded.settled (before : SelectedRecorded history ledger)
    (chosen : List Ticket) (outcome : Terminal) :
    SelectedRecorded history (settle chosen outcome ledger) := by
  intro ticket position member
  rw [pendingAt_settle] at member
  exact before ticket position (List.mem_filter.mp member).1

theorem SelectedRecorded.admitted (before : SelectedRecorded history ledger)
    (birthPosition generation pid stamp : Nat) (packets : List Packet) :
    SelectedRecorded history
      (StagedAdmission.appendBirths ledger birthPosition (.staged generation pid stamp) packets) := by
  intro ticket position member
  rw [StagedAdmission.pending_other (by simp)] at member
  exact before ticket position member

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
