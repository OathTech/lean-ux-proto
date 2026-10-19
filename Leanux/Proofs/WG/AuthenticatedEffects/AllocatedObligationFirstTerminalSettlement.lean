import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalFrames

/-! Local first-terminal transitions use an exact recorded native cut. A
socket errno is terminal at the inner result, while later cleanup retains that
same result. Initialized source coverage and pending-ticket entry invariants
remain separate obligations; no global conservation theorem is assumed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open HandshakeSecurity.StagedConservation

private theorem settle_one (valid : Valid births ledger)
    (pending : (ticket,Status.pending location) ∈ ledger) (outcome : Staged.Obligations.Terminal) :
    Staged.Obligations.Step ledger (settle [ticket] outcome ledger) ∧
      Valid births (settle [ticket] outcome ledger) ∧
      (ticket,Status.terminal outcome) ∈ settle [ticket] outcome ledger := by
  have selected : ∀ t ∈ [ticket], t ∈ pendingAt location ledger := by
    intro t member
    have same : t = ticket := by simpa using member
    subst t
    exact mem_pendingAt.mpr pending
  have step := settle_pending (valid.1.symm ▸ valid.2) selected (outcome := outcome)
  refine ⟨step,step.valid valid,?_⟩
  apply List.mem_map.mpr
  exact ⟨(ticket,Status.pending location),pending,by simp⟩

/-- This exact inner socket result settles the pending ticket even on errno.
The physical cell remains for cleanup and every older terminal result stays
unchanged. The receipt position is the actual newly appended journal event. -/
theorem socket (receipt : Completion.SocketReceipt) (native : receipt.Valid)
    (valid : Valid births ledger)
    (resident : Resident history ledger receipt.socket.before.wg)
    (injective : Injective history ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation receipt.id value) :
    let outcome := Staged.Obligations.Terminal.socket history.length (receipt.socket.value == 0)
    let after := settle [ticket] outcome ledger
    let journal := history ++ [CausalJournal.Event.old (.socket receipt)]
    Staged.Obligations.Step ledger after ∧ Valid births after ∧
      Resident journal after receipt.socket.after.wg ∧ Injective journal after ∧
      (ticket,Status.terminal outcome) ∈ after ∧
      Origin journal position ordinal generation receipt.id value ∧
      Packets.epoch receipt.socket.after.wg = some generation ∧
      PacketMaterial.view receipt.socket.after.wg receipt.id = some value ∧
      (∀ other previous, (other,Status.terminal previous) ∈ ledger →
        (other,Status.terminal previous) ∈ after) := by
  dsimp only
  let outcome := Staged.Obligations.Terminal.socket history.length (receipt.socket.value == 0)
  obtain ⟨step,afterValid,terminal⟩ := settle_one valid pending outcome
  have still : Resident history (settle [ticket] outcome ledger) receipt.socket.before.wg :=
    fun other batch index member => resident other batch index
      (pending_after_settle [ticket] outcome member).1
  have nativeResident := socket_resident receipt native still
  have views := socket_views receipt native
  have actual := (resident ticket position ordinal pending).at_origin origin
  refine ⟨step,afterValid,nativeResident.append _,
    (injective.settle [ticket] outcome).append nativeResident _,terminal,origin.append _,
    views.1.trans actual.1,?_,fun _ _ prior => step.terminal prior⟩
  exact (congrFun views.2.2 receipt.id).trans actual.2

/-- A branch-labelled native free settles its own exact pending allocation,
using the recorded reason rather than an arbitrary terminal label. Other
pending cells remain backed by the allocation-injectivity carrier. -/
theorem dispose (receipt : Terminal.Receipt) (native : receipt.Valid)
    (valid : Valid births ledger)
    (resident : Resident history ledger receipt.run.before.wg) (injective : Injective history ledger)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation receipt.skb value) :
    let outcome := Staged.Obligations.Terminal.disposed history.length receipt.reason
    let after := settle [ticket] outcome ledger
    let journal := history ++ [CausalJournal.Event.terminalDrop receipt]
    Staged.Obligations.Step ledger after ∧ Valid births after ∧
      Resident journal after receipt.run.after.wg ∧ Injective journal after ∧
      (ticket,Status.terminal outcome) ∈ after ∧
      receipt.stamp = (generation,receipt.skb+1) ∧
      PacketMaterial.view receipt.run.after.wg receipt.skb = none := by
  dsimp only
  let outcome := Staged.Obligations.Terminal.disposed history.length receipt.reason
  obtain ⟨step,afterValid,afterResident,afterInjective,terminal,stamp⟩ :=
    settle_and_free_injective receipt native valid resident injective pending origin outcome
  exact ⟨step,afterValid,afterResident.append _,afterInjective.append afterResident _,
    terminal,stamp,(free_views receipt native).2.1⟩

/-- Cleanup after a recorded first terminal keeps its original outcome. The
explicit unused-cell fact excludes a still-pending alias before native free. -/
theorem cleanup_after (receipt : Terminal.Receipt) (native : receipt.Valid)
    (valid : Valid births ledger)
    (resident : Resident history ledger receipt.run.before.wg) (injective : Injective history ledger)
    (terminal : (ticket,Status.terminal outcome) ∈ ledger)
    (unused : Unused history ledger receipt.run.before.wg receipt.skb) :
    Staged.Obligations.Step ledger ledger ∧ Valid births ledger ∧
      Resident (history ++ [CausalJournal.Event.terminalDrop receipt]) ledger receipt.run.after.wg ∧
      Injective (history ++ [CausalJournal.Event.terminalDrop receipt]) ledger ∧
      (ticket,Status.terminal outcome) ∈ ledger := by
  obtain ⟨step,valid,after,kept⟩ := cleanup receipt native valid resident terminal unused
  exact ⟨step,valid,after.append _,injective.append after _,kept⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.FirstTerminal
