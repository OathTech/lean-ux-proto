import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFreeFrames

/-! One pending ticket may be settled before its exact native cell is freed.
Other pending allocations remain physically backed. A later cleanup preserves
the first terminal outcome instead of producing a second disposition. Native
reason/receipt-position attribution and initialized nonalias transport remain
the caller's separate obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open HandshakeSecurity.StagedConservation

/-- Every pending claim on this current cell belongs to the chosen ticket.
This cannot be inferred from ledger-key uniqueness alone: distinct tickets
could otherwise have been assigned the same allocation ordinal. -/
def Exclusive (history : List CausalJournal.Event) (ledger : Ledger) (w : WGWorld)
    (ticket : Ticket) (skb : SkbId) : Prop :=
  ∀ other position ordinal, (other,Status.pending (.allocated position ordinal)) ∈ ledger →
    ∀ generation value, Origin history position ordinal generation skb value →
      Packets.epoch w = some generation → other = ticket

theorem pending_after_settle (selected : List Ticket)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal)
    (member : (ticket,Status.pending location) ∈ settle selected outcome ledger) :
    (ticket,Status.pending location) ∈ ledger ∧ ticket ∉ selected := by
  have pending := mem_pendingAt.mpr member
  rw [pendingAt_settle] at pending
  obtain ⟨before,kept⟩ := List.mem_filter.mp pending
  exact ⟨mem_pendingAt.mp before,by simpa only [decide_eq_true_eq] using kept⟩

theorem Exclusive.settled_unused
    (exclusive : Exclusive history ledger w ticket skb)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    Unused history (settle [ticket] outcome ledger) w skb := by
  intro other position ordinal member generation value origin epoch
  obtain ⟨before,absent⟩ := pending_after_settle [ticket] outcome member
  have same := exclusive other position ordinal before generation value origin epoch
  subst other
  exact absent (List.mem_cons_self ..)

/-- A historical allocation lookup and current backing designate the same
resident cell/material; using another valid receipt with equal bytes is not
enough to replace the allocation's position and ordinal. -/
theorem Backed.at_origin (backed : Backed history position ordinal w)
    (origin : Origin history position ordinal generation skb value) :
    Packets.epoch w = some generation ∧ PacketMaterial.view w skb = some value := by
  obtain ⟨otherGeneration,otherId,otherValue,other,time,cell⟩ := backed
  obtain ⟨rfl,rfl,rfl⟩ := origin.unique other
  exact ⟨time,cell⟩

/-- Settle one exact pending allocation, then execute its actual native free.
The terminal label is supplied by its source caller; the same ticket and all
other pending physical cells are retained. -/
theorem settle_and_free (receipt : Terminal.Receipt) (native : receipt.Valid)
    (valid : Valid births ledger) (before : Resident history ledger receipt.run.before.wg)
    (pending : (ticket,Status.pending (.allocated position ordinal)) ∈ ledger)
    (origin : Origin history position ordinal generation receipt.skb value)
    (exclusive : Exclusive history ledger receipt.run.before.wg ticket receipt.skb)
    (outcome : TransmitSecurity.Staged.Obligations.Terminal) :
    let after := settle [ticket] outcome ledger
    TransmitSecurity.Staged.Obligations.Step ledger after ∧ Valid births after ∧ Resident history after receipt.run.after.wg ∧
      (ticket,Status.terminal outcome) ∈ after ∧
      (∀ other previous, (other,Status.terminal previous) ∈ ledger →
        (other,Status.terminal previous) ∈ after) ∧
      receipt.stamp = (generation,receipt.skb+1) ∧
      PacketMaterial.view receipt.run.before.wg receipt.skb = some value := by
  dsimp only
  have unique : (keys ledger).Nodup := valid.1.symm ▸ valid.2
  have chosen : ∀ t ∈ [ticket], t ∈ pendingAt (.allocated position ordinal) ledger := by
    intro t member
    have same : t = ticket := by simpa using member
    subst t
    exact mem_pendingAt.mpr pending
  have step : TransmitSecurity.Staged.Obligations.Step ledger (settle [ticket] outcome ledger) := settle_pending unique chosen
  have still : Resident history (settle [ticket] outcome ledger) receipt.run.before.wg := by
    intro other batch index member
    exact before other batch index (pending_after_settle [ticket] outcome member).1
  have actual := (before ticket position ordinal pending).at_origin origin
  refine ⟨step,step.valid valid,still.free native (exclusive.settled_unused outcome),?_,
    fun _ _ terminal => step.terminal terminal,receipt_stamp receipt actual.1,actual.2⟩
  apply List.mem_map.mpr
  refine ⟨(ticket,Status.pending (.allocated position ordinal)),pending,?_⟩
  simp

/-- Cleanup of an already terminal ticket retains that exact earlier outcome.
Its no-pending-alias premise must come from the actual allocation/ownership
carrier, never merely from the presence of a terminal ledger entry. -/
theorem cleanup (receipt : Terminal.Receipt) (native : receipt.Valid)
    (valid : Valid births ledger) (before : Resident history ledger receipt.run.before.wg)
    (settled : (ticket,Status.terminal outcome) ∈ ledger)
    (unused : Unused history ledger receipt.run.before.wg receipt.skb) :
    TransmitSecurity.Staged.Obligations.Step ledger ledger ∧ Valid births ledger ∧ Resident history ledger receipt.run.after.wg ∧
      (ticket,Status.terminal outcome) ∈ ledger :=
  ⟨TransmitSecurity.Staged.Obligations.Step.refl ledger,valid,before.free native unused,settled⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation
