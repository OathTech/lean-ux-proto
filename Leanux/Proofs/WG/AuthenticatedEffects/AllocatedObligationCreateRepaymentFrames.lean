import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateRepaymentSource
import Leanux.Proofs.WG.TransmitSecurity.StagedExactFrames

/-! Native TX reads and key repayment preserve the complete fixed ownership
entry. Their actual access histories are extended independently of state
erasure; key retirement cannot settle a staged peer ticket. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations QueueHandoff
set_option pp.structureInstances false

theorem guard_total (decision : Decision) (flag : Bool)
    (owned : Owned ledger debts locals history w) (bounded : Packets.Inv w.wg) :
    ∃ v, runPrefix (Admission.actualOps.step (branch decision flag)) w history = (.ok (flag,v),history) ∧
      Owned ledger debts locals history v ∧ Packets.Inv v.wg := by
  let v := {w with ambient := {w.ambient with steps := (w.ambient.steps.push
      {decision := decision,outcome := flag,netRx := w.ambient.netRxSection})}}
  refine ⟨v,?_,owned,bounded⟩
  have run : runPrefix (liftPrefix (liftWG (branch decision flag))) w
      (history.filterMap CausalJournal.txEvent?) = (.ok (flag,v),history.filterMap CausalJournal.txEvent? ++ []) := by
    simp only [List.append_nil]
    rfl
  simpa only [Admission.actualOps,HandshakeSecurity.StagedDisposal.TxSource.observed,
    HandshakeSecurity.StagedDisposal.TxSource.Ops.focus,HandshakeSecurity.StagedDisposal.TxSource.native,
    List.map_nil,List.append_nil] using focusPrefix_suffix
    CausalJournal.txEvent CausalJournal.txEvent? _ w history _ [] run

theorem read_tx_owned (skb : SkbId) (owned : Owned ledger debts locals history w)
    (bounded : Packets.Inv w.wg)
    (performed : runPrefix (Admission.actualOps.access (getTxSkbPrefix skb)) w history = (.ok (packet,v),last)) :
    Owned ledger debts locals last v ∧ Packets.Inv v.wg := by
  have erases := focusPrefix_erases CausalJournal.txEvent CausalJournal.txEvent?
    (TxDisposition.nativeAccess_erases (getTxSkbPrefix_erases skb))
  have full := (erases w history).symm.trans (congrArg Prod.fst performed)
  obtain ⟨suffix,extended,quiet⟩ := focused_quiet (TxDisposition.nativeAccess (getTxSkbPrefix skb)) w history
  change (runPrefix (Admission.actualOps.access (getTxSkbPrefix skb)) w history).2 = _ at extended
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [liftWG_run] at full
  cases native : ((getTxSkb skb).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    have same := (Packets.getTxSkb_current skb w.wg g result w.ambient ambient native).1
    refine ⟨⟨?_,same ▸ owned.2.1,same ▸ owned.2.2⟩,same ▸ bounded⟩
    rw [extended]
    exact owned.1.quiet_views suffix quiet (congrArg Packets.epoch same)
      (congrArg Staged.stagedAt same) (congrArg PacketMaterial.view same)

theorem key_put_owned (kid : Option KeypairId) (owned : Owned ledger debts locals history w)
    (bounded : Packets.Inv w.wg)
    (performed : runPrefix (Admission.actualOps.access (keypairPutPrefix kid false)) w history = (.ok ((),v),last)) :
    Owned ledger debts locals last v ∧ Packets.Inv v.wg := by
  have erases := focusPrefix_erases CausalJournal.txEvent CausalJournal.txEvent?
    (TxDisposition.nativeAccess_erases (keypairPutPrefix_erases kid false))
  have full := (erases w history).symm.trans (congrArg Prod.fst performed)
  obtain ⟨suffix,extended,quiet⟩ := focused_quiet (TxDisposition.nativeAccess (keypairPutPrefix kid false)) w history
  change (runPrefix (Admission.actualOps.access (keypairPutPrefix kid false)) w history).2 = _ at extended
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [liftWG_run] at full
  cases native : ((keypairPut kid false).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨ignored,g⟩,ambient⟩ := out
    cases ignored
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨_,rfl⟩ := full
    have geometry := (ProjectedAction.iff_run_ambient _ _ _).mp
      (StagingOccurrences.key_put_geometry kid false) w.wg w.ambient () g ambient native
    have material := (ProjectedAction.iff_run_ambient _ _ _).mp
      (PacketMaterial.of_packets (TxDisposition.keyPut_packets kid false)) w.wg w.ambient () g ambient native
    have epoch := (ProjectedAction.iff_run_ambient _ _ _).mp
      (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid false)) w.wg w.ambient () g ambient native
    have queues := (ProjectedAction.iff_run_ambient _ _ _).mp
      (Staged.Exact.key_put kid false) w.wg w.ambient () g ambient native
    refine ⟨⟨?_,owned.2.1.key_put kid false _ _ native,owned.2.2.key_put kid false _ _ native⟩,?_⟩
    · rw [extended]
      exact owned.1.quiet_views suffix quiet epoch queues material
    · change Lifetimes.Bounded (Packets.snapshot g)
      have shape : Packets.snapshot g = Packets.snapshot w.wg := congrArg Prod.fst geometry
      rw [shape]
      exact bounded

theorem key_repayment_returned (first : SkbId)
    (owned : Owned ledger debts locals history w) (bounded : Packets.Inv w.wg)
    (performed : runPrefix (keyRepayment first) w history = (.ok ((),v),last)) :
    Owned ledger debts locals last v ∧ Packets.Inv v.wg := by
  rw [keyRepayment,runPrefix_bind] at performed
  cases read : runPrefix (Admission.actualOps.access (getTxSkbPrefix first)) w history with
  | mk outcome readHistory =>
    rw [read] at performed
    cases outcome with
    | error stop => cases performed
    | ok out =>
      obtain ⟨packet,u⟩ := out
      obtain ⟨readOwn,bounds⟩ := read_tx_owned first owned bounded read
      exact key_put_owned (some packet.keypair) readOwn bounds performed

theorem PendingBatch.allocated_frame (before : PendingBatch history ledger items)
    {afterLedger : Ledger} (frame : AllocatedFrame ledger afterLedger) : PendingBatch history afterLedger items := by
  intro id member
  obtain ⟨ticket,position,ordinal,generation,value,pending,origin⟩ := before id member
  exact ⟨ticket,position,ordinal,generation,value,(frame.pending _ _ _).mpr pending,origin⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
