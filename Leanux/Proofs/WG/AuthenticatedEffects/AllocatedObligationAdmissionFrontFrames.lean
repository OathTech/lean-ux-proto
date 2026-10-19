import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPublicationHistoryFrames

/-! The admission guard reads its actual peer and records a total branch.
These operations preserve the full canonical ledger and physical owner. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations QueueHandoff
set_option pp.structureInstances false

theorem branch_total (decision : Decision) (flag : Bool)
    (owned : Owned ledger debts locals history w) :
    ∃ v, runPrefix (actualOps.step (branch decision flag)) w history = (.ok (flag,v),history) ∧
      Owned ledger debts locals history v := by
  let v := {w with ambient := {w.ambient with steps := (w.ambient.steps.push
      {decision := decision,outcome := flag,netRx := w.ambient.netRxSection})}}
  refine ⟨v,?_,owned⟩
  have run : runPrefix (liftPrefix (liftWG (branch decision flag))) w
      (history.filterMap CausalJournal.txEvent?) = (.ok (flag,v),history.filterMap CausalJournal.txEvent? ++ []) := by
    simp only [List.append_nil]
    rfl
  simpa only [actualOps,TxSource.observed,TxSource.Ops.focus,TxSource.native,
    List.map_nil,List.append_nil] using focusPrefix_suffix
    CausalJournal.txEvent CausalJournal.txEvent? _ w history _ [] run

theorem read_peer_entry (pid : PeerId) (owned : Owned ledger debts locals history w)
    (performed : runPrefix (actualOps.access (getPeerMixed pid)) w history = (.ok (p,v),last)) :
    Owned ledger debts locals last v := by
  have erases := focusPrefix_erases CausalJournal.txEvent CausalJournal.txEvent?
    (TxDisposition.nativeAccess_erases (getPeerMixed_erases pid))
  have full := (erases w history).symm.trans (congrArg Prod.fst performed)
  obtain ⟨suffix,extended,quiet⟩ := focused_quiet (TxDisposition.nativeAccess (getPeerMixed pid)) w history
  change (runPrefix (actualOps.access (getPeerMixed pid)) w history).2 = _ at extended
  rw [performed] at extended
  change last = history ++ suffix at extended
  rw [liftWG_run] at full
  cases native : ((getPeer pid).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    have same := Peers.getPeer_current pid w.wg g result w.ambient ambient native
    refine ⟨?_,same.1 ▸ owned.2.1,same.1 ▸ owned.2.2⟩
    rw [extended]
    exact owned.1.quiet_views suffix quiet (congrArg Packets.epoch same.1)
      (congrArg Staged.stagedAt same.1) (congrArg PacketMaterial.view same.1)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Admission
