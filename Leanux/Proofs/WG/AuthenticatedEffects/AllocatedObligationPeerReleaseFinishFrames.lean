import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPeerReleaseContracts

/-! Release suffix bookkeeping changes ambient/work metadata, not the packet
or peer store. Its existing receipt remains the last history event on both
normal and stopped results. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open HandshakeSecurity.StagedDisposal Staged.Obligations QueueHandoff
set_option pp.structureInstances false

theorem finish_history (value : Option (PeerId × Peer)) (w : World)
    (history : List CausalJournal.Event) : (runPrefix (finish value) w history).2 = history := by
  rw [finish_native,runPrefix_lift]

theorem finish_returned (value : Option (PeerId × Peer))
    (owned : Owned ledger debts locals history w) (bounded : Packets.Inv w.wg)
    (performed : runPrefix (finish value) w history = (.ok ((),v),last)) :
    last = history ∧ Owned ledger debts locals last v ∧ Packets.Inv v.wg := by
  have hist := (congrArg Prod.snd performed).symm.trans (finish_history value w history)
  change last = history at hist
  subst last
  have store : SameWGStore (match value with
      | none => pure ()
      | some (pid,p) => releaseFinish pid p) := by
    cases value with
    | none => exact SameView.pure wgStoreView ()
    | some pair => exact finish_store pair.1 pair.2
  rw [finish_native,runPrefix_lift] at performed
  have full := congrArg Prod.fst performed
  have lifted : SameView (fun world : World => wgStoreView world.wg)
      (liftWG (match value with | none => pure () | some (pid,p) => releaseFinish pid p)) :=
    sameView_liftWG _ _ _ store (fun _ _ _ same => same)
  have fields := (ProjectedAction.iff_run _ _ _).mp lifted w () v full
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev fields
  have pointsLifted : SameView (fun world : World => ownershipPointView world.wg)
      (liftWG (match value with | none => pure () | some (pid,p) => releaseFinish pid p)) :=
    sameView_liftWG _ _ _ (ownershipPoints_kernel _ store) (fun _ _ _ same => same)
  have points := (ProjectedAction.iff_run _ _ _).mp pointsLifted w () v full
  refine ⟨rfl,⟨?_,owned.2.1.points points,owned.2.2.points points⟩,?_⟩
  · have kept := owned.1.quiet_views (v := v.wg) [] (by intro _ absent; cases absent)
      (by simp only [Packets.epoch,device])
      (by funext pid; simp only [Staged.stagedAt,device])
      (by funext skb; simp only [PacketMaterial.view,TxDisposition.txPackets,device])
    simpa only [List.append_nil] using kept
  · simpa only [Packets.Inv,Packets.snapshot,device] using bounded

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.PeerRelease
