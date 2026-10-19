import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerNativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerTimerFrames
import Leanux.Proofs.WG.Queues.HolderAllowedIps

/-! Native routing edits retain both bounds on the same reference account.
Actual list writes and allocation-failure arms are included. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders
namespace AllowedIps

theorem listAddTail_boundary (pid : PeerId) (id : NodeId) :
    Preserves (ExactBoundary cs loans) (listAddTail pid id) :=
  TimerFrames.modify_boundary
    pid (fun p => {p with allowedipsList:=p.allowedipsList++[id]})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => h) (fun _ => rfl)

private theorem aip_boundary (action : AipM α) : Preserves (ExactBoundary cs loans) (liftAip action) := by
  apply hoare_liftAip
  intro w d store hi hd
  apply hi.fields
  unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  simp [hd,rxView]

private theorem read_boundary : Preserves (ExactBoundary cs loans) getDev :=
  ExactBoundary.native_fields (HolderEncrypt.store_fields getDev_sameWGStore)

macro "retired_peer_aip_step" : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact aip_boundary _)
  | (rx_retention_head liftAip; exact aip_boundary _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head getDev; exact read_boundary)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | rx_retention_step)

/-- All original insertion arms retain funding, including allocation refusal
and replacement through actual resident allowed-IP list writes. -/
theorem add_boundary (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Preserves (ExactBoundary cs loans) (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact listAddTail_boundary _ _)
    | (rx_retention_head listDel; exact ExactBoundary.native_fields (HolderAllowedIps.listDel_fields _))
    | retired_peer_aip_step

/-- The sequence counter belongs to routing state and consumes no holder. -/
theorem insert_boundary (family addr cidr : Nat) (pid : PeerId) :
    Preserves (ExactBoundary cs loans) (WG.insert family addr cidr pid) := by
  unfold WG.insert
  apply preserves_bind (show Preserves (ExactBoundary cs loans)
    (modifyDev fun d => {d with peerAllowedips:={d.peerAllowedips with seq:=d.peerAllowedips.seq+1}}) from ?_)
  · intro _
    split <;> exact add_boundary _ _ _ _ _
  · apply hoare_modify
    intro w hi
    apply hi.fields
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd : w.dev <;> simp [hd,rxView]

theorem setAllowedip_boundary (pid : PeerId) (ip : AllowedIpAttrs) :
    Preserves (ExactBoundary cs loans) (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact insert_boundary _ _ _ _)
    | retired_peer_aip_step

end AllowedIps
end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer
