import Leanux.Proofs.WG.Queues.HolderTimerCallbacks
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint

/-! Allowed-IP edits keep the complete holder account. The native AipM lift
updates its own store; actual resident list writes are checked separately. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderAllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private def fieldsOf (s : WGStoreView × (PeerId → Option Peer)) :=
  let w : WGWorld := {dev:=s.1.dev,nlSock7:=s.1.nlSock7,nlSock8:=s.1.nlSock8}
  ((((s.1.dev.map Device.ifindex,fun pid => (s.2 pid).map fun p => (p.internalId,p.refcount,p.rxQueue)),
      rxView w,keyViewOfBorrow s),
     (RxRing.nativeCell w,rxView w,fun pid => (s.2 pid).map fun p => (p.rxQueue,p.napiScheduled))),
    passiveView w,sendView w,fun pid => (s.2 pid).map fun p => p.txQueue.all)

private theorem clear_factor (w : WGWorld) : fieldsOf (AllowedIps.clearListView w)=HolderEncrypt.fields w := by
  unfold fieldsOf AllowedIps.clearListView HolderEncrypt.fields DecryptCarrier.decryptView
  unfold carrierView peerView rxView keyView keyViewOfBorrow keyWords currentCells currentCell
  unfold stableView RxRing.nativeCell passiveView sendView handoffTxView
  simp only [wgStoreView,Option.map_map,Option.bind_map,Option.map_bind,Function.comp_def]
  rfl

theorem listDel_fields (id : NodeId) : SameView HolderEncrypt.fields (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor fieldsOf HolderEncrypt.fields (fun w => (clear_factor w).symm)

theorem listAddTail_boundary (pid : PeerId) (id : NodeId) :
    Preserves (Boundary cs loans) (listAddTail pid id) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_boundary)
    pid (fun p => {p with allowedipsList:=p.allowedipsList++[id]})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => h) (fun _ => rfl)

private theorem aip_boundary (action : AipM α) : Preserves (Boundary cs loans) (liftAip action) := by
  apply hoare_liftAip
  intro w d store hi hd
  apply HolderEncrypt.boundary_fields hi
  unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  simp [hd,rxView]

private theorem read_boundary : Preserves (Boundary cs loans) getDev :=
  HolderEncrypt.native_boundary (HolderEncrypt.store_fields getDev_sameWGStore)

macro "holder_aip_step" : tactic => `(tactic| first
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
    Preserves (Boundary cs loans) (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact listAddTail_boundary _ _)
    | (rx_retention_head listDel; exact HolderEncrypt.native_boundary (listDel_fields _))
    | holder_aip_step

/-- The sequence counter belongs to routing state and consumes no holder. -/
theorem insert_boundary (family addr cidr : Nat) (pid : PeerId) :
    Preserves (Boundary cs loans) (WG.insert family addr cidr pid) := by
  unfold WG.insert
  apply preserves_bind (show Preserves (Boundary cs loans)
    (modifyDev fun d => {d with peerAllowedips:={d.peerAllowedips with seq:=d.peerAllowedips.seq+1}}) from ?_)
  · intro _
    split <;> exact add_boundary _ _ _ _ _
  · apply hoare_modify
    intro w hi
    apply HolderEncrypt.boundary_fields hi
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd : w.dev <;> simp [hd,rxView]

theorem setAllowedip_boundary (pid : PeerId) (ip : AllowedIpAttrs) :
    Preserves (Boundary cs loans) (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact insert_boundary _ _ _ _)
    | holder_aip_step

end Leanux.Proofs.WG.Queues.RxCredits.HolderAllowedIps
