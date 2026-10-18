import Leanux.Proofs.WG.AuthenticatedEffects.SendWorkClaims

/-! Native frames for the handshake-work queue projection. These facts do not
assume ownership funding or authentication; both are separate caller facts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

theorem of_workQueueFrame {action : WG.M α} (frame : SameView Queues.WorkQueueFrames.view action) :
    SameView queue action :=
  frame.of_factor (fun q => (q.map (fun x => x.2.1)).getD []) queue
    (fun _ => by simp only [queue,Queues.WorkQueueFrames.view,Option.map_map,Function.comp_def])

theorem ambient_frame (action : AmbientM α) : SameView queue (monadLift action : WG.M α) :=
  fun initial => hoare_liftAmbient action (fun w => queue w = initial)

theorem peer_read_frame (pid : PeerId) : SameView queue (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a p v b run
  exact congrArg queue (Queues.getPeer_normal pid w v p a b run).1

theorem peer_write_frame (pid : PeerId) (p : Peer) : SameView queue (setPeer pid p) :=
  of_workQueueFrame (Queues.WorkQueueFrames.update _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

theorem peer_get_frame (pid : PeerId) : SameView queue (peerGet pid) :=
  of_workQueueFrame (Queues.WorkQueueFrames.peerGet_frame pid)

theorem peer_put_frame (pid : Option PeerId) : SameView queue (peerPut pid) :=
  of_workQueueFrame (Queues.WorkQueueFrames.peerPut_frame pid)

theorem branch_expired_frame (site : Decision) (birthdate : Int64) (expiration : Nat)
    (predicate : Bool → Bool) : SameView queue (branchExpired site birthdate expiration predicate) :=
  (branchExpired_sameWGWorld site birthdate expiration predicate).of_factor queue queue (fun _ => rfl)

theorem key_read_frame (id : KeypairId) : SameView queue (getKeypair id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a k v b run
  exact congrArg queue (KeyTimes.getKeypair_return id w v k a b run).1

theorem key_write_frame (id : KeypairId) (k : Keypair) : SameView queue (setKeypair id k) :=
  of_workQueueFrame (Queues.WorkQueueFrames.update _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))

theorem key_put_frame (id : Option KeypairId) (now : Bool) : SameView queue (keypairPut id now) :=
  of_workQueueFrame (Queues.WorkQueueFrames.keypairPut_frame id now)

theorem dev_read_frame : SameView queue getDev := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a d v b run
  cases hd : w.dev with
  | none =>
    simp [getDev,hd,invariant,AmbientM.invariant] at run
    change Except.error _ = Except.ok _ at run
    cases run
  | some device =>
    have same : ((device,w),a) = ((d,v),b) := by simpa [getDev,hd] using run
    exact congrArg (fun z => queue z.1.2) same.symm

theorem skb_frame (action : SkbM α) : SameView queue (liftSkb action) := by
  intro initial
  apply hoare_liftSkb action
  intro w d store hi hd
  simpa [queue,hd] using hi

theorem packet_allocation_frame (packets : List DataPacket) : SameView queue (packets.mapM newTxSkb) := by
  intro initial
  apply mapM_view_spec queue (fun q => q = initial)
  intro packet
  exact skb_frame (SkbStore.newTx packet) initial

theorem index_owner_frame (owner : IndexOwner) : SameView queue owner.peerDeref :=
  fun initial => indexOwner_peerDeref_preserves owner (fun w => queue w = initial)

theorem ecn_frame (packet : WG.Packet) : SameView queue (ipTunnelEcnEncap packet) :=
  (ipTunnelEcnEncap_sameWGWorld packet).of_factor queue queue (fun _ => rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
