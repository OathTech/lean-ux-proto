import Leanux.Proofs.WG.Noise.DriverTagRemovalFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Removal
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Configuration
universe u

/-! The only new factor exposes the two actual inline workqueue flushes.
All guards, original errors and final accounting remain literal. -/
def afterDeadWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → WG.M α → m α)
    (keys timers : PeerId → m Unit) (drain : Option PeerId → m Unit)
    (release : PeerId → m Unit) (pid : PeerId) : m Unit := do
  if ← lift (do branch .peerRemoveNotDead !(← getPeer pid).isDead) then
    lift (unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)")
  keys pid
  timers pid
  let d ← lift getDev
  if !d.encryptQueue.empty || !d.decryptQueue.empty || !d.txWorkQueue.isEmpty
      || d.peers.toList.any (·.2.napiScheduled) then
    lift (unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")
  drain none
  if (← lift getDev).numPeers == 0 then lift (invariant "--num_peers below zero")
  lift (modifyDev fun d => {d with numPeers := d.numPeers-1})
  release pid

theorem afterDead_factor (pid : PeerId) : WG.peerRemoveAfterDead pid =
    afterDeadWith (fun {_} a => a) keypairsClear timersStop drainHandshakeSendWq
      (fun p => WG.peerPut (some p)) pid := by
  simp only [WG.peerRemoveAfterDead,afterDeadWith,bind_assoc]

def makeDeadObserved (pid : PeerId) : Obs Unit := liftWGPrefix (WG.peerMakeDead pid)

def afterDeadObserved (pid : PeerId) : Obs Unit :=
  afterDeadWith (fun {_} a => liftWGPrefix a)
    (fun p => liftWGPrefix (keypairsClear p)) Flush.timersStopObserved Flush.drainObserved
    (fun p => liftWGPrefix (WG.peerPut (some p))) pid

def removeObserved (peer : Option PeerId) : Obs Unit :=
  Configuration.peerRemoveWith (fun {_} a => liftWGPrefix a)
    makeDeadObserved afterDeadObserved peer

def removeAllObserved : Obs Unit :=
  Configuration.peerRemoveAllWith (fun {_} a => liftWGPrefix a)
    (liftWGPrefix WG.free) makeDeadObserved afterDeadObserved

def destructObserved : Obs Unit :=
  Configuration.destructWith (fun {_} a => liftWGPrefix a)
    removeAllObserved (liftWGPrefix destructFinishSource)

theorem makeDeadObserved_erases (pid : PeerId) :
    ErasesStatePrefix (makeDeadObserved pid) (WG.peerMakeDead pid) :=
  erasesStatePrefix_lift _

theorem afterDeadObserved_erases (pid : PeerId) :
    ErasesStatePrefix (afterDeadObserved pid) (WG.peerRemoveAfterDead pid) := by
  rw [afterDead_factor]
  unfold afterDeadObserved afterDeadWith
  repeat' first
    | with_reducible exact Flush.timersStopObserved_erases _
    | with_reducible exact Flush.drainObserved_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem removeObserved_erases (peer : Option PeerId) :
    ErasesStatePrefix (removeObserved peer) (WG.peerRemove peer) := by
  rw [Configuration.peerRemove_factor]
  unfold removeObserved Configuration.peerRemoveWith
  repeat' first
    | with_reducible exact makeDeadObserved_erases _
    | with_reducible exact afterDeadObserved_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)
    | split

theorem removeAllObserved_erases :
    ErasesStatePrefix removeAllObserved WG.peerRemoveAll := by
  rw [Configuration.peerRemoveAll_factor]
  unfold removeAllObserved Configuration.peerRemoveAllWith
  repeat' first
    | with_reducible exact makeDeadObserved_erases _
    | with_reducible exact afterDeadObserved_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (maintenance_intro; try dsimp only)

theorem destructObserved_erases :
    ErasesStatePrefix destructObserved WG.wgDestruct := by
  rw [Configuration.wgDestruct_factor]
  unfold destructObserved Configuration.destructWith
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind removeAllObserved_erases (fun _ => erasesStatePrefix_lift _)))

theorem makeDeadObserved_preserves (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (makeDeadObserved pid) :=
  lift_frame entry _ (makeDead_tags pid)

theorem afterDeadObserved_preserves (entry : TagMap) (pid : PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (afterDeadObserved pid) := by
  have guard : StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix (do branch .peerRemoveNotDead !(← getPeer pid).isDead)) :=
    lift_frame entry _ ((getPeer_frame pid).bind (fun p =>
      ambient_frame (AmbientM.branch .peerRemoveNotDead !p.isDead)))
  have released : StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory
      (liftWGPrefix (WG.peerPut (some pid))) :=
    lift_retained entry _ (Index.staging_tags _ (fun initial =>
      Index.staging_peerPut initial (some pid)))
  change StatePrefixEnsures (fun h g _ => NativeInv entry h g) ValidHistory _
    (fun _ h g _ => NativeInv entry h g)
  unfold afterDeadObserved afterDeadWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | exact guard
    | exact released
    | with_reducible exact Flush.timersStopObserved_preserves entry _
    | with_reducible exact Flush.drainObserved_preserves entry _
    | (maintenance_lift_action_head keypairsClear; exact lift_frame entry _ (Flush.keys_tags _))
    | (maintenance_lift_action_head getDev; exact Flush.dev_preserves entry)
    | (maintenance_lift_action_head unsupported; exact ambient_preserves entry (AmbientM.unsupported _))
    | (maintenance_lift_action_head invariant; exact ambient_preserves entry (AmbientM.invariant _))
    | (maintenance_lift_action_head modifyDev; exact lift_frame entry _ (modifyDev_frame _ (fun _ => rfl)))
    | (maintenance_head Pure.pure; exact pure_preserves entry _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h g _ => NativeInv entry h g))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_intro
    | split

theorem removeObserved_preserves (entry : TagMap) (peer : Option PeerId) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory (removeObserved peer) := by
  change StatePrefixEnsures (fun h g _ => NativeInv entry h g) ValidHistory _
    (fun _ h g _ => NativeInv entry h g)
  unfold removeObserved Configuration.peerRemoveWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | with_reducible exact makeDeadObserved_preserves entry _
    | with_reducible exact afterDeadObserved_preserves entry _
    | (maintenance_lift_action_head branch; exact ambient_preserves entry (AmbientM.branch _ _))
    | (maintenance_lift_action_head invariant; exact ambient_preserves entry (AmbientM.invariant _))
    | (maintenance_head Pure.pure; exact pure_preserves entry _)
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h g _ => NativeInv entry h g))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_intro
    | split

theorem removeAllObserved_preserves (entry : TagMap) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory removeAllObserved := by
  change StatePrefixEnsures (fun h g _ => NativeInv entry h g) ValidHistory _
    (fun _ h g _ => NativeInv entry h g)
  unfold removeAllObserved Configuration.peerRemoveAllWith
  dsimp (config := {zeta := false}) only []
  repeat' first
    | with_reducible exact makeDeadObserved_preserves entry _
    | with_reducible exact afterDeadObserved_preserves entry _
    | (maintenance_lift_action_head free; exact lift_frame entry _ free_frame)
    | (maintenance_lift_action_head getDev; exact Flush.dev_preserves entry)
    | (maintenance_lift_action_head branch; exact ambient_preserves entry (AmbientM.branch _ _))
    | (maintenance_head Pure.pure; exact pure_preserves entry _)
    | (maintenance_head ForIn.forIn
       apply Flush.list_preserves _ _ (fun _ _ _ prior => prior.2)
       intro loopPeer loopState
       change StatePrefixEnsures (fun h g _ => NativeInv entry h g) ValidHistory _
         (fun _ h g _ => NativeInv entry h g))
    | (maintenance_head Bind.bind
       apply StatePrefixEnsures.bind (Q := fun _ h g _ => NativeInv entry h g))
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_intro

theorem destructObserved_preserves (entry : TagMap) :
    StatePrefixPreserves (fun h g _ => NativeInv entry h g) ValidHistory destructObserved := by
  unfold destructObserved Configuration.destructWith
  exact (lift_frame entry _ (modifyDev_frame (fun d => {d with creatingNet := false,incomingPort := 0}) (fun _ => rfl))).bind (fun _ =>
    (lift_frame entry _ (socket_frame (socketReinit_sameSocket none none))).bind (fun _ =>
    removeAllObserved_preserves entry |>.bind (fun _ =>
      lift_retained entry destructFinishSource destructFinish_retains)))


end Leanux.Proofs.WG.Noise.DriverTags.Removal
