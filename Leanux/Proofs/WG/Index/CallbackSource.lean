import Leanux.Proofs.WG.Index.TimerFrames
import Leanux.Proofs.WG.Index.ClearSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem expiredRetransmitHandshake_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredRetransmitHandshake pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  have branch (site : Decision) (value : Bool) :
      Ensures (Leanux.branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    ambient (AmbientM.branch site value)
  have arm (site : HiddenSite) (timer : PeerTimer) (delay : Nat) :
      Ensures (discard (modPeerTimer site pid timer delay)) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g inputs result final after pre run
    change (((modPeerTimer site pid timer delay).run g).run inputs >>=
      fun ((value, out), remaining) => Except.ok (((), out), remaining)) = _ at run
    cases actual : ((modPeerTimer site pid timer delay).run g).run inputs with
    | error stop => rw [actual] at run; cases run
    | ok pair =>
      obtain ⟨⟨value, out⟩, remaining⟩ := pair
      rw [actual] at run
      cases run
      exact (ensures_iff _ _ _).mpr (modPeerTimer_tables site pid timer delay)
        g inputs value final after pre actual
  have compare (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    ambient (AmbientM.branchCmp site value lhs rhs)
  have write (p : Peer) := (ensures_iff _ _ _).mpr (setPeer_tables pid p)
  have deleted := (ensures_iff _ _ _).mpr (delTimer_tables pid .sendKeepalive)
  have purge := (ensures_iff _ _ _).mpr (purgeStagedPackets_tables pid)
  have clear := (ensures_iff _ _ _).mpr (clearPeerEndpointSrc_tables pid)
  have queued := (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_tables pid true)
  apply (ensures_iff _ _ _).mp
  unfold expiredRetransmitHandshake
  repeat' first
    | exact pureValue _
    | exact read
    | exact branch _ _
    | exact compare _ _ _ _
    | exact write _
    | exact deleted
    | exact purge
    | exact clear
    | exact queued
    | exact arm _ _ _
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | split

theorem expiredSendKeepalive_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredSendKeepalive pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  have branch (site : Decision) (value : Bool) :
      Ensures (Leanux.branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    ambient (AmbientM.branch site value)
  have arm (site : HiddenSite) (timer : PeerTimer) (delay : Nat) :
      Ensures (discard (modPeerTimer site pid timer delay)) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g inputs result final after pre run
    change (((modPeerTimer site pid timer delay).run g).run inputs >>=
      fun ((value, out), remaining) => Except.ok (((), out), remaining)) = _ at run
    cases actual : ((modPeerTimer site pid timer delay).run g).run inputs with
    | error stop => rw [actual] at run; cases run
    | ok pair =>
      obtain ⟨⟨value, out⟩, remaining⟩ := pair
      rw [actual] at run
      cases run
      exact (ensures_iff _ _ _).mpr (modPeerTimer_tables site pid timer delay)
        g inputs value final after pre actual
  have write (p : Peer) := (ensures_iff _ _ _).mpr (setPeer_tables pid p)
  apply (ensures_iff _ _ _).mp
  unfold expiredSendKeepalive
  repeat' first
    | exact pureValue _
    | exact read
    | exact branch _ _
    | exact write _
    | exact sendKeepalive_tables pid
    | exact arm _ _ _
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | split

theorem expiredNewHandshake_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredNewHandshake pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  unfold expiredNewHandshake
  exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (clearPeerEndpointSrc_tables pid))
    (fun _ => (ensures_iff _ _ _).mpr (sendQueuedHandshakeInitiation_tables pid false))

/-- The actual recorded requeue test and already-queued compensating put remain in the callback. -/
theorem expiredZeroKeyMaterial_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredZeroKeyMaterial pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  have branch (site : Decision) (value : Bool) :
      Ensures (Leanux.branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    ambient (AmbientM.branch site value)
  have dev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g inputs result final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d =>
      simp [getDev, device] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
  have acquire := (ensures_iff _ _ _).mpr (peerGet_tables pid)
  have release := (ensures_iff _ _ _).mpr (peerPut_tables (some pid))
  have queued := (ensures_iff _ _ _).mpr (modifyClearWorkQueue_tables (fun queue => queue ++ [pid]))
  have peek := ambient (AmbientM.peekQueuedUnit .clearPeerWorker pid)
  have record := ambient (AmbientM.recordQueued .clearPeerWorker pid)
  apply (ensures_iff _ _ _).mp
  unfold expiredZeroKeyMaterial
  repeat' first
    | exact pureValue _
    | exact read
    | exact dev
    | exact branch _ _
    | exact acquire
    | exact release
    | exact queued
    | exact peek
    | exact record
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | split

theorem expiredSendPersistentKeepalive_tables (pid : PeerId) :
    ⦃fun g => ⌜TablesSafeWG g⌝⦄ expiredSendPersistentKeepalive pid
      ⦃⇓? _ g => ⌜TablesSafeWG g⌝⦄ := by
  have pureValue {α : Type} (value : α) :
      Ensures (pure value : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have ambient {α : Type} (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action TablesSafeWG)
  have read : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG)
      g ambient p final after pre run).1
  have branch (site : Decision) (value : Bool) :
      Ensures (Leanux.branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    ambient (AmbientM.branch site value)
  apply (ensures_iff _ _ _).mp
  unfold expiredSendPersistentKeepalive
  repeat' first
    | exact pureValue _
    | exact read
    | exact branch _ _
    | exact sendKeepalive_tables pid
    | (refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | split

/-- All five actual callbacks, retaining their send, queue, timer and release paths. -/
theorem timerCallback_tables (pid : PeerId) (timer : PeerTimer) :
    Ensures (timerCallback pid timer) TablesSafeWG (fun _ => TablesSafeWG) := by
  rw [ensures_iff]
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshake_tables pid
  | sendKeepalive => exact expiredSendKeepalive_tables pid
  | newHandshake => exact expiredNewHandshake_tables pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterial_tables pid
  | persistentKeepalive => exact expiredSendPersistentKeepalive_tables pid

end Leanux.Proofs.WG.Index
