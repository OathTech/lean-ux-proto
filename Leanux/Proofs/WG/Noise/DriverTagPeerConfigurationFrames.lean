import Leanux.Proofs.WG.Noise.DriverTagAllowedFrames
import Leanux.Proofs.WG.Noise.DriverTagFlushCallerSource
import Leanux.Proofs.WG.Queues.JointDevice
import Leanux.Proofs.WG.Noise.DriverTagConfigurationFrames
import Leanux.Proofs.WG.Noise.DriverTagRemovalSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Configuration
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration

theorem peerReadUpdate_frame {α : Type} (pid : PeerId) (f : Peer → Peer)
    (middle : Peer → WG.M α)
    (same : ∀ p, SameView (fun w : WGWorld => w) (middle p))
    (tags : ∀ p, (f p).handshakeState = p.handshakeState) :
    SameView tagView (do
      let p ← getPeer pid
      let x ← middle p
      setPeer pid (f p)
      pure x) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,current,inputs,read,run⟩ := run
  obtain ⟨worldEq,ambientEq,d,device,resident⟩ :=
    Origins.getPeer_return pid w current p ambient inputs read
  subst current
  subst inputs
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨result,middleWorld,middleAmbient,mid,run⟩ := run
  have equality := (ProjectedAction.iff_run_ambient _ _ _).mp (same p) _ _ _ _ _ mid
  change middleWorld = w at equality
  subst middleWorld
  simp [setPeer,modifyDev,device] at run
  obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
  change responseTagMap (some _) = responseTagMap w.dev
  rw [device]
  exact tagMap_write d pid p (f p) resident (tags p)

theorem keepaliveUpdate_frame (pid : PeerId) (interval : Nat) (running : Bool) :
    SameView tagView (do
      let p ← getPeer pid
      let send ← WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
        (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))
      setPeer pid {p with persistentKeepaliveInterval := interval}
      pure send) := by
  apply peerReadUpdate_frame pid (fun p => {p with persistentKeepaliveInterval := interval})
  · intro p initial
    change Preserves (fun w : WGWorld => w = initial) _
    unfold WG.andM
    simp (config := {zeta := false}) only [branch]
    repeat' first
      | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
      | rx_retention_step
  · intro p; rfl

theorem retained_preserves {α : Type} (action : WG.M α)
    (frame : ∀ g ambient result final after,
      (action.run g).run ambient = .ok ((result,final),after) →
      TagsRetained (tagView g) (tagView final)) (entry : TagMap) :
    Preserves (fun g => TagsRetained entry (tagView g)) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g ambient result final after prior run
  exact prior.trans (frame g ambient result final after run)

theorem put_preserves (peer : Option PeerId) (entry : TagMap) :
    Preserves (fun g => TagsRetained entry (tagView g)) (WG.peerPut peer) :=
  retained_preserves _ (Index.staging_tags _ (fun initial => Index.staging_peerPut initial peer)) entry

theorem staged_preserves (pid : PeerId) (entry : TagMap) :
    Preserves (fun g => TagsRetained entry (tagView g)) (sendStagedPackets pid) :=
  retained_preserves _ (Index.sendStagedPackets_tags_retained pid) entry

theorem keepalive_preserves (pid : PeerId) (entry : TagMap) :
    Preserves (fun g => TagsRetained entry (tagView g)) (sendKeepalive pid) :=
  retained_preserves _ (Index.sendKeepalive_tags_retained pid) entry

theorem keepaliveUpdate_then {α : Type} (entry : TagMap)
    (pid : PeerId) (interval : Nat) (running : Bool) (tail : Bool → WG.M α)
    (rest : ∀ send, Preserves (fun w => TagsRetained entry (tagView w)) (tail send)) :
    Preserves (fun w => TagsRetained entry (tagView w)) (do
      let p ← getPeer pid
      let send ← WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
        (WG.andM (branch .peerKeepaliveNonzero (interval != 0)) (branch .peerKeepaliveRunning running))
      setPeer pid {p with persistentKeepaliveInterval := interval}
      tail send) := by
  simpa only [bind_assoc,pure_bind] using
    preserves_bind ((keepaliveUpdate_frame pid interval running).wp (TagsRetained entry)) rest

theorem peerTail_preserves (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (entry : TagMap) :
    Preserves (fun w => TagsRetained entry (tagView w)) (peerConfigTailSource a peer pid) := by
  unfold peerConfigTailSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (env_bind_head getPeer
       apply keepaliveUpdate_then entry
       intro send)
    | (rx_retention_head setAllowedip
       exact (setAllowedip_frame _ _).wp (TagsRetained entry))
    | (rx_retention_head sendStagedPackets; exact staged_preserves _ entry)
    | (rx_retention_head sendKeepalive; exact keepalive_preserves _ entry)
    | (rx_retention_head peerPut; exact put_preserves _ entry)
    | (rx_retention_head getDev; exact (store_frame getDev_sameWGStore).wp (TagsRetained entry))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => TagsRetained entry (tagView w))
       intro x acc
       change Preserves (fun w => TagsRetained entry (tagView w)) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem peerTail_retained (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    ∀ g ambient result final after,
      ((peerConfigTailSource a peer pid).run g).run ambient = .ok ((result,final),after) →
      TagsRetained (tagView g) (tagView final) := by
  intro g ambient result final after run
  exact (hoare_iff_run_ambient _ _ _).mp (peerTail_preserves a peer pid (tagView g))
    g ambient result final after (TagsRetained.refl _) run


end Leanux.Proofs.WG.Noise.DriverTags.Configuration
