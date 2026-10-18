import Leanux.Proofs.WG.Roaming.RemoteSessionEffects
import Leanux.Proofs.WG.Roaming.RemotePeerFrames
import Leanux.Proofs.WG.Noise.ResponseSuffixTagFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing TimerDiscipline Std.Do

theorem wheelPlacementView_endpoints (entry : Campaign2.State) (d : Device)
    (pid : PeerId) (p : Peer) (timer : PeerTimer) (expires clk : UInt64)
    (device : entry.device = some d) (resident : d.peers[pid]? = some p) :
    responseEndpointMap (wheelPlacementView entry pid p timer expires clk).device =
      responseEndpointMap entry.device := by
  unfold wheelPlacementView
  split
  · simp only [device, Option.map_some]
    exact (pinned_const _private.Leanux.Proofs.WG.Roaming.ResponseRejectionFrames.«0».Leanux.Proofs.WG.Roaming.endpoint_write) d pid p _ resident (by cases timer <;> rfl)
  · simp only [device, Option.map_some]
    exact (pinned_const _private.Leanux.Proofs.WG.Roaming.ResponseRejectionFrames.«0».Leanux.Proofs.WG.Roaming.endpoint_write) d pid p _ resident (by cases timer <;> rfl)

theorem peerTimerArmEffect_endpoints (entry : Campaign2.Snapshot) (d : Device)
    (pid : PeerId) (p : Peer) (timer : PeerTimer) (delay : Nat)
    (final : Campaign2.State) (device : entry.wg.device = some d)
    (resident : d.peers[pid]? = some p)
    (effect : peerTimerArmEffect entry pid p timer delay final) :
    responseEndpointMap final.device = responseEndpointMap entry.wg.device := by
  unfold peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller, now, unit, _, _, effect⟩ := effect
    split at effect
    · rw [effect]; rfl
    · obtain ⟨clk, effect⟩ := effect
      rw [effect]
      exact wheelPlacementView_endpoints _ d pid p timer _ clk device resident
  · rw [effect]
    exact wheelPlacementView_endpoints entry.wg d pid p timer _ _ device resident

theorem modPeerTimer_endpoint_frame (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) (entry : Option Device) :
    Ensures (modPeerTimer site pid timer delay)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  intro g ambient result final after pre run
  apply Eq.trans _ pre
  cases device : g.dev with
  | none =>
    exact False.elim (ResponseSuffix.modPeerTimer_missing_false site pid timer delay g final ambient after result
      (by simp [peerAt,device]) run)
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      exact False.elim (ResponseSuffix.modPeerTimer_missing_false site pid timer delay g final ambient after result
        (by simp [peerAt,device,resident]) run)
    | some p =>
      obtain ⟨value, effect⟩ := modPeerTimer_effect site pid timer delay d p resident
        (Campaign2.snapshot g ambient) g ambient result final after ⟨rfl, device⟩ run
      cases result with
      | false =>
        simpa only [Campaign2.snapshot, Campaign2.core, device] using
          congrArg (fun s : Campaign2.State => responseEndpointMap s.device) effect
      | true =>
        simpa only [Campaign2.snapshot, Campaign2.core, device] using
          peerTimerArmEffect_endpoints (Campaign2.snapshot g ambient) d pid p timer delay
          (Campaign2.snapshot final after).wg device resident effect

theorem derived_endpoint_frame (pid : PeerId) (entry : Option Device) :
    Ensures (timersSessionDerived pid)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  change Ensures (modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial
    ZERO_KEY_MATERIAL_TICKS >>= fun _ => pure ()) _ _
  refine ensures_bind _ _ (modPeerTimer_endpoint_frame _ _ _ _ entry) ?_
  intro _ g ambient result final after pre run
  cases run
  exact pre

theorem traversal_endpoint_frame (pid : PeerId) (entry : Option Device) :
    Ensures (timersTraversal pid)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  intro g ambient result final after pre run
  apply Eq.trans _ pre
  cases device : g.dev with
  | none =>
    simp [timersTraversal, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [timersTraversal, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := timersTraversal_effect pid d p resident (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl, device⟩ run
      split at effect
      · simpa only [Campaign2.snapshot, Campaign2.core, device] using
          peerTimerArmEffect_endpoints (Campaign2.snapshot g ambient) d pid p .persistentKeepalive
          (p.persistentKeepaliveInterval * HZ) (Campaign2.snapshot final after).wg device resident effect
      · simpa only [Campaign2.snapshot, Campaign2.core, device] using
          congrArg (fun s : Campaign2.State => responseEndpointMap s.device) effect

theorem delTimer_endpoint_frame (pid : PeerId) (timer : PeerTimer) (entry : Option Device) :
    Ensures (delTimer pid timer)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  intro g ambient result final after pre run
  apply Eq.trans _ pre
  cases device : g.dev with
  | none =>
    simp [delTimer, getPeer, getDev, device, invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [delTimer, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := delTimer_exact pid timer p (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl, by change peerAt g pid = some p; simp [peerAt,device,resident]⟩ run
      have projected := congrArg (fun s : Campaign2.Snapshot => responseEndpointMap s.wg.device) effect
      change responseEndpointMap final.dev = _ at projected
      rw [projected]
      change responseEndpointMap (g.dev.map fun d =>
        {d with peers := d.peers.insert pid ((p.setTimer timer none).setWheel timer none)}) =
        responseEndpointMap (some d)
      rw [device]
      exact (pinned_const _private.Leanux.Proofs.WG.Roaming.ResponseRejectionFrames.«0».Leanux.Proofs.WG.Roaming.endpoint_write) d pid p _ resident (by cases timer <;> rfl)

theorem endpoint_frame_remotes {α : Type} (action : WG.M α)
    (frame : ∀ entry, Ensures action
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry)) :
    SameView destinationAt action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact endpointMap_destinations (frame g.dev g ambient result final after rfl run)

theorem modPeerTimer_remotes (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView destinationAt (modPeerTimer site pid timer delay) :=
  endpoint_frame_remotes _ (modPeerTimer_endpoint_frame site pid timer delay)

theorem derived_remotes (pid : PeerId) : SameView destinationAt (timersSessionDerived pid) :=
  endpoint_frame_remotes _ (derived_endpoint_frame pid)

theorem traversal_remotes (pid : PeerId) : SameView destinationAt (timersTraversal pid) :=
  endpoint_frame_remotes _ (traversal_endpoint_frame pid)

theorem delTimer_remotes (pid : PeerId) (timer : PeerTimer) :
    SameView destinationAt (delTimer pid timer) :=
  endpoint_frame_remotes _ (delTimer_endpoint_frame pid timer)

theorem handshakeComplete_remotes (pid : PeerId) (site : HiddenSite) :
    SameView destinationAt (timersHandshakeComplete pid site) := by
  have updateFactor (f : Peer → Peer) :
      modifyPeer pid f = (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have factor : timersHandshakeComplete pid site = (do
      delTimer pid .retransmitHandshake
      modifyPeer pid (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false})
      let now ← hidden site
      modifyPeer pid (fun p => {p with walltimeLastHandshake := now})) := by
    simp only [timersHandshakeComplete,updateFactor,bind_assoc]
  rw [factor]
  exact (delTimer_remotes pid .retransmitHandshake).bind (fun _ =>
    (modifyPeer_remotes pid (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false})
      (fun _ => rfl)).bind (fun _ =>
      (show SameView destinationAt (hidden site : WG.M (List UInt8)) from
        fun initial => hoare_liftAmbient (AmbientM.hidden site)
          (fun g => destinationAt g = initial)).bind (fun now =>
        modifyPeer_remotes pid (fun p => {p with walltimeLastHandshake := now}) (fun _ => rfl))))

end Leanux.Proofs.WG.Roaming
