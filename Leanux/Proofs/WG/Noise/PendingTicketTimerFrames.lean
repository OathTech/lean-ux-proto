import Leanux.Proofs.WG.Noise.PendingTicketRetentionFrames
import Leanux.Proofs.WG.Noise.ResponseSuffixTagFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing TimerDiscipline

def stateView (s : Campaign2.State) : Store PeerId :=
  ⟨s.keypairCounter,fun pid => s.device.bind fun d => pending d pid⟩

theorem stateView_peer_write (entry : Campaign2.State) (d : Device) (pid : PeerId)
    (p q : Peer) (device : entry.device = some d) (resident : d.peers[pid]? = some p)
    (next : q.keypairNext = p.keypairNext) :
    stateView {entry with device := entry.device.map fun d => {d with peers := d.peers.insert pid q}} =
      stateView entry := by
  apply Store.ext
  · rfl
  · funext tracked
    by_cases same : pid = tracked
    · subst tracked
      simp [stateView,pending,device,resident,next]
    · simp [stateView,pending,device,Std.TreeMap.getElem?_insert,same]

theorem wheelPlacementView_pending (entry : Campaign2.State) (d : Device)
    (pid : PeerId) (p : Peer) (timer : PeerTimer) (expires clk : UInt64)
    (device : entry.device = some d) (resident : d.peers[pid]? = some p) :
    stateView (wheelPlacementView entry pid p timer expires clk) = stateView entry := by
  unfold wheelPlacementView
  split
  · exact stateView_peer_write entry d pid p _ device resident (by cases timer <;> rfl)
  · exact stateView_peer_write
      {entry with timerEnqueues := entry.timerEnqueues+1} d pid p _ device resident
      (by cases timer <;> rfl)

theorem peerTimerArmEffect_pending (entry : Campaign2.Snapshot) (d : Device)
    (pid : PeerId) (p : Peer) (timer : PeerTimer) (delay : Nat)
    (final : Campaign2.State) (device : entry.wg.device = some d)
    (resident : d.peers[pid]? = some p)
    (effect : peerTimerArmEffect entry pid p timer delay final) :
    stateView final = stateView entry.wg := by
  unfold peerTimerArmEffect at effect
  split at effect
  · obtain ⟨caller,now,unit,_,_,effect⟩ := effect
    split at effect
    · rw [effect]; rfl
    · obtain ⟨clk,effect⟩ := effect
      rw [effect]
      exact wheelPlacementView_pending _ d pid p timer _ clk device resident
  · rw [effect]
    exact wheelPlacementView_pending entry.wg d pid p timer _ _ device resident

theorem modPeerTimer_frame (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) : SameView view (modPeerTimer site pid timer delay) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
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
      obtain ⟨value,effect⟩ := modPeerTimer_effect site pid timer delay d p resident
        (Campaign2.snapshot g ambient) g ambient result final after ⟨rfl,device⟩ run
      cases result with
      | false =>
        exact congrArg stateView effect
      | true =>
        exact peerTimerArmEffect_pending (Campaign2.snapshot g ambient) d pid p timer delay
          (Campaign2.snapshot final after).wg device resident effect

theorem delTimer_frame (pid : PeerId) (timer : PeerTimer) : SameView view (delTimer pid timer) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [delTimer,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [delTimer,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := delTimer_exact pid timer p (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl,by change peerAt g pid = some p; simp [peerAt,device,resident]⟩ run
      have projected := congrArg (fun s : Campaign2.Snapshot => stateView s.wg) effect
      change view final = _ at projected
      rw [projected]
      exact stateView_peer_write (Campaign2.snapshot g ambient).wg d pid p _
        device resident (by cases timer <;> rfl)

theorem timersSessionDerived_frame (pid : PeerId) : SameView view (timersSessionDerived pid) := by
  change SameView view (modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial
    ZERO_KEY_MATERIAL_TICKS >>= fun _ => pure ())
  exact (modPeerTimer_frame _ _ _ _).bind (fun _ => SameView.pure view ())

theorem timersTraversal_frame (pid : PeerId) : SameView view (timersTraversal pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [timersTraversal,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [timersTraversal,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have effect := timersTraversal_effect pid d p resident (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl,device⟩ run
      split at effect
      · exact peerTimerArmEffect_pending (Campaign2.snapshot g ambient) d pid p .persistentKeepalive
          (p.persistentKeepaliveInterval*HZ) (Campaign2.snapshot final after).wg device resident effect
      · exact congrArg stateView effect

/-- The actual peer read supplies residency; only the pending slot must be kept. -/
theorem modifyPeer_spec_pending_variant (pid : PeerId) (f : Peer → Peer)
    (next : ∀ p, (f p).keypairNext = p.keypairNext) :
    SameView view (modifyPeer pid f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
  cases device : g.dev with
  | none =>
    simp [getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      simp [getPeer,getDev,device,resident,setPeer,modifyDev] at run
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      simpa only [stateView,Campaign2.snapshot,Campaign2.core,view,device,Option.map_some] using
        stateView_peer_write (Campaign2.snapshot g ambient).wg d pid p (f p)
          device resident (next p)

theorem timersHandshakeComplete_frame (pid : PeerId) (site : HiddenSite := .walltimeLastHandshake) :
    SameView view (timersHandshakeComplete pid site) := by
  have modify_eq (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have factor : timersHandshakeComplete pid site = (do
      delTimer pid .retransmitHandshake
      modifyPeer pid (fun p => {p with timerHandshakeAttempts := 0,sentLastminuteHandshake := false})
      let now ← hidden site
      modifyPeer pid (fun p => {p with walltimeLastHandshake := now})) := by
    simp only [timersHandshakeComplete,modify_eq,bind_assoc]
  rw [factor]
  exact (delTimer_frame pid .retransmitHandshake).bind (fun _ =>
    (modifyPeer_spec_pending_variant pid
      (fun p => {p with timerHandshakeAttempts := 0,sentLastminuteHandshake := false})
      (fun _ => rfl)).bind (fun _ =>
    (frame_ambient (AmbientM.hidden site)).bind (fun now =>
      modifyPeer_spec_pending_variant pid (fun p => {p with walltimeLastHandshake := now})
        (fun _ => rfl))))

theorem timersAnyAuthenticatedPacketSent_frame (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketSent pid) := delTimer_frame pid .sendKeepalive

theorem timersAnyAuthenticatedPacketReceived_frame (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketReceived pid) := delTimer_frame pid .newHandshake

theorem timersDataReceived_frame (pid : PeerId) : SameView view (timersDataReceived pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  cases device : g.dev with
  | none =>
    simp [timersDataReceived,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      cases running : d.running with
      | false =>
        simp [timersDataReceived,getDev,device,running,branch,AmbientM.branch] at run
        obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
        rfl
      | true =>
        simp [timersDataReceived,getDev,getPeer,device,running,resident,
          branch,AmbientM.branch,invariant,AmbientM.invariant] at run
        cases run
    | some p =>
      have effect := timersDataReceived_effect pid d p resident (Campaign2.snapshot g ambient)
        g ambient result final after ⟨rfl,device⟩ run
      split at effect
      · split at effect
        · have projected := congrArg stateView effect
          change view final = _ at projected
          rw [projected]
          simpa only [stateView,Campaign2.snapshot,Campaign2.core,view,device,Option.map_some] using stateView_peer_write
            (Campaign2.snapshot g ambient).wg d pid p
            {p with timerNeedAnotherKeepalive := true} device resident rfl
        · split at effect
          · exact congrArg stateView effect
          · exact peerTimerArmEffect_pending (Campaign2.snapshot g ambient) d pid p .sendKeepalive
              KEEPALIVE_TIMEOUT_TICKS (Campaign2.snapshot final after).wg device resident effect
      · exact congrArg stateView effect

end Leanux.Proofs.WG.Noise.PendingTickets
