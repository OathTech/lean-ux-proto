import Leanux.Proofs.WG.RetirementSecurity.HolderReceiveFrames

/-! The original initiation and response receive arms close their real peer
loan after the session/socket/keepalive continuation. No independent final
peer-release readiness premise is needed at this native caller. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderReceive
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open HolderConsume
variable {selected : PeerId}

theorem inv_points {action : WG.M α} (keys : SameView ownershipPointView action)
    (peers : SameView peerView action) : Preserves (HolderConsume.Inv temporary selected) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨before.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp keys w a result v b run),
    before.2.view ((ProjectedAction.iff_run_ambient _ _ _).mp peers w a result v b run)⟩

theorem stats (bytes : Nat) : Preserves (HolderConsume.Inv temporary selected)
    (modifyDev fun d => {d with rxPackets:=d.rxPackets+1,rxBytes:=d.rxBytes+bytes}) := by
  apply inv_points
  · exact ownership_modifyDev _ (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    simp [peerView,Option.map_map,Option.bind_map,Function.comp_def]

theorem finish (pid : PeerId) (msg : List UInt8) : Hoare (HandshakeReceive.finish (some pid) pid msg)
    (HolderConsume.Inv temporary pid) (fun _ => HolderAccount temporary) := by
  unfold HandshakeReceive.finish timersAnyAuthenticatedPacketReceived
  rw [←bind_assoc]
  apply hoare_bind _ _ (HolderConsume.update pid (fun p => {p with rxBytes:=p.rxBytes+msg.length})
    (fun _=>rfl) (fun _=>rfl))
  intro _
  apply hoare_bind _ _ (stats msg.length)
  intro _
  apply hoare_bind _ _ (inv_points (delTimer_ownership _ _)
    (control_peers (delTimer_control _ _)))
  intro _
  apply hoare_bind _ _ (inv_points (timersTraversal_ownership _)
    (control_peers (timersTraversal_control _)))
  intro _
  exact payment pid

theorem finish_selected (pid : PeerId) (msg : List UInt8) : Hoare
    (HandshakeReceive.finishSelected (some pid) msg)
    (Selected temporary pid) (fun _ => HolderAccount temporary) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  change ((HandshakeReceive.finish (some pid) pid msg).run w).run
    (CounterWindow.record a .hsWrongPacket false)=.ok ((result,v),b) at run
  exact (hoare_iff_run_ambient _ _ _).mp (finish pid msg) w _ result v b ⟨before.1.1.1,before.2⟩ run

theorem initiation_arm (msg : List UInt8) (src : SkbSource) : Hoare
    (HandshakeArms.initiation msg src) (Ready temporary) (fun _ => HolderAccount temporary) := by
  unfold HandshakeArms.initiation
  apply hoare_bind _ _ (consume msg false)
  intro peer
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases peer with
  | none =>
    change Except.ok (((),w),CounterWindow.record a .hsInitNoPeer true)=.ok ((result,v),b) at run
    cases run
    exact before.1.1.1
  | some pid =>
    change ((do
      setPeerEndpointFromSkb pid src
      sendHandshakeResponse pid
      HandshakeReceive.finishSelected (some pid) msg).run w).run
      (CounterWindow.record a .hsInitNoPeer false)=.ok ((result,v),b) at run
    have tail : Hoare (do
        setPeerEndpointFromSkb pid src
        sendHandshakeResponse pid
        HandshakeReceive.finishSelected (some pid) msg)
        (Selected temporary pid) (fun _ => HolderAccount temporary) :=
      hoare_bind _ _ (endpoint pid src) (fun _ =>
        hoare_bind _ _ (send_response pid) (fun _ => finish_selected pid msg))
    exact (hoare_iff_run_ambient _ _ _).mp tail w _ result v b ⟨before.1,before.2 pid rfl⟩ run

theorem response_arm (msg : List UInt8) (src : SkbSource) : Hoare
    (HandshakeArms.response msg src) (Ready temporary) (fun _ => HolderAccount temporary) := by
  unfold HandshakeArms.response
  apply hoare_bind _ _ (consume msg true)
  intro peer
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases peer with
  | none =>
    change Except.ok (((),w),CounterWindow.record a .hsRespNoPeer true)=.ok ((result,v),b) at run
    cases run
    exact before.1.1.1
  | some pid =>
    change ((do
      setPeerEndpointFromSkb pid src
      HandshakeReceive.responseSession pid
      HandshakeReceive.finishSelected (some pid) msg).run w).run
      (CounterWindow.record a .hsRespNoPeer false)=.ok ((result,v),b) at run
    have tail : Hoare (do
        setPeerEndpointFromSkb pid src
        HandshakeReceive.responseSession pid
        HandshakeReceive.finishSelected (some pid) msg)
        (Selected temporary pid) (fun _ => HolderAccount temporary) :=
      hoare_bind _ _ (endpoint pid src) (fun _ =>
        hoare_bind _ _ (response_session pid) (fun _ => finish_selected pid msg))
    exact (hoare_iff_run_ambient _ _ _).mp tail w _ result v b ⟨before.1,before.2 pid rfl⟩ run

end Leanux.Proofs.WG.RetirementSecurity.HolderReceive
