import Leanux.Proofs.WG.Configuration.PeerTailRouting
import Leanux.Proofs.WG.AllowedIps.RoutingSendFrames

/-! Complete original peer-configuration tail with a failure-retaining routing
completion journal. Concrete send/cleanup frames allow peer deletion; only the
allowed-IP loop maintains its insertion target's residency. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.AllowedIps Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000

theorem peerTailFinishSource_routing (a : PeerAttrs) (peer : Option PeerId)
    (pid : PeerId) (ret : Int) : RetainsRoutingCall (peerTailFinishSource a peer pid ret) := by
  let setup (interval : Nat) (running : Bool) : WG.M Bool := do
    let p ← getPeer pid
    let send ← WG.andM (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
      (WG.andM (branch .peerKeepaliveNonzero (interval != 0))
        (branch .peerKeepaliveRunning running))
    setPeer pid {p with persistentKeepaliveInterval := interval}
    return send
  have setup_same (interval : Nat) (running : Bool) : SameView routingView (setup interval running) := by
    intro initial
    unfold setup
    apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
    intro p
    let R := fun w : WGWorld => routingView w = initial ∧
      (w.dev.bind fun d => d.peers[pid]?.map (·.allowedipsList)) = some p.allowedipsList
    have ambient {α : Type} (a : AmbientM α) : Preserves R (monadLift a : WG.M α) :=
      hoare_liftAmbient a R
    have decisions : Preserves R (WG.andM
        (branch .peerKeepaliveWasZero (p.persistentKeepaliveInterval == 0))
        (WG.andM (branch .peerKeepaliveNonzero (interval != 0))
          (branch .peerKeepaliveRunning running))) := by
      unfold WG.andM
      simp only [branch]
      repeat' first
        | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
        | (rx_retention_head MonadLift.monadLift; exact ambient _)
        | rx_retention_step
    apply hoare_bind _ _ decisions
    intro send
    apply hoare_bind _ _ (routing_setPeer (fun view => view = initial) pid
      {p with persistentKeepaliveInterval := interval})
    intro _
    exact preserves_pure send
  have source : peerTailFinishSource a peer pid ret = (do
      let running := (← getDev).running
      if ← branch .peerHasKeepalive a.keepalive.isSome then
        if ← branch .peerSendKeepalive (← setup (a.keepalive.getD 0) running) then
          sendKeepalive pid
      if ← branch .peerRunning running then sendStagedPackets pid
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      return ret) := by
    simp only [peerTailFinishSource, setup, bind_assoc, pure_bind]
  intro s
  let Q := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have dev : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have hs := fun interval running => (setup_same interval running).wp Q
  have keepalive := RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  have staged := RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have release := RetainsRoutingCall.wp (peerPut_retainsRouting peer) s
  have main : Preserves P (peerTailFinishSource a peer pid ret) := by
    rw [source]
    simp (config := { zeta := false }) only [branch]
    apply preserves_bind dev
    intro d
    apply preserves_bind (ambient (AmbientM.branch .peerHasKeepalive a.keepalive.isSome))
    intro keep
    have tail : Preserves P (do
        if ← branch .peerRunning d.running then sendStagedPackets pid
        peerPut peer
        _ ← branch .peerZeroPsk a.presharedKey.isSome
        return ret) := by
      simp only [branch]
      repeat' first
        | (rx_retention_head sendStagedPackets; exact staged)
        | (rx_retention_head peerPut; exact release)
        | (rx_retention_head MonadLiftT.monadLift; exact ambient _)
        | (rx_retention_head MonadLift.monadLift; exact ambient _)
        | rx_retention_step
    cases keep with
    | false => exact tail
    | true =>
      apply preserves_bind (hs (a.keepalive.getD 0) d.running)
      intro send
      apply preserves_bind (ambient (AmbientM.branch .peerSendKeepalive send))
      intro sendKeep
      cases sendKeep with
      | false => exact tail
      | true => exact preserves_bind keepalive (fun _ => tail)
  apply hoare_consequence main
  · intro w h
    change RetainsRouting s (routingView w)
    dsimp only [_root_.id] at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

def peerConfigTailObserved (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    WGPrefix RoutingCompletion Int :=
  peerAllowedIpsObservedWG a peer pid (fun ret => liftWGPrefix (peerTailFinishSource a peer pid ret))

theorem peerConfigTailObserved_erases (a : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    ErasesStatePrefix (peerConfigTailObserved a peer pid) (peerConfigTailSource a peer pid) := by
  rw [peerConfigTailSource_factor]
  exact peerAllowedIpsObservedWG_erases a peer pid _ _ (fun _ => erasesStatePrefix_lift _)

theorem peerConfigTailObserved_spec (initial : FlatTable × FlatTable)
    (a : PeerAttrs) (shape : PeerAddressShape a) (peer : Option PeerId) (pid : PeerId) :
    StatePrefixEnsures (fun h w _ => CompletionTarget initial pid h w) (CompletionSafe initial)
      (peerConfigTailObserved a peer pid) (fun _ h w _ => CompletionState initial h w) := by
  apply peerAllowedIpsObservedWG_spec initial a shape peer pid
  intro ret
  exact (completion_lift_retains_wg initial _ (peerTailFinishSource_routing a peer pid ret)).consequence
    (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => hi)

end Leanux.Proofs.WG.Configuration
