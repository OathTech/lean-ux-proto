import Leanux.Proofs.WG.AllowedIps.RoutingNapiFrames
import Leanux.Proofs.WG.AllowedIps.RoutingDeviceLifecycleFrames
import Leanux.Proofs.WG.Lifetimes.TimerCallbacks

/-! Concrete timer and device-control routing frames. Timer callbacks and staged
sends may delete a peer; later original getters either establish a fresh setter
witness or Stop. Saved peer lists, successful drains and reference credits are
not premises. Device absence is retained by these normal-endpoint contracts. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem expiredRetransmitHandshake_routing (pid : PeerId) :
    RetainsRoutingCall (expiredRetransmitHandshake pid) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have del : Preserves P (delTimer pid .sendKeepalive) := (delTimer_routing pid .sendKeepalive).wp Q
  have purge : Preserves P (purgeStagedPackets pid) := (purgeStagedPackets_routing pid).wp Q
  have arm : Preserves P (modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS) :=
    (modPeerTimer_routing .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).wp Q
  have endpoint : Preserves P (clearPeerEndpointSrc pid) := (clearPeerEndpointSrc_routing pid).wp Q
  have queued : Preserves P (sendQueuedHandshakeInitiation pid true) :=
    RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid true) s
  let retry : WG.M Unit := do
    let p ← getPeer pid
    setPeer pid {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1}
  have retryFrame : Preserves P retry :=
    (modifyPeer_routing pid (fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
      (fun _ => rfl)).wp Q
  have source : expiredRetransmitHandshake pid = (do
      let attempts := (← getPeer pid).timerHandshakeAttempts
      if ← branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES then
        delTimer pid .sendKeepalive
        purgeStagedPackets pid
        if ← branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial) then
          discard <| modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
      else
        retry
        clearPeerEndpointSrc pid
        sendQueuedHandshakeInitiation pid true) := by
    simp only [expiredRetransmitHandshake, retry, bind_assoc]
  have main : Preserves P (expiredRetransmitHandshake pid) := by
    rw [source]
    routing_tx_source [] using [retryFrame, peer, del, purge, arm, endpoint, queued, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem expiredSendKeepalive_routing (pid : PeerId) :
    RetainsRoutingCall (expiredSendKeepalive pid) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have keep : Preserves P (sendKeepalive pid) := RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  have arm : Preserves P (modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS) :=
    (modPeerTimer_routing .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp Q
  let reset : WG.M Unit := do
    setPeer pid {(← getPeer pid) with timerNeedAnotherKeepalive := false}
  have resetFrame : Preserves P reset :=
    (modifyPeer_routing pid (fun p => {p with timerNeedAnotherKeepalive := false}) (fun _ => rfl)).wp Q
  have source : expiredSendKeepalive pid = (do
      sendKeepalive pid
      if ← branch .keepaliveNeedAnother (← getPeer pid).timerNeedAnotherKeepalive then
        reset
        discard <| modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS) := by
    simp only [expiredSendKeepalive, reset, bind_assoc]
  have main : Preserves P (expiredSendKeepalive pid) := by
    rw [source]
    routing_tx_source [] using [resetFrame, peer, keep, arm, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem expiredNewHandshake_routing (pid : PeerId) :
    RetainsRoutingCall (expiredNewHandshake pid) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have endpoint : Preserves P (clearPeerEndpointSrc pid) := (clearPeerEndpointSrc_routing pid).wp Q
  have queued : Preserves P (sendQueuedHandshakeInitiation pid false) :=
    RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid false) s
  have main : Preserves P (expiredNewHandshake pid) := by
    routing_tx_source [expiredNewHandshake] using [endpoint, queued]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem expiredZeroKeyMaterial_routing (pid : PeerId) :
    RetainsRoutingCall (expiredZeroKeyMaterial pid) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have acquire : Preserves P (peerGet pid) := (peerGet_routing pid).wp Q
  have put : Preserves P (peerPut (some pid)) := RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  have enqueue : Preserves P (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}) :=
    (modifyDev_routing (fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}) (fun _ => rfl)).wp Q
  have main : Preserves P (expiredZeroKeyMaterial pid) := by
    routing_tx_source [expiredZeroKeyMaterial, peekQueuedUnit, recordQueued]
      using [peer, device, acquire, put, enqueue, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem expiredSendPersistentKeepalive_routing (pid : PeerId) :
    RetainsRoutingCall (expiredSendPersistentKeepalive pid) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have keep : Preserves P (sendKeepalive pid) := RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  have main : Preserves P (expiredSendPersistentKeepalive pid) := by
    routing_tx_source [expiredSendPersistentKeepalive] using [peer, keep, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem timerCallback_routing (pid : PeerId) (timer : PeerTimer) :
    RetainsRoutingCall (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshake_routing pid
  | sendKeepalive => exact expiredSendKeepalive_routing pid
  | newHandshake => exact expiredNewHandshake_routing pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterial_routing pid
  | persistentKeepalive => exact expiredSendPersistentKeepalive_routing pid

theorem wgOpen_routing : RetainsRoutingCall wgOpen := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have socket (port : Nat) : Preserves P (socketInit port) :=
    (socketControl_routing_native _ (socketInit_sameSocket port)).wp Q
  have send (pid : PeerId) : Preserves P (sendStagedPackets pid) :=
    RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have keep (pid : PeerId) : Preserves P (sendKeepalive pid) := RetainsRoutingCall.wp (sendKeepalive_routing pid) s
  have main : Preserves P wgOpen := by
    routing_tx_source [wgOpen] using [device, peer, socket, send, keep, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem wgUp_routing : RetainsRoutingCall wgUp := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have edit (running : Bool) : Preserves P (modifyDev fun d => {d with running}) :=
    (modifyDev_routing (fun d => {d with running}) (fun _ => rfl)).wp Q
  have opened : Preserves P wgOpen := RetainsRoutingCall.wp wgOpen_routing s
  have main : Preserves P wgUp := by
    routing_tx_source [wgUp] using [edit, opened]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem netnsPreExit_routing : SameView routingView netnsPreExit := by
  intro s
  let Q : Option RoutingState → Prop := fun t => t = s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have socket : Preserves P (socketReinit none none) :=
    (socketControl_routing_native _ (socketReinit_sameSocket none none)).wp Q
  have endpoint (pid : PeerId) : Preserves P (clearPeerEndpointSrc pid) := (clearPeerEndpointSrc_routing pid).wp Q
  have edit : Preserves P (modifyDev fun d => {d with carrier := false, creatingNet := false}) :=
    (modifyDev_routing (fun d => {d with carrier := false, creatingNet := false}) (fun _ => rfl)).wp Q
  change Preserves P _
  routing_tx_source [netnsPreExit] using [read, device, socket, endpoint, edit, ambient]

end Leanux.Proofs.WG.AllowedIps
