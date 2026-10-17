import Leanux.Proofs.WG.AllowedIps.RoutingTxFrames
import Leanux.Proofs.WG.Queues.RxPollPrefix
import Leanux.Proofs.WG.Queues.RxRingWorker

/-! Original receive completion, poll and decrypt-worker routing frames.
Callbacks have explicit routing contracts; the stack callback is discharged
concretely. Normal endpoints permit peer deletion and retain orphan owners. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.WG.Queues Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem decryptPacket_routing (pkt : RxPacket) : SameView routingView (decryptPacket pkt) := by
  have expired := fun d birth age => show SameView routingView _ from
    (branchExpired_sameWGWorld d birth age).factor routingView
  routing_handshake_source [decryptPacket] using [expired, setKeypair_routing]

theorem counterValidate_routing (kp : KeypairId) (nonce : Nat) :
    SameView routingView (counterValidate kp nonce) := by
  intro initial
  let P := fun w : WGWorld => routingView w = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have key : Preserves P (getKeypair kp) := (getKeypair_routing kp).wp (fun v => v = initial)
  have write (k : Keypair) : Preserves P (setKeypair kp k) :=
    (setKeypair_routing kp k).wp (fun v => v = initial)
  change Preserves P _
  routing_tx_source [counterValidate] using [key, write, ambient]

theorem receivedWithKeypair_routing (pid : PeerId) (kp : KeypairId) :
    SameView routingView (receivedWithKeypair pid kp) := by
  routing_handshake_source [receivedWithKeypair,
    _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_routing]

theorem timersHandshakeComplete_routing (pid : PeerId) (site : HiddenSite) :
    SameView routingView (timersHandshakeComplete pid site) := by
  routing_handshake_source [timersHandshakeComplete] using [delTimer_routing]

theorem timersAnyAuthenticatedPacketReceived_routing (pid : PeerId) :
    SameView routingView (timersAnyAuthenticatedPacketReceived pid) := delTimer_routing pid .newHandshake

theorem timersDataReceived_routing (pid : PeerId) : SameView routingView (timersDataReceived pid) := by
  routing_handshake_source [timersDataReceived, Functor.discard] using [modPeerTimer_routing]

theorem keepKeyFreshRx_routing (pid : PeerId) : RetainsRoutingCall (keepKeyFreshRx pid) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have peer : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have key (kp : KeypairId) : Preserves P (getKeypair kp) := (getKeypair_routing kp).wp Q
  have expired (d : Decision) (birth : Int64) (age : Nat) : Preserves P (branchExpired d birth age) :=
    (branchExpired_sameWGWorld d birth age).wp P
  have queued : Preserves P (sendQueuedHandshakeInitiation pid false) :=
    RetainsRoutingCall.wp (sendQueuedHandshakeInitiation_routing pid false) s
  have update : Preserves P (do
      setPeer pid {(← getPeer pid) with sentLastminuteHandshake := true}) :=
    (modifyPeer_routing pid (fun p => {p with sentLastminuteHandshake := true})
      (fun _ => rfl)).wp Q
  let finish : WG.M Unit := do
    setPeer pid {(← getPeer pid) with sentLastminuteHandshake := true}
    sendQueuedHandshakeInitiation pid false
  have done : Preserves P finish := by
    simpa only [finish, bind_assoc] using preserves_bind update (fun _ => queued)
  have source : keepKeyFreshRx pid = (do
      if ← branch .rxFreshSentLastminute (← getPeer pid).sentLastminuteHandshake then return
      let current := (← getPeer pid).keypairCurrent
      let send ← WG.andM (branch .rxFreshKeypair current.isSome) do
        let some id := current | invariant "unreachable"
        let k ← getKeypair id
        WG.andM (branch .rxFreshValid k.sending.isValid) do
          WG.andM (branch .rxFreshInitiator k.iAmTheInitiator) do
            branchExpired .rxFreshExpired k.sending.birthdate
              (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT)
      if ← branch .rxFreshSend send then finish) := rfl
  have main : Preserves P (keepKeyFreshRx pid) := by
    rw [source]
    routing_tx_source [] using [peer, key, expired, done, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem dishonest_routing (why : Dishonest) : SameView routingView (dishonest why) :=
  modifyDev_routing _ (fun d => by cases why <;> rfl)

theorem updateRxStats_routing (pid : PeerId) (len : Nat) :
    SameView routingView (updateRxStats pid len) := by
  routing_handshake_source [updateRxStats] using [modifyDev_routing]
  all_goals rfl

theorem consumeDataDone_routing (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    RetainsRoutingCall (consumeDataDone pid pkt endpoint) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) :=
    hoare_liftAmbient a P
  have endpointSet : Preserves P (setPeerEndpoint pid endpoint) := (setPeerEndpoint_routing pid endpoint).wp Q
  have received : Preserves P (receivedWithKeypair pid pkt.keypair) := (receivedWithKeypair_routing pid pkt.keypair).wp Q
  have handshake : Preserves P (timersHandshakeComplete pid .walltimeLastHandshakeData) :=
    (timersHandshakeComplete_routing pid .walltimeLastHandshakeData).wp Q
  have staged : Preserves P (sendStagedPackets pid) := RetainsRoutingCall.wp (sendStagedPackets_routing pid) s
  have fresh : Preserves P (keepKeyFreshRx pid) := RetainsRoutingCall.wp (keepKeyFreshRx_routing pid) s
  have authenticated : Preserves P (timersAnyAuthenticatedPacketReceived pid) :=
    (timersAnyAuthenticatedPacketReceived_routing pid).wp Q
  have traversal : Preserves P (timersTraversal pid) := (timersTraversal_routing pid).wp Q
  have dataReceived : Preserves P (timersDataReceived pid) := (timersDataReceived_routing pid).wp Q
  have stats (len : Nat) : Preserves P (updateRxStats pid len) := (updateRxStats_routing pid len).wp Q
  have dishonest (why : Dishonest) : Preserves P (WG.dishonest why) := (dishonest_routing why).wp Q
  have ecn (protocol outer : Nat) (bytes : List UInt8) : Preserves P (inetEcnDecapsulate protocol outer bytes) :=
    (routing_kernel _ (inetEcnDecapsulate_sameWGStore protocol outer bytes)).wp Q
  have lookup (protocol : Nat) (bytes : List UInt8) : Preserves P (lookupSrc protocol bytes) :=
    (lookupSrc_routing protocol bytes).wp Q
  have put (peer : Option PeerId) : Preserves P (peerPut peer) :=
    RetainsRoutingCall.wp (peerPut_retainsRouting peer) s
  have main : Preserves P (consumeDataDone pid pkt endpoint) := by
    routing_tx_source [consumeDataDone] using [endpointSet, received, handshake, staged, fresh,
      authenticated, traversal, dataReceived, stats, dishonest, ecn, lookup, put, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

private theorem peekRxQueue_routing (pid : PeerId) : SameView routingView (peekRxQueue pid) := by
  have peek := fun (q : PrevQueue SkbId) => show SameView routingView _ from
    routing_kernel _ (prevQueuePeek_sameWGStore q)
  routing_handshake_source [peekRxQueue] using [peek]

private theorem dropRxQueue_routing (pid : PeerId) : SameView routingView (dropRxQueue pid) := by
  simp only [dropRxQueue, getPeer_twice]
  exact modifyPeer_routing pid _ (fun _ => rfl)

private theorem completeRxQueue_routing (pid : PeerId) : SameView routingView (completeRxQueue pid) :=
  modifyPeer_routing pid _ (fun _ => rfl)

theorem groNormalList_routing (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) (g : GroState) : ProductRetainsRoutingCall (groNormalList cb g) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have callback (xs : List (List UInt8)) : Preserves P (cb xs) := RetainsRoutingCall.wp (hc xs) s
  have main : Preserves P (groNormalList cb g) := by
    routing_tx_source [groNormalList] using [callback, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem groNormalOne_routing (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) (g : GroState) (pkt : List UInt8) (segs : Nat) :
    ProductRetainsRoutingCall (groNormalOne cb g pkt segs) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have list (g : GroState) : Preserves P (groNormalList cb g) :=
    RetainsRoutingCall.wp (groNormalList_routing cb hc g) s
  have main : Preserves P (groNormalOne cb g pkt segs) := by
    routing_tx_source [groNormalOne] using [list, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem napiGroReceive_routing (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) (g : GroState) (pkt : List UInt8) :
    ProductRetainsRoutingCall (napiGroReceive cb g pkt) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have one (g : GroState) (pkt : List UInt8) (segs : Nat) : Preserves P (groNormalOne cb g pkt segs) :=
    RetainsRoutingCall.wp (groNormalOne_routing cb hc g pkt segs) s
  have main : Preserves P (napiGroReceive cb g pkt) := by
    routing_tx_source [napiGroReceive] using [one, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem napiGroFlushAll_routing (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) (g : GroState) :
    ProductRetainsRoutingCall (napiGroFlushAll cb g) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have one (g : GroState) (pkt : List UInt8) (segs : Nat) : Preserves P (groNormalOne cb g pkt segs) :=
    RetainsRoutingCall.wp (groNormalOne_routing cb hc g pkt segs) s
  have list (g : GroState) : Preserves P (groNormalList cb g) :=
    RetainsRoutingCall.wp (groNormalList_routing cb hc g) s
  have main : Preserves P (napiGroFlushAll cb g) := by
    routing_tx_source [napiGroFlushAll] using [one, list, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem rxPoll_routing (pid : PeerId) (budget : Nat) (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, ProductRetainsRoutingCall (cb xs)) : ProductRetainsRoutingCall (rxPoll pid budget cb) := by
  rw [← rxPollGrouped_eq]
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have lifted {α : Type} (a : WG.M α) (ha : SameView routingView a) : Preserves P (liftWG a) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView a ha (fun _ _ _ h => h)).wp Q
  have packets {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  have readPacket (id : SkbId) : Preserves P (liftWG (getRxSkb id)) :=
    lifted _ (packets _)
  have writePacket (id : SkbId) (f : RxPacket → RxPacket) : Preserves P (liftWG (setRxSkb id f)) :=
    lifted _ (packets _)
  have freePacket (id : SkbId) : Preserves P (liftWG (freeRxSkb id)) :=
    lifted _ (packets _)
  have lift {α : Type} (a : WG.M α) : (liftM a : Leanux.M α) = liftWG a := rfl
  have peek : Preserves P (liftWG (peekRxQueue pid)) := lifted _ (peekRxQueue_routing pid)
  have drop : Preserves P (liftWG (dropRxQueue pid)) := lifted _ (dropRxQueue_routing pid)
  have complete : Preserves P (liftWG (completeRxQueue pid)) := lifted _ (completeRxQueue_routing pid)
  have counter (key : KeypairId) (nonce : Nat) : Preserves P (liftWG (counterValidate key nonce)) :=
    lifted _ (counterValidate_routing key nonce)
  have endpoint (src : SkbSource) : Preserves P (liftWG (endpointFromSkb src)) :=
    lifted _ (routing_kernel _ (endpointFromSkb_sameWGStore src))
  have consume (pkt : RxPacket) (ep : Endpoint) : Preserves P (liftWG (consumeDataDone pid pkt ep)) :=
    RetainsRoutingCall.wp ((consumeDataDone_routing pid pkt ep).liftWG) s
  have gro (g : GroState) (pkt : List UInt8) : Preserves P (napiGroReceive cb g pkt) :=
    RetainsRoutingCall.wp (napiGroReceive_routing cb hc g pkt) s
  have flush (g : GroState) : Preserves P (napiGroFlushAll cb g) :=
    RetainsRoutingCall.wp (napiGroFlushAll_routing cb hc g) s
  have key (kp : Option KeypairId) : Preserves P (liftWG (keypairPut kp false)) :=
    lifted _ (keypairPut_routing kp false)
  have put : Preserves P (liftWG (peerPut (some pid))) :=
    RetainsRoutingCall.wp ((peerPut_retainsRouting (some pid)).liftWG) s
  have go (first : Option SkbId) : Preserves P (liftWG (WG.andM (branch .rxPollPacket first.isSome) do
      let some f := first | invariant "unreachable"
      branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted))) := by
    apply lifted
    routing_handshake_source [WG.andM, getRxSkb] using [packets]
  have main : Preserves P (rxPollGrouped pid budget cb) := by
    simp (config := { zeta := false }) only [rxPollGrouped, Std.Legacy.Range.forIn_eq_forIn_range', lift]
    routing_tx_source [] using [go, peek, drop, complete, counter, endpoint, consume, gro, flush,
      key, put, readPacket, writePacket, freePacket, ambient]
    all_goals exact go _
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem actualRxPoll_routing (pid : PeerId) (budget : Nat) :
    ProductRetainsRoutingCall (rxPoll pid budget (fun xs => xs.forM Leanux.Env.deliverInner)) :=
  rxPoll_routing pid budget _ stackForM_routing

theorem enqueuePerPeerRx_routing (irq : Leanux.M Unit) (hi : ProductRetainsRoutingCall irq)
    (id : SkbId) (state : PacketState) : ProductRetainsRoutingCall (enqueuePerPeerRx irq id state) := by
  let before : WG.M PeerId := do
    let pid ← IndexOwner.peerDeref (.keypair (← getRxSkb id).keypair)
    peerGet pid
    let p ← getPeer pid
    if !(p.rxQueue.all.contains id) then
      invariant "a decrypted packet that is not on its peer's rx_queue"
    setRxSkb id fun q => {q with state}
    setPeer pid {p with napiScheduled := true}
    pure pid
  have before_frame : SameView routingView before := by
    have packets {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
      intro initial
      apply hoare_liftSkb a
      intro w d store hi hd
      simpa only [routingView, hd, Option.map_some, routingState] using hi
    routing_handshake_source [before, getRxSkb, setRxSkb] using [packets, peerGet_routing]
  have factor : enqueuePerPeerRx irq id state =
      (do let pid ← liftWG before; irq; liftWG (peerPut (some pid))) := by
    have lift {α : Type} (a : WG.M α) : (liftM a : Leanux.M α) = liftWG a := rfl
    have ambientLift {α : Type} (a : AmbientM α) :
        liftWG (monadLift a : WG.M α) = (monadLift a : Leanux.M α) :=
      liftWG_ambient a
    have bindIte {α β : Type} (c : Prop) [Decidable c]
        (a b : Leanux.M α) (f : α → Leanux.M β) :
        ((if c then a else b) >>= f) = (if c then a >>= f else b >>= f) := by
      split <;> rfl
    simp only [enqueuePerPeerRx, before, lift, liftWG_bind, bind_assoc]
    simp only [apply_ite, bindIte, liftWG_bind, liftWG_pure, invariant,
      ambientLift, bind_assoc, pure_bind]
  rw [factor]
  intro initial
  let Q := RetainsRouting initial
  let P := fun w : World => Q (routingView w.wg)
  have beforeFrame : Preserves P (liftWG before) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView before
      before_frame (fun _ _ _ h => h)).wp Q
  have irqFrame : Preserves P irq := RetainsRoutingCall.wp hi initial
  have putFrame (pid : PeerId) : Preserves P (liftWG (peerPut (some pid))) :=
    RetainsRoutingCall.wp ((peerPut_retainsRouting (some pid)).liftWG) initial
  have main : Preserves P (do let pid ← liftWG before; irq; liftWG (peerPut (some pid))) :=
    preserves_bind beforeFrame (fun pid => preserves_bind irqFrame (fun _ => putFrame pid))
  apply hoare_consequence main
  · intro w he
    change RetainsRouting initial _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

private theorem decryptPoll_routing : SameView routingView RxRing.pollSource := by
  routing_handshake_source [RxRing.pollSource] using [modifyDev_routing]
  all_goals rfl

theorem decryptStep_routing (softirq irq : Leanux.M Unit)
    (hs : ProductRetainsRoutingCall softirq) (hi : ProductRetainsRoutingCall irq) :
    ProductRetainsRoutingCall (decryptStep softirq irq) := by
  rw [← RxRing.stepSource_eq]
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have lifted {α : Type} (a : WG.M α) (ha : SameView routingView a) : Preserves P (liftWG a) :=
    (sameView_liftWG (fun w => routingView w.wg) routingView a ha (fun _ _ _ h => h)).wp Q
  have packets {α : Type} (a : SkbM α) : SameView routingView (liftSkb a) := by
    intro initial
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  have readPacket (id : SkbId) : Preserves P (liftWG (getRxSkb id)) :=
    lifted _ (packets _)
  have writePacket (id : SkbId) (f : RxPacket → RxPacket) : Preserves P (liftWG (setRxSkb id f)) :=
    lifted _ (packets _)
  have freePacket (id : SkbId) : Preserves P (liftWG (freeRxSkb id)) :=
    lifted _ (packets _)
  have lift {α : Type} (a : WG.M α) : (liftM a : Leanux.M α) = liftWG a := rfl
  have softirqFrame : Preserves P softirq := RetainsRoutingCall.wp hs s
  have poll : Preserves P (liftWG RxRing.pollSource) := lifted _ decryptPoll_routing
  have decrypt (pkt : RxPacket) : Preserves P (liftWG (decryptPacket pkt)) := lifted _ (decryptPacket_routing pkt)
  have queue (id : SkbId) (state : PacketState) : Preserves P (enqueuePerPeerRx irq id state) :=
    RetainsRoutingCall.wp (enqueuePerPeerRx_routing irq hi id state) s
  have main : Preserves P (RxRing.stepSource softirq irq) := by
    simp (config := { zeta := false }) only [RxRing.stepSource, lift]
    routing_tx_source [] using [softirqFrame, poll, decrypt, queue, readPacket, writePacket, freePacket, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem decryptIter_routing (softirq irq : Leanux.M Unit) (need : Leanux.M Bool)
    (hs : ProductRetainsRoutingCall softirq) (hi : ProductRetainsRoutingCall irq) (hn : ProductRetainsRoutingCall need) :
    ProductRetainsRoutingCall (decryptIter softirq irq need) := by
  apply workerIter_routing _ _ _ _ (decryptStep_routing softirq irq hs hi)
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : World => Q (routingView w.wg)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ h => h)
  have needFrame : Preserves P need := RetainsRoutingCall.wp hn s
  have main : Preserves P (do let n ← need; branch .decWorkerNeedResched n) := by
    routing_tx_source [] using [needFrame, ambient]
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [_root_.id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.AllowedIps
