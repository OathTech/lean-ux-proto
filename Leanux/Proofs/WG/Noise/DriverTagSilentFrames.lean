import Leanux.Proofs.WG.Noise.TransmitRulesSource
import Leanux.Proofs.WG.Noise.SendSkbRulesSource
import Leanux.Proofs.WG.Index.EncryptRuleSource
import Leanux.Proofs.WG.Noise.DataCompletionRulesSource
import Leanux.Proofs.WG.Noise.DriverTagFlushCallerSource
import Leanux.Proofs.WG.Noise.DriverTagControlFrames
import Leanux.Proofs.WG.Noise.DriverTagConfigurationFrames
import Leanux.Proofs.WG.Noise.InitiationCoverageFrames
import Leanux.Proofs.WG.Queues.CurrentSlotTransmit
import Leanux.Proofs.WG.Queues.CurrentSlotWorkers
import Leanux.Proofs.WG.TimerDiscipline.DataDoneSource
import Leanux.Proofs.WG.TimerDiscipline.ArmingPrefixesSource
import Leanux.Proofs.WG.Noise.DriverTagProductFrames
import Leanux.Proofs.WG.Packets.PublicationIdentity

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Silent
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues TimerDiscipline

def Retained (entry : TagMap) (g : WGWorld) : Prop := TagsRetained entry (tagView g)

theorem of_frame {α : Type} (entry : TagMap) (action : WG.M α)
    (frame : SameView tagView action) : Preserves (Retained entry) action :=
  frame.wp (TagsRetained entry)

theorem of_retained {α : Type} (entry : TagMap) (action : WG.M α)
    (frame : ∀ g ambient result final after,
      ((action.run g).run ambient) = .ok ((result,final),after) →
      TagsRetained (tagView g) (tagView final)) :
    Preserves (Retained entry) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g ambient result final after pre run
  exact pre.trans (frame g ambient result final after run)

theorem of_staging {α : Type} (entry : TagMap) (action : WG.M α)
    (frame : ∀ g, Ensures action (Index.StagingFrame g) (fun _ => Index.StagingFrame g)) :
    Preserves (Retained entry) action :=
  of_retained entry action (Index.staging_tags action frame)

theorem update (entry : TagMap) (pid : PeerId) (f : Peer → Peer)
    (tag : ∀ p, (f p).handshakeState = p.handshakeState) :
    Preserves (Retained entry) (getPeer pid >>= fun p => setPeer pid (f p)) :=
  of_frame entry _ (modifyPeer_frame pid f tag)

theorem update_bind {α : Type} (entry : TagMap) (pid : PeerId) (f : Peer → Peer)
    (next : Unit → WG.M α) (tag : ∀ p, (f p).handshakeState = p.handshakeState)
    (tail : ∀u, Preserves (Retained entry) (next u)) :
    Preserves (Retained entry) (getPeer pid >>= fun p => setPeer pid (f p) >>= next) := by
  simpa only [bind_assoc] using preserves_bind (update entry pid f tag) tail

theorem getKeypair_frame (kid : KeypairId) : SameView tagView (getKeypair kid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient key final after run
  exact congrArg tagView (KeyTimes.getKeypair_return kid g final key ambient after run).1

theorem packet_frame {α : Type} (action : SkbM α) : SameView tagView (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro g d store pre device
  change responseTagMap (some d) = initial
  simpa only [tagView,device] using pre

theorem queued (entry : TagMap) (pid : PeerId) (retry : Bool) :
    Preserves (Retained entry) (sendQueuedHandshakeInitiation pid retry) :=
  of_staging entry _ (fun g => (ensures_iff _ _ _).mpr (Index.sendQueuedHandshakeInitiation_staging pid retry g))

theorem peerPut (entry : TagMap) (pid : Option PeerId) :
    Preserves (Retained entry) (WG.peerPut pid) :=
  of_staging entry _ (fun g => Index.staging_peerPut g pid)

theorem keypairPut (entry : TagMap) (key : Option KeypairId) (unreference : Bool) :
    Preserves (Retained entry) (WG.keypairPut key unreference) :=
  of_staging entry _ (fun g => (ensures_iff _ _ _).mpr (Index.keypairPut_staging key unreference g))

theorem modTimer (entry : TagMap) (site : HiddenSite) (pid : PeerId)
    (timer : PeerTimer) (delay : Nat) :
    Preserves (Retained entry) (modPeerTimer site pid timer delay) := by
  apply of_frame
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact ResponseSuffix.modPeerTimer_tag_frame site pid timer delay g.dev g ambient result final after rfl run

theorem delTimer (entry : TagMap) (pid : PeerId) (timer : PeerTimer) :
    Preserves (Retained entry) (WG.delTimer pid timer) := by
  apply of_frame
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact ResponseSuffix.delTimer_tag_frame pid timer g.dev g ambient result final after rfl run

open Origins.HandshakeSources in
macro "silent_native_step " entry:term : tactic => `(tactic| first
  | (receive_update_head setPeer
     apply update $entry _ _ ?_
     intro p; rfl)
  | (receive_update_head Bind.bind
     apply update_bind $entry _ _ _ ?_
     · intro p; rfl
     intro u)
  | (rx_retention_head getPeer; exact of_frame $entry _ (getPeer_frame _))
  | (rx_retention_head getKeypair; exact of_frame $entry _ (getKeypair_frame _))
  | (rx_retention_head getDev; exact of_frame $entry _ (store_frame getDev_sameWGStore))
  | (rx_retention_head modifyDev
     exact of_frame $entry _ (modifyDev_frame _ (fun _ => rfl)))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ite; apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
  | rx_retention_step)

theorem timerCallback_retained (entry : TagMap) (pid : PeerId) (timer : PeerTimer) :
    Preserves (Retained entry) (timerCallback pid timer) := by
  have modify_eq (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have retry_source : expiredRetransmitHandshake pid = (do
      let attempts := (← getPeer pid).timerHandshakeAttempts
      if ← branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES then
        WG.delTimer pid .sendKeepalive
        purgeStagedPackets pid
        if ← branch .retransmitZeroKeyNotPending !((← getPeer pid).timerPending .zeroKeyMaterial) then
          discard <| modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
      else
        modifyPeer pid (fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1})
        clearPeerEndpointSrc pid
        sendQueuedHandshakeInitiation pid true) := by
    simp only [expiredRetransmitHandshake,modify_eq,bind_assoc]
  have keepalive_source : expiredSendKeepalive pid = (do
      sendKeepalive pid
      if ← branch .keepaliveNeedAnother (← getPeer pid).timerNeedAnotherKeepalive then
        modifyPeer pid (fun p => {p with timerNeedAnotherKeepalive := false})
        discard <| modPeerTimer .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS) := by
    simp only [expiredSendKeepalive,modify_eq,bind_assoc]
  cases timer <;> simp only [timerCallback]
  all_goals first
    | rw [retry_source]
    | rw [keepalive_source]
    | unfold expiredNewHandshake
    | unfold expiredZeroKeyMaterial
    | unfold expiredSendPersistentKeepalive
  all_goals try simp (config := {zeta := false}) only
    [branch,branchCmp,peekQueuedUnit,recordQueued,discard,map_const,Function.comp_def,map_eq_pure_bind]
  all_goals repeat' first
    | (rx_retention_head modifyPeer
       exact update entry _ _ (fun _ => rfl))
    | (rx_retention_head clearPeerEndpointSrc; exact of_frame entry _ (clearPeerEndpointSrc_frame _))
    | (rx_retention_head purgeStagedPackets; exact of_frame entry _ (Control.purgeStagedPackets_tag_frame _))
    | (rx_retention_head WG.delTimer; exact delTimer entry _ _)
    | (rx_retention_head modPeerTimer; exact modTimer entry _ _ _ _)
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued entry _ _)
    | (rx_retention_head sendKeepalive; exact of_retained entry _ (Index.sendKeepalive_tags_retained _))
    | (rx_retention_head peerGet; exact of_frame entry _ (peerGet_frame _))
    | (rx_retention_head WG.peerPut; exact peerPut entry _)
    | silent_native_step entry


theorem send4_frame (pid : PeerId) (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView tagView (send4 e (some pid) bytes ds exactRx) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact tagMap_frame_of_sendWork _ pid (send4_sendWorkView pid e bytes ds exactRx)
    g.dev g ambient result final after rfl run

theorem send6_frame (pid : PeerId) (e : Endpoint) (bytes : List UInt8) (ds : Nat) (exactRx : Bool) :
    SameView tagView (send6 e (some pid) bytes ds exactRx) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact tagMap_frame_of_sendWork _ pid (send6_sendWorkView pid e bytes ds exactRx)
    g.dev g ambient result final after rfl run

theorem sendSkb_retained (entry : TagMap) (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Preserves (Retained entry) (sendSkbToPeer pid bytes ds) :=
  DataCompletionRules.sendSkb_preserves _ pid bytes ds
    (fun e exactRx => of_frame entry _ (send4_frame pid e bytes ds exactRx))
    (fun e exactRx => of_frame entry _ (send6_frame pid e bytes ds exactRx))
    (update entry pid (fun p => {p with txBytes:=p.txBytes+bytes.length}) (fun _ => rfl))

theorem guardedArm_frame (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) :
    SameView tagView (do if ← modPeerTimerGuard pid then armTimer pid timer delay caller) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact InitiationCaller.guardedArm_tag_frame pid timer delay caller g.dev g ambient result final after rfl run

theorem timersDataSent_frame (pid : PeerId) : SameView tagView (timersDataSent pid) := by
  rw [dataSent_source]
  unfold dataSentPrefix
  simp only [bind_assoc]
  apply (getPeer_frame pid).bind
  intro p
  apply (ambient_frame (AmbientM.branch .timersDataSentNotPending !(p.timerPending .newHandshake))).bind
  intro ready
  cases ready with
  | false => exact SameView.pure tagView ()
  | true =>
    unfold jitteredArm
    exact ((callerJiffies_sameWGWorld .timerJiffiesDataSent).factor tagView).bind (fun caller =>
      ((jitterBelowRekeyTimeout_sameWGWorld .newHandshakeJitter).factor tagView).bind (fun jitter =>
        guardedArm_frame pid .newHandshake
          (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) caller))

theorem fresh_retained (entry : TagMap) (pid : PeerId) :
    Preserves (Retained entry) (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued entry _ _)
    | (rx_retention_head branchExpired; exact (branchExpired_sameWGWorld _ _ _).wp (Retained entry))
    | silent_native_step entry

theorem traversal_frame (pid : PeerId) : SameView tagView (timersTraversal pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  exact ResponseSuffix.traversal_tag_frame pid g.dev g ambient result final after rfl run

theorem completion_retained (entry : TagMap) (pid : PeerId) (item : List SkbId) :
    Preserves (Retained entry) (createDataDone pid item) :=
  DataCompletionRules.preserves _ pid item
    (DriverTags.Silent.of_frame entry _ (DriverTags.Silent.traversal_frame pid))
    (DriverTags.Silent.delTimer entry pid .sendKeepalive)
    (DriverTags.Silent.sendSkb_retained entry pid)
    (DriverTags.Silent.of_frame entry _ (DriverTags.Silent.timersDataSent_frame pid))
    (DriverTags.Silent.fresh_retained entry pid)

theorem txStep_retained (entry : TagMap) (pid : PeerId) :
    Preserves (Retained entry) (txStep pid) := by
  exact TransmitRules.step_preserves _ pid
    (fun f => update entry pid (fun p=>{p with txQueue:=f p.txQueue}) (fun _=>rfl))
    (completion_retained entry pid) (keypairPut entry) (peerPut entry (some pid))
    (fun a => of_frame entry _ (packet_frame a))
    (fun q => of_frame entry _ (store_frame (prevQueuePeek_sameWGStore q)))

theorem setKeypair_frame (kid : KeypairId) (key : Keypair) :
    SameView tagView (setKeypair kid key) :=
  modifyDev_frame _ (fun _ => rfl)

theorem decryptPacket_retained (entry : TagMap) (packet : RxPacket) :
    Preserves (Retained entry) (decryptPacket packet) := by
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) _)
  intro missing
  cases missing with
  | true => exact preserves_pure none
  | false =>
    apply preserves_bind (of_frame entry _ (getKeypair_frame packet.keypair))
    intro key
    apply preserves_bind ((Origins.receiveReject_sameWGWorld key).wp (Retained entry))
    intro reject
    cases reject with
    | false => exact (Origins.receiveTail_sameWGWorld packet key).wp (Retained entry)
    | true =>
      simp only [ite_true]
      exact preserves_bind (of_frame entry _ (getKeypair_frame packet.keypair)) (fun fresh =>
        preserves_bind (of_frame entry _ (setKeypair_frame packet.keypair
          {fresh with receiving := {fresh.receiving with isValid := false}}))
          (fun _ => preserves_pure (none : Option RxPacket)))

theorem publish_frame (id : SkbId) (state : PacketState) :
    SameView tagView (RxWorkers.publishSource id state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient pid final after run
  obtain ⟨d,packet,key,p,device,hpacket,hkey,word,resident,effect⟩ :=
    PublicationIdentity.publish_execution id state g final ambient after pid run
  have ending := congrArg WGStoreView.dev effect
  change final.dev = some _ at ending
  change responseTagMap final.dev = responseTagMap g.dev
  rw [ending,device]
  funext target
  by_cases same : pid = target
  · subst target
    simp [responseTagMap,resident]
  · simp [responseTagMap,Std.TreeMap.getElem?_insert,same]

theorem decryptPrepare_retained (entry : TagMap) :
    Preserves (Retained entry) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant,getRxSkb,setRxSkb]
  repeat' first
    | (rx_retention_head decryptPacket; exact decryptPacket_retained entry _)
    | (rx_retention_head RxWorkers.publishSource; exact of_frame entry _ (publish_frame _ _))
    | (rx_retention_head liftSkb; exact of_frame entry _ (packet_frame _))
    | silent_native_step entry

theorem encryptPoll_retained (entry : TagMap) :
    Preserves (Retained entry) TxRing.pollSource := by
  unfold TxRing.pollSource
  repeat' silent_native_step entry

theorem enqueue_retained (entry : TagMap) (item : List SkbId) (state : PacketState) :
    Preserves (Retained entry) (enqueuePerPeerTx item state) :=
  of_staging entry _ (fun g => (ensures_iff _ _ _).mpr (Index.enqueuePerPeerTx_staging item state g))

theorem product_store {α : Type} (entry : TagMap) (action : Leanux.M α)
    (frame : SameProductStore action) :
    Preserves (fun w : World => Retained entry w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro g result final pre run
  have same := congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame g result final run)
  have tags := congrArg (fun s : WGStoreView => responseTagMap s.dev) same
  change tagView final.wg = tagView g.wg at tags
  change TagsRetained entry (tagView final.wg)
  rw [tags]
  exact pre

theorem encryptPacket_retained (entry : TagMap) (key : KeypairId) (packet : DataPacket) :
    Preserves (fun w : World => Retained entry w.wg) (encryptPacket Env.checksumHelp key packet) := by
  let P := fun w : World => Retained entry w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding packet.plaintext.bytes.length packet.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product (Retained entry) _
      ((calculateSkbPadding_sameWGWorld _ _).wp (Retained entry))
  have checksum (p : WG.Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have read : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) :=
    PublicationPoll.native_product (Retained entry) _ (of_frame entry _ (getKeypair_frame key))
  exact Index.EncryptCore.packet_preserves_source P key packet padding checksum read ambient

theorem encryptTail_retained (entry : TagMap) (item : Option (List SkbId)) :
    Preserves (fun w : World => Retained entry w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World => Retained entry w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product (Retained entry) _ (of_frame entry _ (packet_frame (SkbStore.getTx id)))
  have write (id : SkbId) (f : DataPacket → DataPacket) :
      Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    PublicationPoll.native_product (Retained entry) _ (of_frame entry _ (packet_frame (SkbStore.setTx id f)))
  have enqueue (xs : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product (Retained entry) _ (enqueue_retained entry xs state)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := encryptPacket_retained entry key pkt
  have need : Preserves P (Env.condResched .encryptWorker) :=
    product_store entry _ (condResched_sameKernel _)
  exact Index.EncryptCore.tail_preserves_source P item read write enqueue packet need ambient

theorem txIter_retained (entry : TagMap) (pid : PeerId) (need : Leanux.M Bool)
    (next : Preserves (fun w : World => Retained entry w.wg) need) :
    Preserves (fun w : World => Retained entry w.wg) (txIter pid need) := by
  let P := fun w : World => Retained entry w.wg
  have step : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product (Retained entry) _ (txStep_retained entry pid)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  routing_tx_source [txIter,workerIter] using [step,next,ambient]


end Leanux.Proofs.WG.Noise.DriverTags.Silent
