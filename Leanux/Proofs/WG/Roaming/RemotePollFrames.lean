import Leanux.Proofs.WG.Roaming.RemoteControlSource
import Leanux.Proofs.WG.Roaming.RemoteSilentSource
import Leanux.Proofs.WG.Roaming.RemotePollBridge
import Leanux.Proofs.WG.Index.TransmitRuleSource
import Leanux.Proofs.WG.Noise.DriverTagPollSource
import Leanux.Proofs.WG.Queues.ObservePollSource
import Leanux.Proofs.WG.Roaming.RemoteWorkerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemotePoll
open Leanux Leanux.WG Noise Lifetimes Queues Std.Do
open Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem getPeer_frame (pid : PeerId) : SameView destinationAt (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a p v b run
  exact congrArg destinationAt (getPeer_normal pid g v p a b run).1

theorem getKeypair_frame (kid : KeypairId) : SameView destinationAt (getKeypair kid) :=
  RemoteWorkers.getKeypair_frame kid

theorem packet_frame {α : Type} (action : SkbM α) :
    SameView destinationAt (liftSkb action) :=
  RemoteWorkers.packet_frame action

theorem update_frame (pid : PeerId) (f : Peer→Peer)
    (same : ∀p,(f p).endpoint.map destination=p.endpoint.map destination) :
    SameView destinationAt (getPeer pid >>= fun p=>setPeer pid (f p)) :=
  modifyPeer_remotes pid f same

theorem modifyDev_retained (entry : RemoteMap) (f : Device→Device)
    (same : ∀d,(f d).peers=d.peers) : Preserves (Retained entry) (WG.modifyDev f) :=
  (modifyDev_remotes f same).wp (RemoteRetained entry)

theorem setKeypair_frame (kid : KeypairId) (key : Keypair) :
    SameView destinationAt (setKeypair kid key) := modifyDev_remotes _ (fun _=>rfl)

theorem update (entry : RemoteMap) (pid : PeerId) (f : Peer→Peer)
    (same : ∀p,(f p).endpoint.map destination=p.endpoint.map destination) :
    Preserves (Retained entry) (getPeer pid >>= fun p=>setPeer pid (f p)) :=
  (modifyPeer_remotes pid f same).wp (RemoteRetained entry)

theorem update_bind {α : Type} (entry : RemoteMap) (pid : PeerId) (f : Peer→Peer)
    (tail : Unit→WG.M α)
    (same : ∀p,(f p).endpoint.map destination=p.endpoint.map destination)
    (keep : ∀u,Preserves (Retained entry) (tail u)) :
    Preserves (Retained entry) (getPeer pid >>= fun p=>setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update entry pid f same) keep

open Origins.HandshakeSources in
macro "remote_poll_native " entry:term : tactic => `(tactic| first
  | (receive_update_head setPeer
     exact update $entry _ _ (fun _=>rfl))
  | (receive_update_head Bind.bind
     apply update_bind $entry _ _ _ (fun _=>rfl)
     intro u)
  | (rx_retention_head getPeer; exact (getPeer_frame _).wp (RemoteRetained $entry))
  | (rx_retention_head getKeypair; exact (getKeypair_frame _).wp (RemoteRetained $entry))
  | (rx_retention_head getDev; exact (RemoteCompletion.store_remotes getDev_sameWGStore).wp (RemoteRetained $entry))
  | (rx_retention_head modifyDev; exact modifyDev_retained $entry _ (fun _=>rfl))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ite; apply (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredReceive.«0».Leanux.Proofs.WG.ConfiguredReceive.preserve_ite))
  | rx_retention_step)

theorem peek_frame (pid : PeerId) : SameView destinationAt (peekRxQueue pid) := by
  unfold peekRxQueue
  apply (getPeer_frame pid).bind
  intro p
  apply (RemoteCompletion.store_remotes (prevQueuePeek_sameWGStore p.rxQueue)).bind
  intro result
  simpa only [bind_assoc] using
    (update_frame pid (fun q=>{q with rxQueue:=result.2}) (fun _=>rfl)).bind
      (fun _=>SameView.pure destinationAt result.1)

theorem drop_frame (pid : PeerId) : SameView destinationAt (dropRxQueue pid) := by
  unfold dropRxQueue
  rw [getPeer_twice]
  exact modifyPeer_remotes pid (fun p=>{p with rxQueue:=p.rxQueue.dropPeeked}) (fun _=>rfl)

theorem complete_frame (pid : PeerId) : SameView destinationAt (completeRxQueue pid) :=
  modifyPeer_remotes pid (fun p=>{p with napiScheduled:=false}) (fun _=>rfl)

theorem counter_retained (entry : RemoteMap) (kid nonce : Nat) :
    Preserves (Retained entry) (counterValidate kid nonce) := by
  unfold counterValidate
  simp (config := {zeta := false}) only [WG.orM,Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' first
    | (rx_retention_head setKeypair; exact (setKeypair_frame _ _).wp (RemoteRetained entry))
    | remote_poll_native entry
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head ForIn.forIn; apply list_view_spec id (Retained entry))
    | material_component
    | material_intro
    | material_reduce
    | material_match
  all_goals change Preserves (Retained entry) _
  all_goals repeat' remote_poll_native entry

theorem ready_retained (entry : RemoteMap) (first : Option SkbId) :
    Preserves (Retained entry)
      (WG.andM (branch .rxPollPacket first.isSome) do
        let some f:=first | invariant "unreachable"
        branch .rxPollNotUncrypted ((←getRxSkb f).state != .uncrypted)) := by
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head getRxSkb; exact (packet_frame (SkbStore.getRx _)).wp (RemoteRetained entry))
    | remote_poll_native entry

theorem keypairPut_retained (entry : RemoteMap) (key : Option KeypairId) (now : Bool) :
    Preserves (Retained entry) (keypairPut key now) :=
  (ensures_iff _ _ _).mp (staging_remotes _ (fun g=>Index.StagingRich.release g key now) entry)

theorem lookupDst_frame (family addr : Nat) : SameView destinationAt (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result v b run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp (RxBorrow.lookupDst_spec family addr (wgStoreView g))
    g a result v b rfl run
  cases result with
  | none => exact congrArg (fun s : WGStoreView=>fun pid=>((s.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination) borrowed
  | some pid =>
    obtain ⟨d,p,device,resident,_,effect⟩:=borrowed
    change g.dev=some d at device
    change (fun target=>(((wgStoreView v).dev.bind fun d=>d.peers[target]?).bind Peer.endpoint).map destination)=_
    rw [effect]
    funext target
    by_cases same:pid=target
    · subst target; simp [destinationAt,peerAt,device,resident]
    · simp [destinationAt,peerAt,device,Std.TreeMap.getElem?_insert,same]

theorem trim_frame (pid : PeerId) : SameView destinationAt (xmitTrim pid) := by
  apply Index.TransmitCore.xmitTrim_view destinationAt pid
  intro g d p device resident
  funext target
  by_cases same:pid=target
  · subst target; simp [destinationAt,peerAt,device,resident]
  · simp [destinationAt,peerAt,device,Std.TreeMap.getElem?_insert,same]

theorem splice_frame (pid : PeerId) (packets : List Packet) :
    SameView destinationAt (xmitSplice pid packets) := by
  unfold xmitSplice
  rw [getPeer_twice]
  exact modifyPeer_remotes pid (fun p=>{p with staged:=p.staged++packets}) (fun _=>rfl)

theorem xmit_retained (entry : RemoteMap) (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Preserves (Retained entry) (wgXmit family addr packets mtu) :=
  Index.TransmitCore.wgXmit_preserves_source _ family addr packets mtu
    (fun _ same=>(RemoteCompletion.store_remotes same).wp (RemoteRetained entry))
    ((lookupDst_frame family addr).wp (RemoteRetained entry))
    (fun pid=>(trim_frame pid).wp (RemoteRetained entry))
    (fun pid xs=>(splice_frame pid xs).wp (RemoteRetained entry))
    (fun pid=>(ensures_iff _ _ _).mp (sendStagedPackets_remotes pid entry))
    (fun peer=>(ensures_iff _ _ _).mp (peerPut_remotes peer entry))
    ((modifyDev_remotes (fun d=>{d with txErrors:=d.txErrors+1}) (fun _=>rfl)).wp (RemoteRetained entry))

theorem product_store (entry : RemoteMap) (w v : World)
    (same : productStoreView v=productStoreView w) (pre : ProductRetained entry w) :
    ProductRetained entry v := by
  have dest : destinationAt v.wg=destinationAt w.wg :=
    congrArg (fun s : ProductStore43=>fun pid=>((s.2.2.2.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination) same
  change RemoteRetained entry (destinationAt v.wg)
  rw [dest]
  exact pre

theorem stack_retained (entry : RemoteMap) (bytes : List UInt8) :
    Preserves (ProductRetained entry) (Env.deliverInner bytes) := by
  have support : PrefixPreserves (fun (_ : List Empty)=>ProductRetained entry)
      (fun _=>True) (PendingStack.stackSource bytes) :=
    Index.TransmitCore.stack_preserves_source _ bytes (product_store entry)
      (fun family addr packets mtu=>PublicationPoll.native_product _ _ (xmit_retained entry family addr packets mtu))
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  obtain ⟨suffix,appended,safe,normal⟩:=support w [] pre
  have erased:=(PendingStack.stackSource_erases bytes w []).trans run
  simpa only [erased] using normal

theorem decryptPacket_retained (entry : RemoteMap) (packet : RxPacket) :
    Preserves (Retained entry) (decryptPacket packet) := by
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) _)
  intro missing
  cases missing with
  | true=>exact preserves_pure none
  | false=>
    apply preserves_bind ((getKeypair_frame packet.keypair).wp (RemoteRetained entry))
    intro key
    apply preserves_bind ((Origins.receiveReject_sameWGWorld key).wp (Retained entry))
    intro reject
    cases reject with
    | false=>exact (Origins.receiveTail_sameWGWorld packet key).wp (Retained entry)
    | true=>
      simp only [ite_true]
      exact preserves_bind ((getKeypair_frame packet.keypair).wp (RemoteRetained entry)) (fun fresh=>
        preserves_bind ((modifyDev_remotes (fun d=>{d with keypairs:=d.keypairs.insert packet.keypair {fresh with receiving:={fresh.receiving with isValid:=false}}}) (fun _=>rfl)).wp (RemoteRetained entry))
          (fun _=>preserves_pure (none : Option RxPacket)))

theorem publish_frame (id : SkbId) (state : PacketState) :
    SameView destinationAt (RxWorkers.publishSource id state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a pid v b run
  obtain ⟨d,pkt,key,p,device,_,_,_,resident,effect⟩:=
    PublicationIdentity.publish_execution id state g v a b pid run
  have ending:=congrArg WGStoreView.dev effect
  change v.dev=some _ at ending
  funext target
  simp only [destinationAt,peerAt,ending,device,Option.bind_some]
  by_cases same:pid=target
  · subst target; simp [resident]
  · simp [Std.TreeMap.getElem?_insert,same]

theorem prepare_retained (entry : RemoteMap) :
    Preserves (Retained entry) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant,getRxSkb,setRxSkb]
  repeat' first
    | (rx_retention_head decryptPacket; exact decryptPacket_retained entry _)
    | (rx_retention_head RxWorkers.publishSource; exact (publish_frame _ _).wp (RemoteRetained entry))
    | (rx_retention_head liftSkb; exact (packet_frame _).wp (RemoteRetained entry))
    | remote_poll_native entry

theorem covered_product_store {E : Type} (entry : RemoteMap)
    (cause : E→PeerId→Nat×Nat×Nat×Nat→Prop) (h : List E) (w v : World)
    (same : productStoreView v=productStoreView w) (pre : Covered entry cause h w) :
    Covered entry cause h v := by
  have dest : destinationAt v.wg=destinationAt w.wg :=
    congrArg (fun s : ProductStore43=>fun pid=>((s.2.2.2.dev.bind fun d=>d.peers[pid]?).bind Peer.endpoint).map destination) same
  change RemoteCovered entry cause h (destinationAt v.wg)
  rw [dest]
  exact pre

end Leanux.Proofs.WG.Roaming.RemotePoll
