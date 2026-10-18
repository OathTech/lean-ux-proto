import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverNapi

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits Origins Origins.Retaining ConfiguredTraffic

theorem carrier_publication (item : List SkbId) (state : PacketState) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (enqueuePerPeerTx item state) :=
  carrier_join confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredTraffic.«0».Leanux.Proofs.WG.ConfiguredTraffic.enqueue) item state)
    (publication_native item state confirmed)

theorem carrier_encrypt (kid : KeypairId) (pkt : DataPacket) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) (encryptPacket Env.checksumHelp kid pkt) := by
  let P := fun w : World => Carrier confirmed w.wg
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Framing.Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (Carrier confirmed))
  have checksum (p : WG.Packet) : Framing.Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have read : Framing.Preserves P (monadLift (getKeypair kid) : Leanux.M Keypair) :=
    PublicationPoll.native_product _ _ (carrier_key_read kid confirmed)
  routing_tx_source [encryptPacket] using [padding,checksum,read,effect]

theorem carrier_encrypt_tail (item : Option (List SkbId)) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) (RxWorkers.encryptStepTailSource item) := by
  let P := fun w : World => Carrier confirmed w.wg
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have skb {α : Type} (a : SkbM α) : Framing.Preserves P (monadLift (liftSkb a) : Leanux.M α) :=
    PublicationPoll.native_product _ _ (carrier_skb a confirmed)
  have encrypt (kid : KeypairId) (pkt : DataPacket) : Framing.Preserves P
      (encryptPacket Env.checksumHelp kid pkt) := carrier_encrypt kid pkt confirmed
  have publish (xs : List SkbId) (state : PacketState) : Framing.Preserves P
      (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (carrier_publication xs state confirmed)
  routing_tx_source [RxWorkers.encryptStepTailSource,getTxSkb,setTxSkb] using [skb,encrypt,publish,effect]

theorem carrier_encrypt_poll (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) TxRing.pollSource := by
  unfold TxRing.pollSource
  apply preserves_bind (carrier_store getDev_sameWGStore confirmed)
  intro d
  apply preserves_bind (carrier_modify
    (fun dev => {dev with encryptQueue := d.encryptQueue.consume.2})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) confirmed)
  intro _
  exact preserves_pure _

theorem carrier_fresh (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (keepKeyFresh pid) := by
  apply carrier_join confirmed _ (fresh_native pid confirmed)
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact ConfiguredTraffic.queued _ _)
    | configured_traffic_step

theorem carrier_data_done (pid : PeerId) (item : List SkbId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (createDataDone pid item) := by
  apply carrier_join confirmed _ (createDataDone_native pid item confirmed)
  let P := ConfiguredIdentity.Inv
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Framing.Preserves P (liftSkb a) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredTraffic.«0».Leanux.Proofs.WG.ConfiguredTraffic.skb) a
  have traversal : Framing.Preserves P (timersTraversal pid) :=
    ConfiguredRemoval.frame (ConfiguredIdentity.timersTraversal_view pid)
  have sent : Framing.Preserves P (timersAnyAuthenticatedPacketSent pid) :=
    ConfiguredRemoval.frame (ConfiguredIdentity.timersAnyAuthenticatedPacketSent_view pid)
  have send (bytes : List UInt8) (ds : Nat) : Framing.Preserves P (sendSkbToPeer pid bytes ds) :=
    ConfiguredRemoval.frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.sendSkb_view) pid bytes ds)
  have dataSent : Framing.Preserves P (timersDataSent pid) :=
    ConfiguredRemoval.frame ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentEnvironment.«0».Leanux.Proofs.WG.CurrentEnvironment.dataSent_view) pid)
  have fresh : Framing.Preserves P (keepKeyFresh pid) := by
    unfold keepKeyFresh WG.andM WG.orM
    change Framing.Preserves ConfiguredIdentity.Inv _
    simp (config := {zeta := false}) only [branch,branchCmp,invariant]
    repeat' first
      | (rx_retention_head sendQueuedHandshakeInitiation; exact ConfiguredTraffic.queued _ _)
      | configured_traffic_step
  routing_tx_source [createDataDone] using [traversal,sent,send,dataSent,fresh,skb,effect]

theorem carrier_tx_step (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  let P := Carrier confirmed
  have ambient {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) : Framing.Preserves P (liftSkb a) := carrier_skb a confirmed
  have complete (item : List SkbId) : Framing.Preserves P (createDataDone pid item) := carrier_data_done pid item confirmed
  have key (kp : Option KeypairId) : Framing.Preserves P (keypairPut kp false) := carrier_key_put kp false confirmed
  have put : Framing.Preserves P (peerPut (some pid)) := carrier_peer_put (some pid) confirmed
  have dispose (item : List SkbId) (kp : KeypairId) : Framing.Preserves P (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [skb, key, put]
  have update (f : Peer → Peer) (same : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
      (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
      Framing.Preserves P (do let p ← getPeer pid; setPeer pid (f p)) := carrier_update pid f same configured confirmed
  have drop : Framing.Preserves P (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) :=
    update _ (fun _ => rfl) (fun _ => rfl)
  have body (first : Option (List SkbId)) : Framing.Preserves P (TxDisposition.bodySource pid first) := by
    unfold TxDisposition.bodySource
    simp only [getPeer_twice]
    apply preserves_bind
    · routing_tx_source [WG.andM] using [skb, ambient]
    · intro go
      cases go with
      | false => exact preserves_pure false
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases first with
        | none => exact ambient (AmbientM.invariant "unreachable")
        | some item =>
          cases head : item.head? with
          | none => simp only [head]; exact ambient (AmbientM.invariant "an empty ring item")
          | some headId =>
            simp only [head]
            apply preserves_bind (skb (SkbStore.getTx headId))
            intro packet
            apply preserves_bind drop
            intro _
            routing_tx_source [] using [complete, dispose, ambient]
  unfold TxDisposition.stepSource
  apply preserves_bind (carrier_read_peer pid confirmed)
  intro p
  apply preserves_bind (carrier_store (prevQueuePeek_sameWGStore p.txQueue) confirmed)
  intro out
  rcases out with ⟨first, queue⟩
  exact preserves_bind (update (fun p => {p with txQueue := queue}) (fun _ => rfl) (fun _ => rfl)) (fun _ => body first)

private theorem publication_configured (id : SkbId) (state : PacketState) :
    SameView ConfiguredIdentity.view (RxWorkers.publishSource id state) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a pid v b run
  obtain ⟨d,pkt,key,p,hd,_,_,_,hp,effect⟩ :=
    PublicationIdentity.publish_execution id state w v a b pid run
  have hv := congrArg WGStoreView.dev effect
  change v.dev = some _ at hv
  unfold ConfiguredIdentity.view
  rw [hv,hd]
  simp only [Option.map_some]
  apply congrArg some
  exact (ConfiguredIdentity.state_peer_same
    {d with rxSkbs := d.rxSkbs.insert id {pkt with state}, peers := d.peers.insert pid {p with refcount := p.refcount+1}}
    pid {p with refcount := p.refcount+1} {p with refcount := p.refcount+1,napiScheduled := true}
    (by simp) rfl).trans
    (ConfiguredIdentity.state_peer_same d pid p {p with refcount := p.refcount+1} hp rfl)

theorem carrier_rx_publish (id : SkbId) (state : PacketState) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (RxWorkers.publishSource id state) :=
  carrier_frame confirmed (publication_configured id state) (publish_native id state confirmed)

theorem carrier_decrypt (pkt : RxPacket) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (decryptPacket pkt) :=
  carrier_frame confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.decryptPacket_view) pkt)
    (decrypt_native pkt confirmed)

theorem carrier_prepare_worker (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact carrier_decrypt _ confirmed)
    | (rx_retention_head RxWorkers.publishSource; exact carrier_rx_publish _ _ confirmed)
    | (rx_retention_head getDev; exact carrier_store getDev_sameWGStore confirmed)
    | (rx_retention_head setRxSkb; exact carrier_skb _ confirmed)
    | responder_carrier_poll_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
