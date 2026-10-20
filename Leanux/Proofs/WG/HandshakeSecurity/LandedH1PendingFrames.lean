import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionDispatch
import Leanux.Proofs.WG.Noise.Statements

/-! Local pending-slot adapters from H1 landed at be8c209c, carried through
ac55c7d5. The direct frame packages are constructed here. The stronger actor-
specific transition package remains an explicit argument to the aggregate. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.LandedH1.Pending
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes PendingPromotion

/-- C3 and landed H1 observe the same pending allocation store. -/
theorem view_eq : PendingPromotion.view = Noise.PendingTickets.view := by
  funext w
  apply Store.ext
  · rfl
  · funext pid
    unfold PendingPromotion.view PendingPromotion.nextSlot
      Noise.PendingTickets.view Noise.PendingTickets.pending
    unfold keypairResidents
    cases w.dev <;> simp [Option.bind_assoc,Option.map_eq_bind,Function.comp_def]

private theorem transport {α : Type} {action : WG.M α} {R : Store PeerId → Store PeerId → Prop}
    (frame : ProjectedAction Noise.PendingTickets.view R action) :
    ProjectedAction PendingPromotion.view R action := by
  rw [view_eq]
  exact frame

/-- Landed H1 supplies staging and the receive suffix's pending-store frames. -/
theorem quiet : H1PendingQuietFrames where
  staging := fun pid => transport (Noise.PendingTickets.sendStagedPackets_retained pid)
  keepalive := fun pid => transport (Noise.PendingTickets.sendKeepalive_retained pid)
  endpoint := fun pid ep => transport (Noise.PendingTickets.setPeerEndpoint_frame pid ep)
  receiveTail := fun pid pkt confirmed => transport (Noise.PendingTickets.afterConfirmation_retained pid pkt confirmed)

/-- Landed H1 supplies the receive-counter pending-store frame. -/
theorem poll : H1PendingPollFrames where
  counter := fun kid nonce => transport (Noise.PendingSession.counter_pending kid nonce)

/-- Landed H1 supplies routed transmit's pending-store frames. -/
theorem stack : H1PendingStackFrames where
  lookup := fun family addr => transport (Noise.PendingStack.lookupDst_frame family addr)
  trim := fun pid => transport (Noise.PendingStack.xmitTrim_pending_variant pid)
  splice := fun pid packets => transport (Noise.PendingStack.xmitSplice_pending_variant pid packets)

/-- Landed H1 supplies every pending-store frame in the handshake suffix. -/
theorem handshake : H1PendingHandshakeFrames where
  initiation := fun msg => transport (Noise.PendingTickets.consumeInitiation_frame msg)
  response := fun msg => transport (Noise.PendingTickets.consumeResponse_frame msg)
  cookie := fun msg => transport (Noise.PendingReception.cookieMessageConsume_pending msg)
  create := fun pid => transport (Noise.PendingTickets.createResponse_frame pid)
  mac := fun pid msg => transport (Noise.PendingTickets.addMacToPacket_frame pid msg)
  send := fun pid msg => transport (Noise.PendingTickets.sendBufferToPeer_frame pid msg)
  derived := fun pid => transport (Noise.PendingTickets.timersSessionDerived_frame pid)
  traversal := fun pid => transport (Noise.PendingTickets.timersTraversal_frame pid)
  sent := fun pid => transport (Noise.PendingTickets.timersAnyAuthenticatedPacketSent_frame pid)
  received := fun pid => transport (Noise.PendingTickets.timersAnyAuthenticatedPacketReceived_frame pid)
  complete := fun pid site => transport (Noise.PendingTickets.timersHandshakeComplete_frame pid site)
  endpoint := fun pid src => transport (Noise.PendingTickets.setPeerEndpointFromSkb_frame pid src)

/-- Landed H1/H2 publication effects retain pending allocation identities. -/
theorem publication : H1PublicationFrame where
  publication := fun item state => transport (Noise.PendingTickets.retained_of_staging_ordinary _
    (fun entry => (Noise.ensures_iff _ _ _).mpr (Index.enqueuePerPeerTx_staging item state entry))
    (Keypairs.SameView.ordinary (Keypairs.WGTransitions.enqueuePerPeerTx_sameSnapshot item state)))

/-- Landed H1 supplies the socket and rekey pending-store frames. -/
theorem transmit : H1TransmitFrames where
  send4 := fun pid ep bytes ds exactRx => transport (Noise.PendingTickets.send4_cached_frame pid ep bytes ds exactRx)
  send6 := fun pid ep bytes ds exactRx => transport (Noise.PendingTickets.send6_cached_frame pid ep bytes ds exactRx)
  dataSent := fun pid => transport (Noise.PendingTickets.timersDataSent_frame pid)
  queued := fun pid retry => transport (Noise.PendingTickets.sendQueuedHandshakeInitiation_retained pid retry)

/-- Landed H1 supplies timer mutations' pending-store frames. -/
theorem timer : H1TimerFrames where
  delete := fun pid timer => transport (Noise.PendingTickets.delTimer_frame pid timer)
  modify := fun site pid timer delay => transport (Noise.PendingTickets.modPeerTimer_frame site pid timer delay)
  purge := fun pid => transport (Noise.PendingTickets.purgeStagedPackets_frame pid)
  endpoint := fun pid => transport (Noise.PendingTickets.clearPeerEndpointSrc_frame pid)

/-- Landed H1 supplies flushed-worker retention at each native return. -/
theorem flushed : H1FlushedFrames where
  send := fun pid => transport (Noise.PendingTickets.runFlushedSendWork_retained pid)
  clear := fun pid => transport (Noise.PendingTickets.runFlushedClearWork_retained pid)

/-- Landed H1 supplies the pending-store projection of index lookup. -/
theorem ingress : H1IngressFrames where
  lookup := fun kinds index => transport (Noise.PendingReception.indexLookup_pending_frame kinds index)

/-- Landed H1 supplies the configuration pending-store frames and retentions. -/
theorem configuration : H1ConfigurationFrames where
  peer := fun attrs => transport (Noise.PendingTickets.setPeerCmd_retained attrs)
  pubkey := fun key => transport (Noise.PendingTickets.pubkeyLookup_frame key)
  remove := fun peer => transport (Noise.PendingTickets.peerRemove_retained peer)
  removeAll := transport Noise.PendingTickets.peerRemoveAll_retained
  precompute := fun pid => transport (Noise.PendingTickets.precomputeStaticStatic_frame pid)
  expire := fun pid => transport (Noise.PendingTickets.expireCurrentPeerKeypairs_frame pid)
  identity := fun key => transport (Noise.PendingTickets.setStaticIdentityPrivateKey_frame key)
  cookies := transport Noise.PendingTickets.cookiePrecomputeDeviceKeys_frame
  port := fun port => transport (Noise.PendingTickets.setPort_frame port)
  endpoint := fun pid => transport (Noise.PendingTickets.clearPeerEndpointSrc_frame pid)

/-- Landed H1 supplies the lifecycle pending-store retentions. -/
theorem lifecycle : H1LifecycleFrames where
  down := transport Noise.PendingTickets.wgDown_retained
  create := transport Noise.PendingTickets.wgCreate_retained

/-- All direct frame fields are constructed. The actor-specific promotion
transitions remain the named premise; no initialized security claim is assumed. -/
theorem driver (edges : H1PendingPromotionEdges) : H1DriverFrames where
  deferred := ⟨⟨edges,quiet,poll,stack,handshake,publication,transmit⟩,timer,flushed⟩
  ingress := ingress
  configuration := configuration
  lifecycle := lifecycle

end Leanux.Proofs.WG.HandshakeSecurity.LandedH1.Pending
