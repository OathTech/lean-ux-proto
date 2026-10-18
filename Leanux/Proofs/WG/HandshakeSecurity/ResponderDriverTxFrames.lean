import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverSource

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits Origins Origins.Retaining TransmitSecurity

/-- Both projections are transported by one native execution. -/
theorem carrier_store {action : WG.M α} (same : SameWGStore action) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) action :=
  carrier_frame confirmed (ConfiguredIdentity.sameWG (project := id) same)
    (native_store same confirmed)

theorem carrier_peer_get (pid : PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (peerGet pid) :=
  carrier_frame confirmed (CreationLoan.peerGet_configured_view pid) (peerGet_native pid confirmed)

theorem carrier_peer_put (pid : Option PeerId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (peerPut pid) :=
  carrier_join confirmed (ConfiguredIdentity.peerPut_preserves pid) (peerPut_native pid confirmed)

theorem carrier_key_read (kid : KeypairId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (getKeypair kid) :=
  carrier_frame confirmed (ConfiguredIdentity.getKeypair_view kid) (readKey_native kid confirmed)

theorem carrier_reserve (kid : KeypairId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (Nonce.reserveNative kid) := by
  apply carrier_frame confirmed
  · unfold Nonce.reserveNative
    exact (ConfiguredIdentity.getKeypair_view kid).bind (fun k =>
      (ConfiguredIdentity.setKeypair_view kid _).bind (fun _ => SameView.pure _ _))
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b hi run
    unfold Nonce.reserveNative at run
    rw [MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨key,read,ar,getter,rest⟩ := run
    obtain ⟨same,time,d,hd,hk⟩ := KeyTimes.getKeypair_return kid w read key a ar getter
    subst read ar
    cases rest
    refine ⟨hi.1.frame ?_, CurrentSlots.fields_transport hi.2 ?_⟩
    · simpa [setKeypair,modifyDev,hd] using
        current_key_write w d kid key {key with sendingCounter := key.sendingCounter + 1} hd hk rfl
    · unfold CurrentSlots.fields RxCredits.keyWords
      simp only [hd,Option.map_some,Option.bind_some]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      funext q
      by_cases eq : kid = q
      · subst q; simp [hk]
      · simp [Std.TreeMap.getElem?_insert,eq]

theorem carrier_skb (action : SkbM α) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (liftSkb action) :=
  carrier_join confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredTraffic.«0».Leanux.Proofs.WG.ConfiguredTraffic.skb) action)
    (native_skb action confirmed)

theorem carrier_allocate (ps : List DataPacket) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (ps.mapM newTxSkb) := by
  induction ps with
  | nil => exact preserves_pure _
  | cons p ps ih =>
    simp only [List.mapM_cons]
    exact preserves_bind (carrier_skb (SkbStore.newTx p) confirmed) (fun id =>
      preserves_bind ih (fun ids => preserves_pure (id :: ids)))

theorem carrier_create (pid : PeerId) (item : List SkbId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (createData pid item) :=
  carrier_join confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredTraffic.«0».Leanux.Proofs.WG.ConfiguredTraffic.create) pid item)
    (native_retained (createData_core pid item) (createData_keyEffect pid item)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.createData_preserves) pid item) confirmed)

theorem carrier_out (pid : PeerId) (packets : List WG.Packet) (kid : Option KeypairId)
    (invalid : Bool) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (stagedOutNokey pid packets kid invalid) :=
  carrier_join confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.ConfiguredTraffic.«0».Leanux.Proofs.WG.ConfiguredTraffic.outNokey) pid packets kid invalid)
    (native_retained (stagedOutNokey_core pid packets kid invalid)
      (stagedOutNokey_keyEffect pid packets kid invalid)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.stagedOutNokey_preserves) pid packets kid invalid) confirmed)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
