import Leanux.Proofs.WG.Config.RequestWgChainClaims
import Leanux.Proofs.WG.Config.ScalarCommandClaims
import Leanux.Proofs.WG.Config.RequestCommandClaims
import Leanux.Proofs.WG.Config.ConfiguredReadbackClaims
import Leanux.Proofs.WG.Config.RequestFinalHeaderClaims
import Leanux.Proofs.WG.Config.ScalarTailClaims
import Leanux.Proofs.WG.Config.CommandOrderClaims
import Leanux.Proofs.WG.Config.RequestKeyHeaderClaims
import Leanux.Proofs.WG.Config.ScalarFinishClaims
import Leanux.Proofs.WG.Config.AllowedOrderClaims
import Leanux.Proofs.WG.Config.KeyIdentityReadbackClaims
import Leanux.Proofs.WG.Config.PeerScalarRetentionClaims
import Leanux.Proofs.WG.Config.ScalarPrefixClaims
import Leanux.Proofs.WG.Config.UpdateOnlyClaims
import Leanux.Proofs.WG.Config.KeyIdentityClaims
import Leanux.Proofs.WG.Config.GetterContextClaims
import Leanux.Proofs.WG.Config.RequestReadbackClaims
import Leanux.Proofs.WG.Config.RequestMetadataClaims
import Leanux.Proofs.WG.Config.KeyStageEntryClaims
import Leanux.Proofs.WG.Config.InitializedReadbackClaims
import Leanux.Proofs.WG.Config.RequestInputClaims
import Leanux.Proofs.WG.Config.KeyStageClaims
import Leanux.Proofs.WG.Config.GetterPeerCommandClaims
import Leanux.Proofs.WG.Config.GetterReadyClaims
import Leanux.Proofs.WG.Config.InitializedOwnerClaims
import Leanux.Proofs.WG.Config.RequestReceiptClaims
import Leanux.Proofs.WG.Config.GetterStagingSource
import Leanux.Proofs.WG.Config.QueuedRemoveClaims
import Leanux.Proofs.WG.Config.RequestOrderClaims
import Leanux.Proofs.WG.Config.InitializedOwnerAccountClaims
import Leanux.Proofs.WG.Config.ConfiguredDeviceClaims
import Leanux.Proofs.WG.Config.OwnerRunnerNormalSource
import Leanux.Proofs.WG.Config.QueuedReplacementReadbackClaims
import Leanux.Proofs.WG.Config.ConfiguredOptionalSource
import Leanux.Proofs.WG.Config.ConfiguredCommandClaims
import Leanux.Proofs.WG.Config.GetterCleanupMacFrames
import Leanux.Proofs.WG.Config.ConfiguredBoundaryClaims
import Leanux.Proofs.WG.Config.ConfiguredTailClaims
import Leanux.Proofs.WG.Config.ConfiguredRepresentationEffects
import Leanux.Proofs.WG.Config.EmptyMetadataGetterClaims
import Leanux.Proofs.WG.Config.ReplacementCompletionClaims
import Leanux.Proofs.WG.Config.GetterMetadataFrames
import Leanux.Proofs.WG.Config.ConfiguredRemovalClaims
import Leanux.Proofs.WG.Config.InitializedRoutingClaims
import Leanux.Proofs.WG.Config.ConfiguredOwnerClaims
import Leanux.Proofs.WG.Config.RoutingReadbackClaims
import Leanux.Proofs.WG.Config.ReplacementInitialClaims
import Leanux.Proofs.WG.Config.ReplacementMixedGetterClaims
import Leanux.Proofs.WG.Config.ZeroPortMixedGetterClaims
import Leanux.Proofs.WG.Config.NonzeroPortMixedGetterClaims
import Leanux.Proofs.WG.Config.PortMixedGetterClaims
import Leanux.Proofs.WG.Config.FwmarkMixedGetterClaims
import Leanux.Proofs.WG.Config.EndpointMixedGetterClaims
import Leanux.Proofs.WG.Config.KeyMixedGetterClaims
import Leanux.Proofs.WG.Config.ScalarMixedGetterClaims
import Leanux.Proofs.WG.Config.MixedGetterClaims
import Leanux.Proofs.WG.Config.MixedPageContentSource
import Leanux.Proofs.WG.Config.MixedPageBoundsClaims
import Leanux.Proofs.WG.Config.MixedHeldCallbackSource
import Leanux.Proofs.WG.Config.MixedPageDeviceClaims
import Leanux.Proofs.WG.Config.MixedPageSelectionClaims
import Leanux.Proofs.WG.Config.MixedPageReferenceFrames
import Leanux.Proofs.WG.Config.MixedCallbackSource
import Leanux.Proofs.WG.Config.CursorStepEffects
import Leanux.Proofs.WG.Config.MixedPagePlanClaims
import Leanux.Proofs.WG.Config.MixedPageScanSource
import Leanux.Proofs.WG.Config.CursorReadySource
import Leanux.Proofs.WG.Config.MixedPeerSerializerSource
import Leanux.Proofs.WG.Config.MixedPeerCoalesceSource
import Leanux.Proofs.WG.Config.PeerKeyGetterClaims
import Leanux.Proofs.WG.Config.PeerMixedGetterClaims
import Leanux.Proofs.WG.Config.PeerScalarGetterClaims
import Leanux.Proofs.WG.Config.PeerGetterClaims
import Leanux.Proofs.WG.Config.PeerPagePlanClaims
import Leanux.Proofs.WG.Config.PeerPageCoalesceClaims
import Leanux.Proofs.WG.Config.PageTransitionSource
import Leanux.Proofs.WG.Config.MiddlePageSource
import Leanux.Proofs.WG.Config.TwoPageGetterClaims
import Leanux.Proofs.WG.Config.TwoPageCoalesceClaims
import Leanux.Proofs.WG.Config.CursorCallbackClaims
import Leanux.Proofs.WG.Config.CursorBodySource
import Leanux.Proofs.WG.Config.FactoredTailClaims
import Leanux.Proofs.WG.Config.EndpointSetClaims
import Leanux.Proofs.WG.Config.MixedWeightedPaginationClaims
import Leanux.Proofs.WG.Config.KeyWeightedPaginationClaims
import Leanux.Proofs.WG.Config.WeightedGetterClaims
import Leanux.Proofs.WG.Config.MixedEndpointPaginationClaims
import Leanux.Proofs.WG.Config.KeyEndpointPaginationClaims
import Leanux.Proofs.WG.Config.EndpointPaginationClaims
import Leanux.Proofs.WG.Config.MultiMixedClaims
import Leanux.Proofs.WG.Config.MultiPeerScalarClaims
import Leanux.Proofs.WG.Config.MultiPeerGetterClaims
import Leanux.Proofs.WG.Config.KeyPaginationClaims
import Leanux.Proofs.WG.Config.MixedPaginationClaims
import Leanux.Proofs.WG.Config.PaginationClaims
import Leanux.Proofs.WG.Config.KeyReadbackClaims
import Leanux.Proofs.WG.Config.PortRefusalClaims
import Leanux.Proofs.WG.Config.MixedPeerClaims
import Leanux.Proofs.WG.Config.MixedAttributeClaims
import Leanux.Proofs.WG.Config.LiveRemovalObservation
import Leanux.Proofs.WG.Config.SocketReadbackClaims
import Leanux.Proofs.WG.Config.ScalarSocketReadbackClaims
import Leanux.Proofs.WG.Config.SourceClaims
import Leanux.Proofs.WG.Config.SuffixReadbackClaims
import Leanux.Proofs.WG.Config.ClaimView
import Leanux.Proofs.WG.Config.ObservationBridge
import Leanux.Proofs.WG.Config.LiveRemovalSource
import Leanux.Proofs.WG.Config.AllowedRemovalConverseClaims
import Leanux.Proofs.WG.Config.CollisionRequestSource
import Leanux.Proofs.WG.Config.AllowedRoundTripSource
import Leanux.Proofs.WG.Config.AllowedTransferReadbackSource
import Leanux.Proofs.WG.Config.RemoveFlagRequestSource
import Leanux.Proofs.WG.Config.ReplacementConverseRequestSource
import Leanux.Proofs.WG.Config.RemoveAllObservationSource
import Leanux.Proofs.WG.Config.ReplacePeersRequestClaims
import Leanux.Proofs.WG.Config.MultipartClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Invalid allowed-IP family, length, prefix or missing attributes return
EINVAL and leave the WireGuard core unchanged; records of the tests are still emitted. -/
theorem original_invalid_allowedip (pid : PeerId) (ip : AllowedIpAttrs)
    (invalid : ¬ validAllowedIp ip) (initial : Campaign2.Core) :
    Campaign2.Ensures (setAllowedip pid ip) (fun w => w.wg.toCore = initial)
      (fun ret w => ret = -EINVAL ∧ w.wg.toCore = initial) := by
  intro g ambient ret final after hp hr
  have h := setAllowedip_rejected pid ip invalid g g ambient ret final after rfl hr
  exact ⟨h.1, (congrArg Campaign2.core h.2).trans hp⟩


/-- With sufficient tailroom, the original allowed-IP dump emits exactly
its family/address/prefix fields, preserves the WireGuard core and consumes their space. -/
theorem original_allowedip_dump (skb : NlSkb) (family masked cidr : Nat)
    (room : allowedIpSpace family ≤ skb.room) (initial : Campaign2.Core) :
    Campaign2.Ensures (getAllowedips skb family masked cidr) (fun w => w.wg.toCore = initial)
      (fun result w => w.wg.toCore = initial ∧ result =
        ({ skb with room := skb.room - allowedIpSpace family },
          some (Lean.Json.mkObj [("family", Lean.toJson family),
            ("addr", Lean.toJson (hexBE masked (if family = 6 then 16 else 4))),
            ("cidr", Lean.toJson cidr)]))) := by
  intro g ambient ret final after hp hr
  have h := getAllowedips_exact skb family masked cidr room g g ambient ret final after rfl hr
  exact ⟨(congrArg Campaign2.core h.1).trans hp, h.2⟩


/-- The private-key leaf clamps the stored key, uses generation's identity
flag, and retains the previous public bytes when the null-secret arm writes none. -/
theorem original_static_identity (key : Key) (d : Device) :
    Campaign2.Ensures (setStaticIdentityPrivateKey key) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some { d with staticIdentity := identityAfter key d.staticIdentity }) :=
  SourceClaims.original_static_identity key d

/-- Static-static precomputation updates exactly the resident peer's DH
field; absent identity or a null result stores 32 zero bytes. -/
theorem original_static_precomputation (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (precomputeStaticStatic pid) (fun w => w.wg.device = some d)
      (fun _ w => w.peerAt pid = some
        { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p }) :=
  SourceClaims.original_static_precomputation pid d p resident

/-- A normal listen-port update while down stores the requested port and
preserves both socket pointers and down status; it may clear endpoint caches. -/
theorem original_down_port (port old : Nat) (sock4 sock6 : Option Nat) :
    Campaign2.Ensures (setPort port)
      (fun w => ClaimView.portState w.wg.toCore = some (old, sock4, sock6, false))
      (fun ret w => ret = 0 ∧ ClaimView.portState w.wg.toCore = some (port, sock4, sock6, false)) :=
  SourceClaims.original_down_port port old sock4 sock6

/-- For a missing public key, valid remove or update-only requests return zero
and preserve the WireGuard core on normal completion. -/
theorem original_absent_remove_update (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : Campaign2.Core) (d : Device)
    (device : initial.device = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (noCreate : flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) ≠ 0) :
    Campaign2.Ensures (setPeerCmd a) (fun w => w.wg.toCore = initial)
      (fun ret w => ret = 0 ∧ w.wg.toCore = initial) := by
  intro g ambient ret final after hp hr
  have hd : g.dev = some d := (congrArg Campaign2.Core.device hp).trans device
  have h := setPeer_absent_remove_update a key flags g d hd missing pubkey flagattr valid protocol noCreate g ambient ret final after rfl hr
  exact ⟨h.1, (congrArg Campaign2.core h.2).trans hp⟩


/-- An unknown peer flag with a supplied public key returns EOPNOTSUPP
and preserves the WireGuard core on normal completion. -/
theorem original_invalid_peer_flags (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (invalid : flags &&& ~~~WGPEER_F_ALL ≠ 0) (initial : Campaign2.Core) :
    Campaign2.Ensures (setPeerCmd a) (fun w => w.wg.toCore = initial)
      (fun ret w => ret = -EOPNOTSUPP ∧ w.wg.toCore = initial) := by
  intro g ambient ret final after hp hr
  have h := setPeer_invalid_flags a key flags pubkey flagattr invalid g g ambient ret final after rfl hr
  exact ⟨h.1, (congrArg Campaign2.core h.2).trans hp⟩


/-- A supplied unsupported protocol version, after valid flags, returns
EPFNOSUPPORT and preserves the WireGuard core on normal completion. -/
theorem original_invalid_peer_protocol (a : PeerAttrs) (key : Key) (flags : UInt32)
    (version : Nat) (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = some version) (invalid : version ≠ 1)
    (initial : Campaign2.Core) :
    Campaign2.Ensures (setPeerCmd a) (fun w => w.wg.toCore = initial)
      (fun ret w => ret = -EPFNOSUPPORT ∧ w.wg.toCore = initial) := by
  intro g ambient ret final after hp hr
  have h := setPeer_invalid_protocol a key flags version pubkey flagattr valid protocol invalid g g ambient ret final after rfl hr
  exact ⟨h.1, (congrArg Campaign2.core h.2).trans hp⟩


/-- A valid request for the device identity, absent from the public-key table,
returns zero without changing the WireGuard core on normal completion. -/
theorem original_absent_self_peer (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : Campaign2.Core) (d : Device)
    (device : initial.device = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (identity : d.staticIdentity.hasIdentity = true) (self : key = d.staticIdentity.staticPublic) :
    Campaign2.Ensures (setPeerCmd a) (fun w => w.wg.toCore = initial)
      (fun ret w => ret = 0 ∧ w.wg.toCore = initial) := by
  intro g ambient ret final after hp hr
  have hd : g.dev = some d := (congrArg Campaign2.Core.device hp).trans device
  have h := setPeer_absent_self a key flags g d hd missing pubkey flagattr valid protocol identity self g ambient ret final after rfl hr
  exact ⟨h.1, (congrArg Campaign2.core h.2).trans hp⟩


/-- At the acquired-peer stage, removal takes precedence over every
attribute update; the projected agreement includes the subsequent peer put. -/
theorem original_acquired_remove_precedence (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0) :
    Campaign2.Product.AgreesOn (fun _ => True) (liftWG (peerConfigUpdateSource a peer flags psk pid)) (liftWG (do
      _ ← branch .peerRemoveMe true
      peerRemove peer
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure 0)) := by
  intro w _
  rw [SourceClaims.original_acquired_remove_precedence a peer flags psk pid remove]


/-- The validation, lookup and acquired-peer stages used above are exactly
the original peer setter, including every return and Stop. -/
theorem original_peer_set_source (a : PeerAttrs) :
    Campaign2.Product.AgreesOn (fun _ => True) (liftWG (setPeerCmdSource a)) (liftWG (setPeerCmd a)) := by
  intro w _
  rw [SourceClaims.original_peer_set_source a]


/-- For an existing peer with positive reference count while down, normal completion stores the
preshared key and keepalive interval through the exact device updates. -/
theorem original_peer_scalars_down (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (down : d.running = false) :
    Campaign2.Ensures (setPeerCmd (scalarAttrs key psk interval)) (fun w => w.wg.device = some d)
      (fun ret w => ret = 0 ∧ w.wg.device = some (scalarDevice d pid p psk interval)) :=
  SourceClaims.original_peer_scalars_down key psk interval pid d p found resident live down

/-- For a resident peer without allowed IPs, a fresh peer chunk with at least 168 bytes of
room serializes its fixed fields and preserves that peer on normal completion. -/
theorem original_fresh_peer_dump (pid : PeerId) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Campaign2.Ensures (getPeerDump pid ctx skb) (fun w => w.peerAt pid = some p)
      (fun result w => w.peerAt pid = some p ∧ result =
        ({ skb with room := skb.room - peerFixedSpace p },
         { ctx with nextAllowedip := none, allowedipsSeq := 0 },
         .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p })) :=
  SourceClaims.original_fresh_peer_dump pid p ctx skb fresh empty room

/-- Setting an existing peer with positive reference count while down and then dumping it reads back
the requested preshared key and keepalive interval on normal completion.
This covers a fresh peer chunk with at least 168 bytes of room and an empty allowed-IP list. -/
theorem original_scalars_get_after_set (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (down : d.running = false)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Campaign2.Ensures (do
      let ret ← setPeerCmd (scalarAttrs key psk interval)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun w => w.wg.device = some d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        w.peerAt pid = some updated ∧ result =
          (0, { skb with room := skb.room - peerFixedSpace updated },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) :=
  SourceClaims.original_scalars_get_after_set key psk interval pid d p ctx skb found resident live down fresh empty room

/-- An outer device set updates the first peer and increments the device
generation before a following malformed peer entry returns EINVAL.
With the stated reference-count bound and device selection, it returns normally. -/
theorem original_device_partial_error (d : Device) (key psk : Key) (interval : Nat)
    (pid : PeerId) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Campaign2.Returns (wgSetDevice (partialAttrs d key psk interval))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = -EINVAL ∧ w.wg.device = some
        (scalarDevice { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid p psk interval)) :=
  SourceClaims.original_device_partial_error d key psk interval pid p found resident live bounded down

/-- The outer setter returns EINVAL for a later malformed peer entry; a
subsequent peer dump returns normally and reads back the earlier scalar update.
The count bound, stopped device, empty allowed-IP list and tailroom are explicit. -/
theorem original_partial_error_readback (d : Device) (key psk : Key) (interval : Nat)
    (pid : PeerId) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Campaign2.Returns (do
      let ret ← wgSetDevice (partialAttrs d key psk interval)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        w.peerAt pid = some updated ∧ result =
          (-EINVAL, { skb with room := skb.room - peerFixedSpace updated },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) :=
  SourceClaims.original_partial_error_readback d key psk interval pid p ctx skb found resident live bounded down fresh empty room

/-- The stopped-device scalar setter returns normally and establishes the
exact device update when the peer reference count is positive and cannot overflow. -/
theorem original_peer_scalars_return (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Campaign2.Returns (setPeerCmd (scalarAttrs key psk interval)) (fun w => w.wg.device = some d)
      (fun ret w => ret = 0 ∧ w.wg.device = some (scalarDevice d pid p psk interval)) :=
  SourceClaims.original_peer_scalars_return key psk interval pid d p found resident live bounded down

/-- A scalar set and subsequent peer dump both return normally and read back
the requested preshared key and keepalive interval, under the stated count,
stopped-device, empty allowed-IP list and sufficient-tailroom premises. -/
theorem original_scalar_roundtrip_returns (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Campaign2.Returns (do
      let ret ← setPeerCmd (scalarAttrs key psk interval)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun w => w.wg.device = some d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        w.peerAt pid = some updated ∧ result =
          (0, { skb with room := skb.room - peerFixedSpace updated },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) :=
  SourceClaims.original_scalar_roundtrip_returns key psk interval pid d p ctx skb found resident live bounded down fresh empty room

/-- Clearing a resident peer zeroes its cached local source addresses and
drops its cached destination; only the cache reset timestamp is unspecified.
Other peer entries and all other device fields are preserved on normal completion. -/
theorem original_endpoint_source_clear (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (clearPeerEndpointSrc pid) (fun w => w.wg.device = some d)
      (fun _ w => ∃ d' reset, w.wg.device = some d' ∧
        d' = { d with peers := d'.peers } ∧
        d'.peers[pid]? = some (clearedSource p reset) ∧
        ∀ q, q ≠ pid → d'.peers[q]? = d.peers[q]?) :=
  SourceClaims.original_endpoint_source_clear pid d p resident

/-- On normal completion, a fwmark-only outer set writes the mark and increments
the generation, preserving every other device field outside the peer store.
The creating namespace exists and the request selects this device by index. -/
theorem original_fwmark_device_frame (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Campaign2.Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 })) :=
  SourceClaims.original_fwmark_device_frame d mark net

/-- On normal completion, a fwmark-only outer set clears local endpoint
sources and cached destination slots for every peer in the device list.
It also writes the mark, increments generation and frames other device fields. -/
theorem original_fwmark_clears_listed_peers (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Campaign2.Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        ClaimView.sourcesClear w.wg.toCore d.peerList) :=
  SourceClaims.original_fwmark_clears_listed_peers d mark net

/-- Socket replacement returns normally, installs both supplied socket
pointers, and takes the incoming port from the supplied IPv4 socket,
preserving it when that socket is absent.
Every other device field is preserved. -/
theorem original_socket_reinit (new4 new6 : Option Nat) (d : Device) :
    Campaign2.Returns (socketReinit new4 new6) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some
        { d with sock4 := new4, sock6 := new6, incomingPort := new4.getD d.incomingPort }) :=
  SourceClaims.original_socket_reinit new4 new6 d

/-- With an existing creating namespace and a nonzero requested port,
socket initialization returns normally: a conflict returns EADDRINUSE with
the device unchanged; otherwise both sockets and the incoming port are replaced. -/
theorem original_nonzero_socket_init (port : Nat) (nonzero : port ≠ 0)
    (d : Device) (bound : Bool) (net : d.creatingNet = true) :
    Campaign2.Returns (socketInit port) (fun w => w.wg.device = some d ∧ w.wg.portBound port = bound)
      (fun ret w => if bound || d.sock4 == some port || d.sock6 == some port
        then ret = -EADDRINUSE ∧ w.wg.device = some d
        else ret = 0 ∧ w.wg.device = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) :=
  SourceClaims.original_nonzero_socket_init port nonzero d bound net

/-- On normal completion, a fwmark-only outer set changes each listed peer
only by clearing local source addresses and its cached destination and possibly
updating the cache-reset timestamp. Unlisted peer entries are unchanged.
The mark/generation writes and every other device field are also specified. -/
theorem original_fwmark_peer_store_effects (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Campaign2.Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        ClaimView.clearedPeers d w.wg.toCore d.peerList) :=
  SourceClaims.original_fwmark_peer_store_effects d mark net

/-- A nonzero port request equal to the current port preserves the device.
Otherwise every listed peer has its local source/cache cleared, including when
socket initialization returns an error; the non-peer device fields have the
specified stopped/running, namespace and bind-conflict outcome. This contract
concerns normal completion. -/
theorem original_nonzero_port_effects (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (bound : Nat → Bool) :
    Campaign2.Ensures (setPort port) (fun w => w.wg.device = some d ∧ w.wg.portBound = bound)
      (fun ret w => if d.incomingPort = port then ret = 0 ∧ w.wg.device = some d
        else ret = (portOutcome d port bound).1 ∧
          w.wg.device.map withoutPeers = some (withoutPeers (portOutcome d port bound).2) ∧
          ClaimView.clearedPeers d w.wg.toCore d.peerList) :=
  SourceClaims.original_nonzero_port_effects d port nonzero bound

/-- A port-only outer configuration request increments the device generation.
For a nonzero port, it then has exactly the set_port effects, including retained
source/cache clearing on a bind error. The namespace exists; normal completion
is assumed. -/
theorem original_device_nonzero_port (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (net : d.creatingNet = true) (bound : Nat → Bool) :
    Campaign2.Ensures (wgSetDevice (portAttrs d port))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d ∧ w.wg.portBound = bound)
      (fun ret w =>
        let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
        if d.incomingPort = port then ret = 0 ∧ w.wg.device = some updated
        else ret = (portOutcome updated port bound).1 ∧
          w.wg.device.map withoutPeers = some (withoutPeers (portOutcome updated port bound).2) ∧
          ClaimView.clearedPeers d w.wg.toCore d.peerList) :=
  SourceClaims.original_device_nonzero_port d port nonzero net bound

/-- On normal completion in an existing namespace, port-zero initialization
installs both sockets at the same selected port in the configured local range,
preserving every other device field. -/
theorem original_zero_socket_range (d : Device) (net : d.creatingNet = true) :
    Campaign2.Ensures (socketInit 0) (fun w => w.wg.device = some d)
      (fun ret w => ret = 0 ∧ ∃ port,
        LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧ w.wg.device = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) :=
  SourceClaims.original_zero_socket_range d net

/-- With an explicit correctly padded UDP draw at the head of the records,
an existing namespace and a free first candidate, port-zero initialization
returns normally and installs exactly the port computed from the four draw
bytes. Other device fields are preserved. -/
theorem original_zero_socket_record_return (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) :
    Campaign2.Returns (socketInit 0)
      (fun w => w.wg.device = some d ∧
        w.ambient.hidden = some (udpDrawRecord a b c e :: rest) ∧ w.wg.portBound (drawnPort a b c e) = false)
      (fun ret w => ret = 0 ∧ w.wg.device = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e }) :=
  SourceClaims.original_zero_socket_record_return d net a b c e rest free4 free6

/-- In an existing namespace, normal completion of a port-zero request
returns zero. An existing zero port is a no-op; otherwise listed peer sources
and caches are cleared, a stopped device stores zero, and a running device
installs both sockets at a port within the local range. Other fields are framed. -/
theorem original_zero_port_effects (d : Device) (net : d.creatingNet = true) :
    Campaign2.Ensures (setPort 0) (fun w => w.wg.device = some d)
      (fun ret w => ret = 0 ∧ ClaimView.zeroPortEffects d w) :=
  SourceClaims.original_zero_port_effects d net

/-- A port-zero outer configuration request in an existing namespace
increments the device generation and has the specified no-op, stopped-device,
or running-allocation effects on normal completion. -/
theorem original_device_zero_port (d : Device) (net : d.creatingNet = true) :
    Campaign2.Ensures (wgSetDevice (portAttrs d 0))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ ClaimView.zeroPortEffects
        { d with deviceUpdateGen := d.deviceUpdateGen + 1 } w) :=
  SourceClaims.original_device_zero_port d net

/-- An explicit free first-candidate draw in an existing namespace guarantees
socket initialization returns normally and installs the computed port. It consumes exactly the head
draw record and preserves the remaining record list through socket replacement. -/
theorem original_zero_socket_record_tail (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) :
    Campaign2.Returns (socketInit 0)
      (fun w => w.wg.device = some d ∧
        w.ambient.hidden = some (udpDrawRecord a b c e :: rest) ∧ w.wg.portBound (drawnPort a b c e) = false)
      (fun ret w => ret = 0 ∧ w.wg.device = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e } ∧
        w.ambient.hidden = some rest) :=
  SourceClaims.original_zero_socket_record_tail d net a b c e rest free4 free6

/-- With an explicit draw whose first candidate is occupied, socket
initialization stops at the mirror's declared domain boundary with its collision
message. This describes the modeled-domain stop, not a kernel bind error or
a claim about the kernel's collision retry behavior. -/
theorem original_zero_socket_collision_stop (d : Device) (a b c e : UInt8)
    (rest : List HiddenRecord) (net : d.creatingNet = true) :
    Campaign2.Observes (socketInit 0)
      (fun w => w.wg.device = some d ∧
        w.ambient.hidden = some (udpDrawRecord a b c e :: rest) ∧
        (w.wg.portBound (drawnPort a b c e) || d.sock4 == some (drawnPort a b c e) ||
          d.sock6 == some (drawnPort a b c e)) = true)
      (fun _ out => ∃ site, out = .error
        (.outsideDomain site "the random port draw collides with a bound port")) :=
  SourceClaims.original_zero_socket_collision_stop d a b c e rest net

/-- Cookie-key precomputation returns normally. It changes only the device
cookie-encryption and MAC1 keys, to the specified public-key hashes when identity
exists and to zero otherwise. -/
theorem original_cookie_precomputation_return (d : Device) :
    Campaign2.Returns cookiePrecomputeDeviceKeys (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some (cookieKeysAfter d)) :=
  SourceClaims.original_cookie_precomputation_return d

/-- Identity installation returns normally, clamps the private bytes and
sets the public identity as specified, preserving all other device fields. -/
theorem original_identity_install_return (key : Key) (d : Device) :
    Campaign2.Returns (setStaticIdentityPrivateKey key) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some { d with staticIdentity := identityAfter key d.staticIdentity }) :=
  SourceClaims.original_identity_install_return key d

/-- A private-key-only request equal byte-for-byte to the stored private key
returns normally and changes only the device generation. Equality is against
the raw request, not a normalized equivalence class of keys. -/
theorem original_unchanged_private_key_return (d : Device) (key : Key)
    (same : d.staticIdentity.staticPrivate = key) :
    Campaign2.Returns (wgSetDevice (privateKeyAttrs d key))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device = some { d with deviceUpdateGen := d.deviceUpdateGen + 1 }) :=
  SourceClaims.original_unchanged_private_key_return d key same

/-- Static-static precomputation for a resident peer returns normally with
the exact ordered peer-store updates, including the intermediate DH write
before zeroing a null result. All surrounding device fields are preserved. -/
theorem original_static_precomputation_return (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Returns (precomputeStaticStatic pid) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some (precomputeDevice d pid p)) :=
  SourceClaims.original_static_precomputation_return pid d p resident

/-- Normal completion of expiry removes the peer's handshake entries, zeros
handshake fields, preserves its slots, and invalidates next/current sending keys.
The exact store transformation preserves all other fields except last-sent time.
Its existential clock parameter does not constrain that time or prove clock-read
provenance. Missing keypair targets can stop; no return guarantee is claimed. -/
theorem original_expiry_store_effects (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) (fun w => w.wg.device = some d)
      (fun _ w => ∃ now, w.wg.device = some (expiredDevice d pid p now)) :=
  SourceClaims.original_expiry_store_effects pid d p resident

/-- On normal completion, expiry changes only sending validity in current
and next keypair entries. Every other keypair field and lookup is preserved.
Aliased slots are covered by the union of the two target identities. -/
theorem original_expiry_keypair_fields (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (q : KeypairId) :
    Campaign2.Ensures (expireCurrentPeerKeypairs pid) (fun w => w.wg.device = some d)
      (fun _ w => (w.wg.device.bind fun dev => dev.keypairs[q]?) = (d.keypairs[q]?).map fun k =>
        if p.keypairNext = some q ∨ p.keypairCurrent = some q then
          { k with sending := { k.sending with isValid := false } } else k) :=
  SourceClaims.original_expiry_keypair_fields pid d p resident q

/-- Every normally completed original expiry run has an actual prefix and
reset-clock read whose returned value determines the final store, including
last-sent time minus six seconds in wrapping Int64 arithmetic. The prefix and read are inspected from the same concrete entry before the
original operation; this is not merely an unconstrained existential timestamp. -/
theorem original_expiry_clock_relation (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Product.Ensures (observedExpiry pid) (fun s => s.wg.device = some d)
      (fun observation final => ∃ now before after,
        observation = .ok ((before, now), after) ∧
        final.wg.device = some (expiredDevice d pid p now)) :=
  observedExpiry_effect pid d p resident


/-- Exact projected source agreement exposing identity installation and the peer-list
loop after optional self-peer removal, before later peer attributes. This is
unconditional; the effects below separately require normal completion. -/
theorem original_private_key_factor (a : DeviceAttrs) :
    Campaign2.Product.AgreesOn (fun _ => True) (liftWG (deviceKeyFactoredSource a)) (liftWG (deviceKeySource a)) := by
  intro w _
  rw [SourceClaims.original_private_key_factor a]


/-- With staged sending disabled, a completed peer update precomputes its
static-static value and performs the exact expiry store transformation. The
clock here is existential; the stronger per-expiry read relation is separate. -/
theorem original_quiet_key_peer (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (keyPeerSource pid false) (fun w => w.wg.device = some d)
      (fun _ w => ∃ now, w.wg.device = some (peerUpdatedDevice d pid p now)) :=
  SourceClaims.original_quiet_key_peer pid d p resident

/-- A completed quiet peer-list loop has the ordered relational effects of
each resident peer update. Repeated peers and aliased keypair slots are allowed;
missing peers or hidden inputs may stop, so this is not a return guarantee. -/
theorem original_quiet_key_peer_loop (pids : List PeerId) (d : Device) :
    Campaign2.Ensures (keyPeerLoopSource pids false) (fun w => w.wg.device = some d)
      (fun _ w => ∃ final, w.wg.device = some final ∧ KeyPeerUpdates d pids final) :=
  SourceClaims.original_quiet_key_peer_loop pids d

/-- The quiet installation block sets identity and cookie keys, then applies
ordered precomputation/expiry to its snapshotted peer list. The initial device
is after optional collision removal; later peer attributes are outside this
block. Normal completion is assumed, and clock values remain existential. -/
theorem original_quiet_key_install (d : Device) (key : Key)
    (quiet : requestsStagedSend d key = false) :
    Campaign2.Ensures (keyInstallSource key) (fun w => w.wg.device = some d)
      (fun _ w => ∃ final, w.wg.device = some final ∧
        KeyPeerUpdates (installedDevice d key) d.peerList final) :=
  SourceClaims.original_quiet_key_install d key quiet

/-- The actual prefix and clock read come from the same full Product entry.
The final Device is selected by an existential actual queue inspection, retaining
age/dead guards and the inspection-dependent reference effect. The returned
payload records clock states, not a queue-inspection certificate. -/
theorem original_queued_handshake_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Product.Ensures (observedQueuedHandshake pid) (fun s => s.wg.device = some d)
      (fun observation final => ∃ now seen before after,
        observation = .ok (({ p with timerHandshakeAttempts := 0 }, before, now), after) ∧
        match seen with
        | none => final.wg.device = some (withPeer d pid {p with timerHandshakeAttempts := 0}) ∧
            (¬p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∨ p.isDead = true)
        | some queued => p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now ∧
            p.isDead = false ∧ final.wg.device = some (queuedDeviceAfterInspection
              (withPeer d pid {p with timerHandshakeAttempts := 0})
              pid {p with timerHandshakeAttempts := 0} now queued)) :=
  observedQueuedHandshake_effect pid d p resident


/-- Corrected invalid-key effects use the observation of actual staging and
queue inspection. The original invalid-key domain is retained; an empty list
returns unchanged, while missing prerequisites may still stop. This is a
normal-completion claim over the decorated original action. -/
theorem original_staged_invalid_key (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (invalid : ∀ id k, p.keypairCurrent = some id → d.keypairs[id]? = some k → k.sending.isValid = false) :
    Campaign2.Ensures (observedInvalidStaged pid) (fun s => s.wg.device = some d)
      (invalidStagedObservation d pid p) :=
  SourceClaims.original_staged_invalid_key pid d p resident invalid


/-- Corrected peer effects retain actual precomputation, expiry and optional
staged-send observations, on the original resident-peer domain. Clock and queue
consequences are taken from those actual inspections; completion is assumed. -/
theorem original_key_peer_effects (pid : PeerId) (d : Device) (p : Peer) (sendStaged : Bool)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (observedKeyPeerSource pid sendStaged) (fun s => s.wg.device = some d)
      (keyPeerObservation d pid p sendStaged) :=
  SourceClaims.original_key_peer_effects pid d p sendStaged resident


/-- The actual ordered peer observations determine the corrected Device
relation for either staged-send setting. Repeated peers and aliases remain
permitted, and normal completion is assumed. -/
theorem original_key_peer_loop_effects (pids : List PeerId) (d : Device) (sendStaged : Bool) :
    Campaign2.Ensures (observedKeyPeerLoopSource pids sendStaged)
      (fun s => s.wg.device = some d)
      (fun observations s => ∃ final, s.wg.device = some final ∧
        ObservedKeyPeerRun sendStaged d pids observations final) :=
  SourceClaims.original_key_peer_loop_effects pids d sendStaged


/-- The installation relation follows actual peer observations after identity
and cookie-key publication. It starts after optional collision removal and
preserves the original domain; this is a normal-completion contract. -/
theorem original_key_install_effects (d : Device) (key : Key) :
    Campaign2.Ensures (observedKeyInstallSource key) (fun s => s.wg.device = some d)
      (fun observations s => ∃ final, s.wg.device = some final ∧
        ObservedKeyPeerRun (requestsStagedSend d key) (installedDevice d key) d.peerList observations final) :=
  SourceClaims.original_key_install_effects d key


/-- A single empty-device getter is accepted from the runner's ordinary
fixture with an empty hidden record list. This establishes reachability of the
cancelled-nest accounting case, not a changed external observation. -/
theorem empty_dump_trace_accepted : DumpCancellation.accepted = true :=
  SourceClaims.empty_dump_trace_accepted

/-- The original empty-device dump callback completes with one message,
a cleared cursor and 3720 bytes of tailroom. This retains the cancelled nest's
four bytes; the source correspondence discrepancy is recorded in request 3. -/
theorem original_empty_dump_room : DumpCancellation.callbackResult = some (0, 3720, true, 1) :=
  SourceClaims.original_empty_dump_room

/-- The C-derived accounting of the retained header and attributes leaves
3724 bytes, exactly one cancelled nest header more than the mirror witness.
This is arithmetic supporting the source review, not a formal C simulation. -/
theorem empty_dump_cancellation_accounting :
    DumpCancellation.cancelledNestRoom = 3724 ∧ 3720 + nlaTotal 0 = DumpCancellation.cancelledNestRoom :=
  SourceClaims.empty_dump_cancellation_accounting

/-- On the original changed-key/no-collision domain, normal completion returns
zero and the observed installation relation after generation update. No input
record availability or aggregate clock provenance is assumed. -/
theorem original_private_key_request_no_collision (d : Device) (key : Key)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key) :
    Campaign2.Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d)
      (fun ret s => ret = 0 ∧ ∃ final observations, s.wg.device = some final ∧
        ObservedKeyPeerRun (requestsStagedSend d key)
          (installedDevice (requestGeneration d) key) d.peerList observations final) :=
  SourceClaims.original_private_key_request_no_collision d key changed absent


/-- A fresh original callback for one resident peer without allowed IPs
returns all fixed device and peer attributes, completes its cursor and preserves
the device. The bound reserves room for the transport's final DONE message. -/
theorem original_single_peer_dump_callback (pid : PeerId) (d : Device) (p : Peer)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE) :
    Campaign2.Returns (wgGetDeviceDump { hasWg := true } 0 {}) (fun w => w.wg.device = some d)
      (fun result w => result = singlePeerDump d p ∧ w.wg.device = some d) :=
  SourceClaims.original_single_peer_dump_callback pid d p peers resident empty room

/-- The original public getter for one resident peer without allowed IPs
returns exact canonical JSON, including the empty allowed-IP array, preserves
the device and leaves socket 7 drained and finished. The socket starts idle
with an empty queue; its bound flag is unrestricted. This is a total-return
contract for one complete chunk, not a multipart snapshot theorem. -/
theorem original_single_peer_getter (pid : PeerId) (d : Device) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun w => w.wg.device = some d ∧ w.wg.nlSock7 = sock ∧ ClaimView.selectsDevice w d)
      (fun result w => result = .ok (singlePeerJson d p) ∧ w.wg.device = some d ∧
        w.wg.nlSock7 = { completedSock sock d p with queue := [] }) :=
  SourceClaims.original_single_peer_getter pid d p sock peers resident noIps room idle empty

/-- Setting an existing stopped peer's preshared key and keepalive interval,
then calling the original public getter after either setter return, returns the
exact applied configuration
and a drained socket. A malformed second peer entry makes the setter return
EINVAL but does not roll back the first update; the same readback holds.
The bound on the live reference count guarantees the temporary lookup reference
can be acquired. The single peer has no allowed IPs and fits one dump chunk. -/
theorem original_scalar_get_after_set (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun w => w.wg.device = some d ∧ w.wg.nlSock7 = sock ∧ ClaimView.selectsDevice w d)
      (fun result w =>
        let updated := scalarRequestDevice d pid p psk interval
        let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        result = ((if bad then -EINVAL else 0), .ok (singlePeerJson updated configured)) ∧
          w.wg.device = some updated ∧
          w.wg.nlSock7 = { completedSock sock updated configured with queue := [] }) :=
  SourceClaims.original_scalar_get_after_set d key psk interval bad pid p sock peers found resident live bounded down noIps room idle empty

/-- Replacing a stopped peer's singleton root-leaf allowed-IP list with an
empty list removes the node, clears its family root, increments the trie
sequence, and removes that node from every peer list. The public device
setter increments its generation and balances the lookup reference. -/
theorem original_allowedips_replace_single_root (v4 : Bool) (key : Key) (pid : PeerId)
    (d : Device) (p : Peer) (id : NodeId) (n : AipNode)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (peer : d.peers[pid]? = some p) (listed : p.allowedipsList = [id])
    (resident : d.nodes[id]? = some n) (leaf : n.bit = #[none, none])
    (parent : n.parent = rootSlot v4) (owned : n.peer = some pid)
    (root : (if v4 then d.peerAllowedips.root4 else d.peerAllowedips.root6) = some id)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Campaign2.Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w =>
        let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
        ret = 0 ∧ w.wg.device = some (rootReplacementDevice v4 updated pid p id n) ∧
          RootReplacementEffects v4 updated id (rootReplacementDevice v4 updated pid p id n)) :=
  SourceClaims.original_allowedips_replace_single_root v4 key pid d p id n found peer listed resident leaf parent owned root live bounded down

/-- A supplied pure removal witness covers every structural branch and the evolving
snapshot loop. The original operation returns, filters the removed identities from
every peer list, clears every processed node owner, empties the target list and
increments the sequence once exactly
when the snapshot was nonempty. This does not establish witness existence for all
valid tries, trie validity, lookup preservation or ownership/list coherence. -/
theorem original_allowedips_remove_general (pid : PeerId) (p : Peer) (d final : Device)
    (resident : d.peers[pid]? = some p) (steps : RemovalEffect d p.allowedipsList final) :
    Campaign2.Returns (removeByPeer pid) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some final ∧
        (∀ other : PeerId, final.peers[other]? = d.peers[other]?.map (erasePeerList p.allowedipsList)) ∧
        final.peers[pid]? = some (erasePeerList p.allowedipsList p) ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        final.peerAllowedips.seq = d.peerAllowedips.seq + (if p.allowedipsList.isEmpty then 0 else 1) ∧
        ∀ id ∈ p.allowedipsList, nodeOwner final id = none) :=
  SourceClaims.original_allowedips_remove_general pid p d final resident steps

/-- The public setter replaces an existing stopped peer's allowed-IP list by the
empty list for any supplied pure removal witness. The lookup reference is balanced
and peer identity is preserved; every processed node is absent or unowned.
Readiness is checked on successive maps, including
the acquired reference and updated generation; no global trie invariant or general
existence of a removal witness is claimed. -/
theorem original_allowedips_replace_general (key : Key) (pid : PeerId) (d removed : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (steps : RemovalEffect
      (withPeer { d with deviceUpdateGen := d.deviceUpdateGen + 1 } pid { p with refcount := p.refcount + 1 })
      p.allowedipsList removed) :
    Campaign2.Returns (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun w => w.wg.device = some d ∧ ClaimView.selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.wg.device = some (generalReplacementDevice removed pid p) ∧
        ∃ q, (generalReplacementDevice removed pid p).peers[pid]? = some q ∧
          q.allowedipsList = [] ∧ q.refcount = p.refcount ∧ q.internalId = p.internalId ∧
          ∀ id ∈ p.allowedipsList, nodeOwner (generalReplacementDevice removed pid p) id = none) :=
  SourceClaims.original_allowedips_replace_general key pid d removed p found resident live bounded down steps

/-- Original peer death removes the identity from the device peer list and
public-key table, performs the witnessed allowed-IP removal and sets isDead.
The peer remains resident with its original reference count; the numeric index
table and device peer count are unchanged at this stage. Every processed node
is absent or unowned. This is peerMakeDead, before later keypair/timer/work
cleanup and final reference release; no complete peerRemove claim is made. -/
theorem original_peer_make_dead (pid : PeerId) (p : Peer) (d removed : Device)
    (resident : d.peers[pid]? = some p)
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    Campaign2.Returns (peerMakeDead pid) (fun w => w.wg.device = some d)
      (fun _ w =>
        let final := deadPeerDevice removed pid p
        w.wg.device = some final ∧
        final.peerList = d.peerList.filter (· != pid) ∧
        final.peerHashtable = d.peerHashtable.filter (·.2 != pid) ∧
        final.indexTable = d.indexTable ∧ final.numPeers = d.numPeers ∧
        final.peers[pid]? = some { erasePeerList p.allowedipsList p with isDead := true } ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        (erasePeerList p.allowedipsList p).refcount = p.refcount ∧
        (∀ id ∈ p.allowedipsList, nodeOwner final id = none)) :=
  SourceClaims.original_peer_make_dead pid p d removed resident steps

/-- The original quiet-removal domain admits exact crypt-work and final-reference
refusals, so its former totality is corrected to an outcome contract. Successful
cleanup has the exact ordered Device effect. No new queue/readiness premise
is added; the original empty-key and send/clear-queue premises remain. -/
theorem original_peer_remove_quiet (pid : PeerId) (d removed : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (empty : p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    Campaign2.Observes (peerRemove (some pid)) (fun s => s.wg.device = some d)
      (fun _ out => quietRemovalOutcome (deadPeerDevice removed pid p) pid
        {erasePeerList p.allowedipsList p with isDead := true} out) :=
  SourceClaims.original_peer_remove_quiet pid d removed p resident live count empty send clear steps


/-- Corrected totality: the actual guard, key-clear and timer prefix determines
the exact crypt-work or reference refusal, or the original successful Device
effect. All original static premises remain; both observations share the same
actual native entry states. -/
theorem original_peer_remove_after_dead_live (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (dead : p.isDead = true)
    (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (ready : ClearReady d (clearKeys p))
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    RemovalJointObserves (removalAfterDeadPrefix pid) (peerRemoveAfterDead pid)
      (fun s => s.wg.device = some d) (LiveRemovalOutcomes pid d p) := by
  intro g ambient device
  change g.dev = some d at device
  obtain ⟨guarded, clearedState, clearAmbient, cleared, timedState, timerAmbient,
      guardRun, clearRun, clearedDevice, steps, clearedPeer, timerRun, timedDevice, outcome⟩ :=
    peerRemoveAfterDead_live_returns pid d p resident dead live count ready send clear
      g ambient device
  refine ⟨cleared, Campaign2.snapshot timedState timerAmbient, ?_, steps, clearedPeer,
    timedDevice, outcome⟩
  have read : ((getDev.run clearedState).run clearAmbient) =
      .ok ((cleared, clearedState), clearAmbient) := by
    simp [getDev, clearedDevice]
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), after) =>
          ((next value).run middle).run after) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  simp only [removalAfterDeadPrefix, bindRun, guardRun, clearRun, read, timerRun, okBind]
  rfl


/-- Corrected totality for full removal: the actual non-null/death/clear/timer
prefix supplies the successful cut and precise diagnostic site. Its outcome and
the original operation are observed from the same actual entry. All original
static premises remain and every continuation refusal is retained. -/
theorem original_peer_remove_live (pid : PeerId) (d removed : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (ready : ClearReady d (clearKeys p))
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = [])
    (steps : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) :
    RemovalJointObserves (removalLivePrefix pid) (peerRemove (some pid))
      (fun s => s.wg.device = some d)
      (LiveRemovalOutcomes pid (deadPeerDevice removed pid p)
        {erasePeerList p.allowedipsList p with isDead := true}) := by
  intro g ambient device
  change g.dev = some d at device
  obtain ⟨current, middle, made, currentDevice,
      guarded, clearedState, clearAmbient, cleared, timedState, timerAmbient,
      guardRun, clearRun, clearedDevice, clearSteps, clearedPeer, timerRun, timedDevice, outcome⟩ :=
    peerRemove_live_returns pid d removed p resident live count ready send clear steps
      g ambient device
  refine ⟨cleared, Campaign2.snapshot timedState timerAmbient, ?_, clearSteps, clearedPeer,
    timedDevice, outcome⟩
  let afterNull := {ambient with steps := ambient.steps.push {
    decision := .peerRemoveNull, outcome := false, netRx := ambient.netRxSection}}
  change ((peerMakeDead pid).run g).run afterNull = .ok (((), current), middle) at made
  have nullRun : ((branch .peerRemoveNull false : WG.M Bool).run g).run ambient =
      .ok ((false, g), afterNull) := rfl
  have read : ((getDev.run clearedState).run clearAmbient) =
      .ok ((cleared, clearedState), clearAmbient) := by
    simp [getDev, clearedDevice]
  have bindRun {α β : Type} (action : WG.M α) (next : α → WG.M β)
      (state : WGWorld) (input : Ambient) :
      (((action >>= next).run state).run input) =
        (((action.run state).run input) >>= fun ((value, middle), after) =>
          ((next value).run middle).run after) := rfl
  have okBind {α β : Type} (value : α) (next : α → Except Stop β) :
      (Except.ok value >>= next) = next value := rfl
  simp only [removalLivePrefix, removalAfterDeadPrefix, bindRun, nullRun, made,
    guardRun, clearRun, read, timerRun, okBind]
  rfl


/-- A normally returning original removal derives its structural witness from
the actual successive reads. The only structural premise is that resident nodes
have two child slots; aliases, cycles and repeated list identities are allowed.
All peer lists filter the captured identities, their owners become absent or
unowned, and the sequence increments exactly once for a nonempty captured list.
NodePairs is preserved. No completion or valid-trie claim is made. -/
theorem original_allowedips_remove_pairs (pid : PeerId) (p : Peer) (d : Device)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Campaign2.Ensures (removeByPeer pid) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧ NodePairs final ∧
        RemovalEffect d p.allowedipsList final ∧
        (∀ other : PeerId, final.peers[other]? = d.peers[other]?.map (erasePeerList p.allowedipsList)) ∧
        final.peers[pid]? = some (erasePeerList p.allowedipsList p) ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        final.peerAllowedips.seq = d.peerAllowedips.seq + (if p.allowedipsList.isEmpty then 0 else 1) ∧
        ∀ id ∈ p.allowedipsList, nodeOwner final id = none) :=
  source_allowedips_remove_pairs pid p d resident pairs

/-- Normal original peer death derives its allowed-IP removal witness under the
two-child-slot shape premise, then performs the exact membership/death updates.
The peer stays resident with its original reference count; the numeric index
table and device peer count are unchanged. This stops before later cleanup and
release. No input execution witness, alias exclusion or completion promise is used. -/
theorem original_peer_make_dead_pairs (pid : PeerId) (p : Peer) (d : Device)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Campaign2.Ensures (peerMakeDead pid) (fun s => s.wg.device = some d)
      (fun _ s => ∃ removed, RemovalEffect (unlistPeer d pid) p.allowedipsList removed ∧
        let final := deadPeerDevice removed pid p
        s.wg.device = some final ∧ NodePairs final ∧
        final.peerList = d.peerList.filter (· != pid) ∧
        final.peerHashtable = d.peerHashtable.filter (·.2 != pid) ∧
        final.indexTable = d.indexTable ∧ final.numPeers = d.numPeers ∧
        final.peers[pid]? = some { erasePeerList p.allowedipsList p with isDead := true } ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        (erasePeerList p.allowedipsList p).refcount = p.refcount ∧
        ∀ id ∈ p.allowedipsList, nodeOwner final id = none) :=
  source_peer_make_dead_pairs pid p d resident pairs

/-- A normally returning original single-peer removal derives its actual
allowed-IP removal relation and ordered live-key cleanup from the same run.
The caller is resident with positive reference/device counts, two-child node
shape and empty send/clear queues. No removal witness or static clear-reference
budget is supplied. Aliases are retained; final release can erase the peer or
leave it resident and dead. This does not guarantee completion or cover queued
work or remove-all ordering. -/
theorem original_peer_remove_live_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Campaign2.Ensures (peerRemove (some pid)) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧ CollisionRemovalEffect pid d p final) :=
  peerRemove_live_effect_pairs pid d p resident pairs live count send clear

/-- Normal completion on the original collision domain derives the actual
lookup, balanced reference, removal and observed installation relation. The
post-removal Device supplies the actual peer list; no completion or new
readiness assumption is introduced. -/
theorem original_private_key_request_collision (d : Device) (key pub : Key)
    (pid : PeerId) (p : Peer) (changed : d.staticIdentity.staticPrivate ≠ key)
    (generated : publicResult key = (some pub, true))
    (found : d.peerHashtable.find? (·.1 == pub) = some (pub, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (count : 0 < d.numPeers)
    (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Campaign2.Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d)
      (fun ret s => ret = 0 ∧ ∃ final, s.wg.device = some final ∧
        ObservedCollisionKeyEffect pid (requestGeneration d) p key final) :=
  setDevice_private_collision d key pub pid p changed generated found resident pairs
    live bounded count send clear

/-- Valid original allowed-IP insertion into the selected empty root has two
normal numeric outcomes: allocation failure returns -ENOMEM after the sequence
increment, or success performs the exact allocation, peer-list append, parent
and root writes. Allocation may overwrite an existing node identity; no
freshness, ownership, topology or completion claim is made. -/
theorem original_allowedip_empty_root_insert (v4 : Bool) (d : Device)
    (pid : PeerId) (p : Peer) (addr cidr : Nat)
    (resident : d.peers[pid]? = some p) (root : allowedRootValue v4 d = none)
    (width : cidr ≤ allowedBits v4) :
    Campaign2.Ensures (setAllowedip pid (allowedAttrs v4 addr cidr))
      (fun s => s.wg.device = some d)
      (fun ret s => ∃ final, s.wg.device = some final ∧
        EmptyRootInsertEffect v4 d pid p addr cidr ret final) :=
  setAllowedip_empty_root_effect v4 d pid p addr cidr resident root width

/-- The actual valid setter followed by the actual peer dump reads back one
masked prefix on success and fixed peer attributes without an allowed_ips
attribute after -ENOMEM;
both retain the exact insertion effect, including the sequence increment.
The peer’s allowed-IP list is initially empty, the dump cursor is fresh, its sequence is zero
or matches the incremented sequence, and room is sufficient. The address uses
the model's mask then fixed-width hexBE serialization, including truncation.
Source errors remain errors; this is normal peer-dump scope, not outer socket,
multipart, valid-trie or global ownership coverage. -/
theorem original_allowedip_get_after_set (v4 : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (addr cidr : Nat) (ctx : DumpCtx) (skb : NlSkb)
    (resident : d.peers[pid]? = some p) (empty : p.allowedipsList = [])
    (root : allowedRootValue v4 d = none) (width : cidr ≤ allowedBits v4)
    (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq + 1)
    (room : 172 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    Campaign2.Ensures (do
      let ret ← setAllowedip pid (allowedAttrs v4 addr cidr)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun s => s.wg.device = some d)
      (fun result s => ∃ final, s.wg.device = some final ∧
        EmptyRootInsertEffect v4 d pid p addr cidr result.1 final ∧
        result.2 =
          ({ skb with room := skb.room - (peerFixedSpace p +
             (if result.1 = 0 then 4 + allowedIpSpace (allowedFamily v4) else 0)) },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p ++
             (if result.1 = 0 then [("allowed_ips", Lean.Json.arr #[allowedJson v4 addr cidr])] else []) })) :=
  allowedip_get_after_set v4 d pid p addr cidr ctx skb resident empty root width fresh sequence room

/-- An exact root-leaf match returns zero and transfers its owner with the
original ordered writes. The same raw address/CIDR is requested; stored address,
CIDR, width, child links, parent, roots and allocation cursor are retained.
Every peer list filters all copies
of this identity, then the destination appends it once. Same-peer assignment
and duplicate list entries are allowed; no global topology/ownership invariant,
fresh identity, live reference or running device is assumed. -/
theorem original_allowedip_root_transfer (v4 : Bool) (d : Device) (id : NodeId)
    (addr cidr : Nat) (owner : Option PeerId) (parent : Slot) (target : PeerId) (p : Peer)
    (width : cidr ≤ allowedBits v4) (root : allowedRootValue v4 d = some id)
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) owner with parent })
    (resident : d.peers[target]? = some p) :
    Campaign2.Returns (setAllowedip target (allowedAttrs v4 addr cidr))
      (fun s => s.wg.device = some d)
      (fun ret s => ret = 0 ∧
        let final := transferRequestDevice d id { newNode addr cidr (allowedBits v4) owner with parent } target p
        s.wg.device = some final ∧ ∀ q : PeerId, final.peers[q]? =
          if q = target then some (transferredPeer id p) else d.peers[q]?.map (eraseListedPeer id)) := by
  intro initial ambient pre
  obtain ⟨ret, final, after, run, zero, device⟩ :=
    setAllowedip_root_transfer v4 d id addr cidr owner parent target p width root node resident initial ambient pre
  refine ⟨ret, final, after, run, zero, device, ?_⟩
  intro q
  exact transferRootDevice_peers (insertSequenceDevice d) id _ target q p

/-- The original setter then donor and destination peer dumps share the actual
successive buffer/context. The node's old owner is the distinct resident donor;
its list filters to empty and the destination list is initially empty. Repeated
copies in the donor list are allowed. The donor emits fixed attributes without
allowed_ips; the destination emits the stored masked prefix. The first dump
resets the allowed-IP cursor and sequence, so no initial sequence premise is needed. The resulting
room and cursor are exact. This is peer serialization, not outer socket or
multipart dump coverage. -/
theorem original_allowedip_transfer_readback (v4 : Bool) (d : Device) (id : NodeId) (addr cidr : Nat)
    (parent : Slot) (donor target : PeerId) (oldPeer newPeer : Peer)
    (ctx : DumpCtx) (skb : NlSkb)
    (different : donor ≠ target) (width : cidr ≤ allowedBits v4)
    (root : allowedRootValue v4 d = some id)
    (node : d.nodes[id]? = some { newNode addr cidr (allowedBits v4) (some donor) with parent })
    (oldResident : d.peers[donor]? = some oldPeer) (newResident : d.peers[target]? = some newPeer)
    (oldOnly : listRemove oldPeer.allowedipsList id = []) (newEmpty : newPeer.allowedipsList = [])
    (fresh : ctx.nextAllowedip = none)
    (room : 340 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    Campaign2.Returns (do
      let ret ← setAllowedip target (allowedAttrs v4 addr cidr)
      let first ← getPeerDump donor ctx skb
      let second ← getPeerDump target first.2.1 first.1
      pure (ret, first.2.2, second))
      (fun w => w.wg.device = some d)
      (fun result w => w.wg.device = some
          (transferRequestDevice d id { newNode addr cidr (allowedBits v4) (some donor) with parent } target newPeer) ∧
        result = (0,
          PeerDump.complete { publicKey := hexKey oldPeer.remoteStatic, attrs := peerFixedAttrs oldPeer },
          { skb with room := skb.room - (peerFixedSpace oldPeer + peerFixedSpace newPeer + 4 + allowedIpSpace (allowedFamily v4)) },
          { ctx with nextAllowedip := none, allowedipsSeq := 0 },
          PeerDump.complete { publicKey := hexKey newPeer.remoteStatic, attrs := peerFixedAttrs newPeer ++
            [("allowed_ips", Lean.Json.arr #[allowedJson v4 addr cidr])] })) :=
  transfer_paired_readback v4 d id addr cidr parent donor target oldPeer newPeer ctx skb
    different width root node oldResident newResident oldOnly newEmpty fresh room

/-- A valid REMOVE_ME command for a resident lookup match removes the peer
before installing any later attributes. Lookup acquires one reference,
removal releases one, and the caller releases one. Normal completion returns
zero with the exact ordered removal effect. The peer is erased exactly when
its original reference count was one; otherwise its remaining count is one
less. Node pairs and empty send/clear queues are explicit premises. No
completion, running-state, key-slot or global ownership premise is hidden in
the conclusion; arbitrary later peer attributes are bypassed. -/
theorem original_remove_flag (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pid : PeerId) (d : Device) (p : Peer)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31)
    (count : 0 < d.numPeers) (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Campaign2.Ensures (setPeerCmd a) (fun s => s.wg.device = some d)
      (fun ret s => ret = 0 ∧ ∃ final, s.wg.device = some final ∧
        RemoveFlagEffect pid d p final ∧
        (final.peers[pid]? = none ↔ p.refcount = 1) ∧
        (p.refcount ≠ 1 → ∃ q, final.peers[pid]? = some q ∧ q.refcount = p.refcount - 1)) := by
  intro entry ambient ret out after pre run
  obtain ⟨zero, final, device, effect⟩ := setPeer_remove_flag a key flags pid d p
    pubkey flagattr valid protocol remove found resident pairs live bounded count send clear
    entry ambient ret out after pre run
  exact ⟨zero, final, device, effect, removeFlag_residency effect⟩

/-- The original device setter carries the REMOVE_ME effect through a single
peer entry, with actual interface selection and the preceding generation
increment. This is a normal-return contract with the same quiet-queue and
reference premises as the peer command, not arbitrary mixed device attributes
or queued-work completion. -/
theorem original_device_remove_flag (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pid : PeerId) (d : Device) (p : Peer)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31)
    (count : 0 < d.numPeers) (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    Campaign2.Ensures (wgSetDevice (singlePeerAttrs d a))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d)
      (fun ret s => ret = 0 ∧ ∃ final, s.wg.device = some final ∧
        RemoveFlagEffect pid (requestGeneration d) p final ∧
        (final.peers[pid]? = none ↔ p.refcount = 1) ∧
        (p.refcount ≠ 1 → ∃ q, final.peers[pid]? = some q ∧ q.refcount = p.refcount - 1)) := by
  intro entry ambient ret out after pre run
  obtain ⟨zero, final, device, effect⟩ := setDevice_remove_flag a key flags pid d p
    pubkey flagattr valid protocol remove found resident pairs live bounded count send clear
    entry ambient ret out after pre run
  exact ⟨zero, final, device, effect, removeFlag_residency effect⟩

/-- A normally returning original REPLACE_ALLOWEDIPS request with an empty
replacement list derives its removal witness from execution. The selected
stopped peer remains resident with an empty list, balanced lookup reference
and unchanged identity; every processed node is absent or unowned. The exact
effect includes generation and sequence updates. Only the two-child node
shape is assumed, not a supplied removal run or global trie validity. This
does not assert completion for arbitrary malformed or cyclic structures. -/
theorem original_allowedips_replace_pairs (key : Key) (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d)
    (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Campaign2.Ensures (wgSetDevice (replaceAllowedipsDeviceAttrs d key))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d)
      (fun ret s => ret = 0 ∧ ∃ removed,
        RemovalEffect (withPeer (requestGeneration d) pid { p with refcount := p.refcount + 1 })
          p.allowedipsList removed ∧
        s.wg.device = some (generalReplacementDevice removed pid p) ∧
        (generalReplacementDevice removed pid p).peerAllowedips.seq =
          d.peerAllowedips.seq + (if p.allowedipsList.isEmpty then 0 else 1) ∧
        ∃ q, (generalReplacementDevice removed pid p).peers[pid]? = some q ∧
          q.allowedipsList = [] ∧ q.refcount = p.refcount ∧ q.internalId = p.internalId ∧
          ∀ id ∈ p.allowedipsList, nodeOwner (generalReplacementDevice removed pid p) id = none) := by
  intro entry ambient ret out after pre run
  obtain ⟨zero, removed, steps, device⟩ := setDevice_replace_effect_pairs key pid d p
    found resident pairs live bounded down entry ambient ret out after pre run
  obtain ⟨q, peer, empty, refs, identity⟩ := generalReplacement_peer removed pid p
  refine ⟨zero, removed, steps, device, ?_, q, peer, empty, refs, identity, ?_⟩
  · simpa only [generalReplacementDevice, withPeer, requestGeneration] using removalEffect_seq steps
  · intro id member
    exact removalEffect_owner_none steps id (Or.inl member)

/-- Original remove-all frees allowed IPs, snapshots one peer list, completes
the entire make-dead pass, then runs cleanup over that same list. Exact erasure
preserves errors and the original queued-work cleanup. On normal full return,
the actual post-free device supplies the first-pass inputs. If its listed peers
are resident and its nodes have two child slots, all selected peers are resident
and dead at the cut before cleanup, including duplicate selections. This is a
phase-order contract: it does not assert cleanup completion, final peer erasure,
free's global trie correctness, or the outer REPLACE_PEERS flag composition. -/
theorem original_peer_remove_all_phase_order :
    Campaign2.Product.AgreesOn (fun _ => True) (liftWG peerRemoveAll) (liftWG (do
      free
      let selected := (← getDev).peerList
      removeAllMark selected
      removeAllCleanup selected)) ∧
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedRemoveAll; pure ()) (liftWG peerRemoveAll) ∧
    Campaign2.Product.Ensures observedRemoveAll (fun _ => True) (fun cut _ => RemoveAllFacts cut) := by
  constructor
  · intro entry _pre
    rw [peerRemoveAll_phases]
  · constructor
    · intro entry _pre
      rw [observedRemoveAll_erase]
    · exact observedRemoveAll_facts


/-- A flag-only REPLACE_PEERS request retains the original selection, generation
update, branch records and cleanup, including errors. Present cuts carry the
actual remove-all phase facts. With a selected resident device, every normal
return has such a cut and result zero. The shape/residency premises of those
phase facts concern the actual post-free device; no completion, final peer
erasure, free correctness, or mixed-attribute contract is asserted. -/
theorem original_replace_peers_phase_order (selector : DeviceRef) (d : Device) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let result ← observedReplacePeers selector; pure result.2)
      (liftWG (wgSetDevice (replacePeersAttrs selector))) ∧
    Campaign2.Product.Ensures (observedReplacePeers selector) (fun _ => True)
      (fun result _ => ∀ cut, result.1 = some cut → result.2 = 0 ∧ RemoveAllFacts cut) ∧
    Campaign2.Product.Ensures (observedReplacePeers (byIndex d))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s.toSnapshot d)
      (fun result _ => ∃ cut, result = (some cut, 0) ∧ RemoveAllFacts cut) := by
  refine ⟨?_, observedReplacePeers_facts selector, observedReplacePeers_selected d⟩
  intro entry _pre
  rw [observedReplacePeers_erase]


/-- With two distinct resident IPv4 nodes and no endpoint, the original peer
getter spends 168 bytes emitting its fixed attributes and first IP, then splits
at the second node. A second original call uses that returned context, spends
72 bytes, emits only public key and the second IP, and resets the allowed-IP
cursor/sequence. The original coalescer merges these actual fragments with the
supplied device attributes into one ordered two-IP peer. Data flags and DONE
are supplied too; other device peers are not traversed. The device stays
unchanged. Chunk capacities are explicit inputs; this proves no socket-level
chunk production, arbitrary pagination, or concurrent-change behavior. The
composition stops explicitly if its actual fragment kinds are unexpected. -/
theorem original_multipart_peer_readback (d : Device) (p : Peer) (a b : NodeId)
    (pid : PeerId) (addr₁ cidr₁ addr₂ cidr₂ : Nat) (parent₁ parent₂ : Slot)
    (ctx : DumpCtx) (firstSkb secondSkb : NlSkb)
    (resident : d.peers[pid]? = some p) (listed : p.allowedipsList = [a, b])
    (distinct : a ≠ b) (endpoint : p.endpoint = none)
    (firstNode : d.nodes[a]? = some { newNode addr₁ cidr₁ 32 (some pid) with parent := parent₁ })
    (secondNode : d.nodes[b]? = some { newNode addr₂ cidr₂ 32 (some pid) with parent := parent₂ })
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0)
    (firstRoom : firstSkb.room = 168) (secondRoom : 72 ≤ secondSkb.room) :
    Campaign2.Returns (multipartPeerDump pid d ctx firstSkb secondSkb)
      (fun s => s.wg.device = some d)
      (fun result s => s.wg.device = some d ∧ result =
        (({ firstSkb with room := 0 },
          { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
          .split (multipartFirst p addr₁ cidr₁)),
         ({ secondSkb with room := secondSkb.room - 72 },
          { ctx with nextAllowedip := none, allowedipsSeq := 0 },
          .complete (multipartLast p addr₂ cidr₂)),
         .ok (multipartJson d p addr₁ cidr₁ addr₂ cidr₂))) :=
  multipartPeerDump_returns d p a b pid addr₁ cidr₁ addr₂ cidr₂ parent₁ parent₂
    ctx firstSkb secondSkb resident listed distinct endpoint firstNode secondNode
    fresh sequence firstRoom secondRoom

/-- For any finite IPv4 list with at least two nodes and distinct first two
IDs, the original peer getter uses a 168-byte first chunk to emit fixed attrs
and one IP, then splits at the second node. A second original call uses that
actual returned context and enough supplied room to serialize the entire
remaining suffix, preserving its order and repetitions and clearing the cursor
and sequence. Node residency and width are explicit; no trie shape, ownership
or global list uniqueness is assumed. The coalescer consumes the actual two
fragments and returns the whole ordered IP list. Device attrs, flags and DONE
are supplied framing, not socket-generated messages. The device is unchanged.
This proves two-call peer serialization with caller-supplied capacities, not
outer socket pagination, traversal of other peers or concurrent modification. -/
theorem original_ipv4_suffix_readback (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (a b : NodeId) (tail : List NodeId) (pid : PeerId)
    (ctx : DumpCtx) (firstSkb secondSkb : NlSkb)
    (resident : d.peers[pid]? = some p) (listed : p.allowedipsList = a :: b :: tail)
    (distinct : a ≠ b) (endpoint : p.endpoint = none)
    (readable : Ipv4Residents d nodes (a :: b :: tail))
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0)
    (firstRoom : firstSkb.room = 168)
    (secondRoom : 44 + 28 * (1 + tail.length) ≤ secondSkb.room) :
    Campaign2.Returns (multipartPeerDump pid d ctx firstSkb secondSkb)
      (fun s => s.wg.device = some d)
      (fun result s => s.wg.device = some d ∧ result =
        (({ firstSkb with room := 0 },
          { ctx with nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq },
          .split (multipartFirst p (nodes a).bits (nodes a).cidr)),
         ({ secondSkb with room := secondSkb.room - (44 + 28 * (1 + tail.length)) },
          { ctx with nextAllowedip := none, allowedipsSeq := 0 },
          .complete (suffixLast p nodes (b :: tail))),
         .ok (suffixJson d p nodes (a :: b :: tail)))) :=
  suffixPeerDump_returns d p nodes a b tail pid ctx firstSkb secondSkb
    resident listed distinct endpoint readable fresh sequence firstRoom secondRoom

/-- The original socket getter selects one resident peer and serializes a
finite IPv4 list across two real 3776-byte chunks. The first callback fills
its prefix and suspends at b; the first receive runs the resumed callback,
which returns DATA, and the enclosing socket dump appends DONE and finalizes.
The second receive finishes the original
4096-iteration drain. Original coalescing checks the repeated device metadata
and continuation guards. The device is unchanged; the socket is empty and
idle, with cleared cursors, zero dump errno and the device generation.
Capacity and residency are explicit premises, not a reachable-state bound;
only b is excluded from the first prefix, with no global Nodup requirement. -/
theorem original_socket_multipart_readback (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (front : List NodeId) (b : NodeId) (tail : List NodeId)
    (sock : NlSock) (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = front ++ b :: tail) (nonempty : front ≠ [])
    (absent : b ∉ front) (readable : Ipv4Residents d nodes (front ++ b :: tail))
    (endpoint : p.endpoint = none)
    (firstFits : devicePrefixSpace d + 140 + 28 * front.length ≤ NLMSG_GOODSIZE)
    (firstFull : NLMSG_GOODSIZE < devicePrefixSpace d + 140 + 28 * (front.length + 1))
    (lastFits : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun q s => q = .ok (suffixJson d p nodes (front ++ b :: tail)) ∧
        s.wg.device = some d ∧ s.wg.nlSock7 = socketReadbackFinal sock d) :=
  socketReadback_returns pid d p nodes front b tail sock peers resident listed nonempty
    absent readable endpoint firstFits firstFull lastFits idle empty

/-- The original scalar setter updates one resident stopped-device peer, and
the original socket getter then reads back its new preshared key and keepalive
interval with its entire ordered IPv4 list across two actual socket chunks.
A later malformed peer makes the set return EINVAL but retains the earlier
update; readback still succeeds. The final device has one generation increment,
and the socket is empty and idle with cleared cursors and that generation.
The list, residency, absent endpoint and chunk capacities are explicit premises;
this is not general pagination, mixed-attribute configuration or reachability. -/
theorem original_scalar_socket_multipart_readback (d : Device) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (listed : p.allowedipsList = front ++ b :: tail) (nonempty : front ≠ [])
    (absent : b ∉ front) (readable : Ipv4Residents d nodes (front ++ b :: tail))
    (endpoint : p.endpoint = none)
    (firstFits : devicePrefixSpace d + 140 + 28 * front.length ≤ NLMSG_GOODSIZE)
    (firstFull : NLMSG_GOODSIZE < devicePrefixSpace d + 140 + 28 * (front.length + 1))
    (lastFits : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun w => w.wg.device = some d ∧ w.wg.nlSock7 = sock ∧ ClaimView.selectsDevice w d)
      (fun result w =>
        let updated := scalarRequestDevice d pid p psk interval
        let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        result = ((if bad then -EINVAL else 0),
          .ok (suffixJson updated configured nodes (front ++ b :: tail))) ∧
        w.wg.device = some updated ∧ w.wg.nlSock7 = socketReadbackFinal sock updated) :=
  scalarSocketReadback_returns d key psk interval bad pid p nodes front b tail sock peers found resident
    live bounded down listed nonempty absent readable endpoint firstFits firstFull lastFits idle empty


/-- The actual mixed fwmark/peer-scalar setter followed by the getter reads
back the model's exact JSON and retains endpoint-source/cache clearing.
A malformed second peer returns EINVAL after the earlier writes. The finite
single-peer, stopped-device getter domain is explicit; reset-record readiness
is not assumed, and an actual prefix Stop prevents the getter. -/
theorem original_mixed_fwmark_scalar_get_after_set (d : Device) (mark : Nat) (key psk : Key)
    (interval : Nat) (bad : Bool) (pid : PeerId) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (noIps : p.allowedipsList = [])
    (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0), .ok
          (singlePeerJson (mixedFwmarkBase d mark)
            {p with presharedKey := psk, persistentKeepaliveInterval := interval})) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ current reset, s.wg.device = some current ∧
          MixedFwmarkEffect d mark pid p psk interval reset current) :=
  mixed_fwmark_scalar_get_after_set d mark key psk interval bad pid p sock
    peers net found resident live bounded down noIps room idle empty

/-- Actual set/readback for a resident peer on a stopped device. Allocation refusal and a
malformed second Allowed-IP retain earlier writes; only full success reaches
the keepalive assignment. The JSON uses the mirror's exact address masking. -/
theorem original_mixed_peer_allowedip_get_after_set (v4 : Bool) (key psk : Key)
    (interval addr cidr : Nat) (bad : Bool) (d : Device) (pid : PeerId) (p : Peer)
    (ctx : DumpCtx) (skb : NlSkb)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (empty : p.allowedipsList = []) (root : allowedRootValue v4 d = none)
    (width : cidr ≤ allowedBits v4) (fresh : ctx.nextAllowedip = none)
    (sequence : ctx.allowedipsSeq = 0 ∨ ctx.allowedipsSeq = d.peerAllowedips.seq + 1)
    (room : 172 + allowedIpSpace (allowedFamily v4) ≤ skb.room) :
    Campaign2.Ensures (do
      let ret ← setPeerCmd (mixedPeerAttrs v4 key psk interval addr cidr bad)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun s => s.wg.device = some d)
      (fun result s => ∃ inserted final,
        s.wg.device = some final ∧
        MixedPeerEffect v4 d pid p psk interval addr cidr bad result.1 final ∧
        result.1 = (if inserted then (if bad then -EINVAL else 0) else -ENOMEM) ∧
        result.2 =
          ({skb with room := skb.room - (peerFixedSpace p +
              (if inserted then 4 + allowedIpSpace (allowedFamily v4) else 0))},
           {ctx with nextAllowedip := none, allowedipsSeq := 0},
           .complete {
             publicKey := hexKey p.remoteStatic
             attrs := peerFixedAttrs (mixedPeerReadback p psk interval d.nextNode bad inserted) ++
               (if inserted then [("allowed_ips", Lean.Json.arr #[allowedJson v4 addr cidr])] else [])})) :=
  mixed_peer_allowedip_get_after_set v4 key psk interval addr cidr bad d pid p ctx skb
    found resident live bounded down empty root width fresh sequence room

/-- A normal mixed request that reaches a nonzero port collision retains its
earlier mark/generation and source-cache writes, while all later attributes are
bypassed. No reset-record or listed-peer readiness is assumed. -/
theorem original_mixed_port_refusal (d : Device) (mark port : Nat)
    (flags : Option UInt32) (key : Option Key) (peers : Option (List PeerEntry))
    (bound : Nat → Bool) (supported : flags.getD 0 &&& ~~~WGDEVICE_F_ALL = 0)
    (net : d.creatingNet = true) (running : d.running = true)
    (nonzero : port ≠ 0) (changed : d.incomingPort ≠ port)
    (collision : (bound port || d.sock4 == some port || d.sock6 == some port) = true) :
    Campaign2.Ensures (wgSetDevice (portRefusalAttrs d mark port flags key peers))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧ s.wg.portBound = bound)
      (fun ret s => ret = -EADDRINUSE ∧
        s.wg.device.map withoutPeers = some (withoutPeers (portRefusalBase d mark)) ∧
        ClaimView.clearedPeers d s.wg.toCore d.peerList) :=
  mixed_port_refusal d mark port flags key peers bound supported net running nonzero changed collision

/-- The actual getter observes the retained prefix of a failed mixed request.
This finite dump domain allows a running device and arbitrary later attributes;
hidden reset Stops prevent the sequence rather than becoming normal refusals.
The equality concerns the mirror's JSON, not byte-level attribute encoding. -/
theorem original_mixed_port_refusal_get_after_set (d : Device) (mark port : Nat)
    (flags : Option UInt32) (key : Option Key) (peers : Option (List PeerEntry))
    (bound : Nat → Bool) (pid : PeerId) (p : Peer) (sock : NlSock)
    (supported : flags.getD 0 &&& ~~~WGDEVICE_F_ALL = 0)
    (net : d.creatingNet = true) (running : d.running = true)
    (nonzero : port ≠ 0) (changed : d.incomingPort ≠ port)
    (collision : (bound port || d.sock4 == some port || d.sock6 == some port) = true)
    (members : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (noIps : p.allowedipsList = [])
    (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (portRefusalAttrs d mark port flags key peers)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.portBound = bound ∧ s.wg.nlSock7 = sock)
      (fun result s =>
        result = (-EADDRINUSE, .ok (singlePeerJson (portRefusalBase d mark) p)) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        s.wg.device.map withoutPeers = some (withoutPeers (portRefusalBase d mark)) ∧
        ClaimView.clearedPeers d s.wg.toCore d.peerList) :=
  mixed_port_refusal_get_after_set d mark port flags key peers bound pid p sock
    supported net running nonzero changed collision members resident noIps room idle empty

/-- Full setter/getter on the actual established-identity, no-collision path.
The supplied key is read back through effective identityAfter/clamping and the
model's JSON convention; a null key removes the serialized identity fields.
No missing-clock, NULL-owner or missing-keypair failure is assumed away. -/
theorem original_private_key_rotation_get_after_set (d : Device) (key : Key) (pid : PeerId) (p : Peer) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (members : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (noIps : p.allowedipsList = [])
    (room : devicePrefixSpace (keyReadbackBase d key) + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0, .ok (singlePeerJson (keyReadbackBase d key) p)) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ now, s.wg.device = some (keyReadbackDevice d key pid p now)) :=
  rotation_get_after_set d key pid p sock established changed absent members resident noIps room idle empty

/-- The original getter drains any finite IPv4 allowed-IP list for one peer
through its actual fixed-capacity callbacks and receives, then coalesces every
occurrence in order. Cursor freshness is required only at canonical chunk
boundaries; the exact receive bound includes a separate DONE envelope when
needed. This is not a global ownership invariant or multi-peer pagination. -/
theorem original_finite_ipv4_pagination (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids) (fresh : ipv4PaginationFresh d ids)
    (readable : Ipv4Residents d nodes ids) (endpoint : p.endpoint = none)
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (enough : ipv4PaginationReceiveCount d ids ≤ 4096) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (suffixJson d p nodes ids) ∧
        s.wg.device = some d ∧ s.wg.nlSock7 = socketReadbackFinal sock d) :=
  ipv4Pagination_returns pid d p nodes ids sock peers resident listed fresh readable endpoint
    room idle empty enough

/-- The actual mixed fwmark/scalar request followed by the original finite
IPv4 paginating getter. A malformed second peer still returns EINVAL after
committing the mark and selected peer's scalar fields. Every reset-record Stop
remains a Stop; the reset timestamp is derived only from a normal setter run.
No callback-success, cache-reset or reference-readiness premise is added. -/
theorem original_mixed_fwmark_scalar_pagination_get_after_set (d : Device) (mark : Nat) (key psk : Key)
    (interval : Nat) (bad : Bool) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (listed : p.allowedipsList = ids) (fresh : ipv4PaginationFresh d ids)
    (readable : Ipv4Residents d nodes ids) (endpoint : p.endpoint = none)
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (enough : ipv4PaginationReceiveCount d ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0), .ok
          (suffixJson (mixedFwmarkBase d mark)
            {p with presharedKey := psk, persistentKeepaliveInterval := interval} nodes ids)) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ current reset, s.wg.device = some current ∧
          MixedFwmarkEffect d mark pid p psk interval reset current) :=
  mixed_fwmark_scalar_pagination_get_after_set d mark key psk interval bad pid p nodes ids sock
    peers net found resident live bounded down listed fresh readable endpoint room enough idle empty

/-- The actual private-key request and getter return every finite IPv4
allowed-IP occurrence in order, with capacities measured after the effective
identity update. The exact normal final Device contains the actual expiry time;
this does not assert totality of key installation or global list ownership. -/
theorem original_private_key_rotation_pagination_get_after_set (d : Device) (key : Key) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (members : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (fresh : ipv4PaginationFresh (keyReadbackBase d key) ids)
    (readable : Ipv4Residents d nodes ids) (endpoint : p.endpoint = none)
    (room : devicePrefixSpace (keyReadbackBase d key) + 168 ≤ NLMSG_GOODSIZE)
    (enough : ipv4PaginationReceiveCount (keyReadbackBase d key) ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0, .ok (suffixJson (keyReadbackBase d key) p nodes ids)) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ now, s.wg.device = some (keyReadbackDevice d key pid p now)) :=
  rotation_pagination_get_after_set d key pid p nodes ids sock established changed absent
    members resident listed fresh readable endpoint room enough idle empty

/-- Every occurrence in the finite peer list is returned by the original
getter in order, with actual endpoint attributes and empty allowed_ips. The
conservative capacity includes all peers and DONE in one envelope. The whole
Device is retained, including for an empty list or repeated peer identifiers;
this does not claim multi-peer pagination or global owner/list consistency. -/
theorem original_fitting_multi_peer_getter (d : Device) (peers : PeerId → Peer) (sock : NlSock)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (emptyIps : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (room : devicePrefixSpace d + 168 * d.peerList.length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (multiPeerJson d peers) ∧ s.wg.device = some d ∧
        s.wg.nlSock7 = socketReadbackFinal sock d) :=
  fitting_peers_getter_returns d peers sock residents emptyIps room idle emptyQueue

/-- The actual getter returns the fitting peer list in order, reflecting the
scalar update at each occurrence of the selected peer, even when a malformed
second request returns -EINVAL. An unlisted target still changes in the exact
Device but is absent from the JSON. Empty/repeated lists and arbitrary endpoints
remain admitted; this is not a fwmark or multi-peer pagination claim. -/
theorem original_scalar_fitting_multi_peer_get_after_set (d : Device) (peers : PeerId → Peer)
    (key psk : Key) (interval : Nat) (bad : Bool) (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount + 1 < 2 ^ 31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = [])
    (room : devicePrefixSpace d + 168 * d.peerList.length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        let updated := scalarRequestDevice d pid (peers pid) psk interval
        result = ((if bad then -EINVAL else 0),.ok
          (multiPeerJson updated (scalarPeerView peers pid psk interval))) ∧
        s.wg.device = some updated ∧ s.wg.nlSock7 = socketReadbackFinal sock updated) :=
  scalar_fitting_peers_get_after_set d peers key psk interval bad pid sock
    found resident live bounded down residents emptyIps room idle emptyQueue

/-- One actual mixed fwmark/scalar request followed by the original getter
for an arbitrary fitting finite peer list. Duplicate visits and arbitrary
endpoints remain visible; the selected peer may be absent from the dump list.
A malformed second peer returns -EINVAL after retaining the earlier writes.
Reset-record Stops remain Stops; no cache-reset readiness is assumed. This does
not establish multi-peer pagination or global Allowed-IP ownership. -/
theorem original_multi_peer_fwmark_scalars_get_after_set (d : Device) (peers : PeerId → Peer)
    (mark : Nat) (key psk : Key) (interval : Nat) (bad : Bool) (pid : PeerId) (sock : NlSock)
    (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount + 1 < 2 ^ 31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = [])
    (room : devicePrefixSpace d + 168 * d.peerList.length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0),.ok
          (multiPeerJson (mixedFwmarkBase d mark) (scalarPeerView peers pid psk interval))) ∧
        s.wg.nlSock7 = {sock with queue := [],ctx := {hasWg := true},prevSeq := d.deviceUpdateGen + 1,dumpDoneErrno := 0,cbRunning := false} ∧
        ∃ current, s.wg.device = some current ∧ MultiMixedEffect d mark pid psk interval current) :=
  multi_mixed_fitting_get_after_set d peers mark key psk interval bad pid sock net
    found resident live bounded down residents emptyIps room idle emptyQueue

/-- The actual getter serializes every finite IPv4 allowed-IP occurrence and
the endpoint JSON produced by the original getter, with canonical boundary
freshness and a receive count including separate DONE envelopes. Repeated
non-boundary IDs remain allowed; endpoint serialization follows peerFixedAttrs. This is a single-peer getter claim; it makes
no global owner/list consistency or mixed-family packing claim. -/
theorem original_endpoint_ipv4_pagination (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids) (fresh : endpointPaginationFresh d p ids)
    (readable : Ipv4Residents d nodes ids)
    (room : devicePrefixSpace d + max 168 (peerFixedSpace p + 32) ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (enough : endpointPaginationReceiveCount d p ids ≤ 4096) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (suffixJson d p nodes ids) ∧
        s.wg.device = some d ∧ s.wg.nlSock7 = socketReadbackFinal sock d) :=
  endpointIpv4Pagination_returns pid d p nodes ids sock peers resident listed fresh readable room idle empty enough
/-- The actual mixed fwmark/scalar setter followed by the finite IPv4 getter
with arbitrary endpoint values under the endpoint-aware capacity and cursor
bounds. Readback uses the actual endpoint serializer; the Device retains
source clearing and cache invalidation, and a later malformed peer retains the
earlier writes. Hidden reset failures remain outside this normal-return claim. -/
theorem original_mixed_fwmark_scalars_endpoint_pagination (d : Device) (mark : Nat) (key psk : Key)
    (interval : Nat) (bad : Bool) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (listed : p.allowedipsList = ids) (fresh : endpointPaginationFresh d p ids)
    (readable : Ipv4Residents d nodes ids)
    (room : devicePrefixSpace d + max 168 (peerFixedSpace p + 32) ≤ NLMSG_GOODSIZE)
    (enough : endpointPaginationReceiveCount d p ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0), .ok
          (suffixJson (mixedFwmarkBase d mark)
            {p with presharedKey := psk, persistentKeepaliveInterval := interval} nodes ids)) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ current reset, s.wg.device = some current ∧
          MixedFwmarkEffect d mark pid p psk interval reset current) :=
  mixed_fwmark_scalar_endpoint_pagination_get_after_set d mark key psk interval bad pid p nodes ids sock peers net found resident live bounded down listed fresh readable room enough idle empty

/-- The actual established-identity setter followed by finite IPv4 pagination
with arbitrary endpoint values. Capacities and JSON use the effective installed
identity, including clamping and null-key behavior. The actual expiry effect and
socket completion are retained; clock/reference failures are not assumed away. -/
theorem original_private_key_endpoint_pagination (d : Device) (key : Key) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (members : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (fresh : endpointPaginationFresh (keyReadbackBase d key) p ids)
    (readable : Ipv4Residents d nodes ids)
    (room : devicePrefixSpace (keyReadbackBase d key) + max 168 (peerFixedSpace p + 32) ≤ NLMSG_GOODSIZE)
    (enough : endpointPaginationReceiveCount (keyReadbackBase d key) p ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0, .ok (suffixJson (keyReadbackBase d key) p nodes ids)) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ now, s.wg.device = some (keyReadbackDevice d key pid p now)) :=
  rotation_endpoint_pagination_get_after_set d key pid p nodes ids sock established changed absent members resident listed fresh readable room enough idle empty


/-- The whole original getter terminates with exact JSON and an empty,
completed socket for a resident singleton listed peer and finite readable
mixed-width allowed-IP list. Greedy 28/40-byte pages preserve all occurrences;
every resumed cursor is fresh against all prior emissions. Empty input and an
empty first fitting prefix take their distinct original branches. The exact
DATA-plus-DONE-spill count must fit 4096 receives. Endpoints and stored-width
mask/hex serialization are unchanged; no valid-IPv6 or global ownership
claim is inferred from an arbitrary stored width. -/
theorem original_finite_mixed_width_pagination (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace p+4) ≤ NLMSG_GOODSIZE)
    (fresh : weightedGetterFresh d p nodes ids)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (within : weightedGetterReceives d p nodes ids ≤ 4096) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (jsonPaginationResult d p
        (ids.map (fun id => dumpNodeJson (nodes id)))) ∧ s.wg.device = some d ∧
        s.wg.nlSock7 = socketReadbackFinal sock d) :=
  mixed_weighted_getter pid d p nodes ids sock peers resident listed readable header nest fresh idle empty within

/-- Actual mixed fwmark/scalar set followed by the whole weighted getter on
normal completion. A malformed later peer retains the earlier writes and
returns -EINVAL. The Device includes actual source/cache clearing; JSON uses
original endpoint and stored-width serializers. Freshness covers all prior
emissions and the bound includes a separate DONE when required. Reset-record
Stops remain outside this normal-return contract; no success witness is assumed. -/
theorem original_mixed_fwmark_scalars_weighted_pagination (d : Device) (mark : Nat) (key psk : Key)
    (interval : Nat) (bad : Bool) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (listed : p.allowedipsList = ids) (fresh : weightedGetterFresh d p nodes ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace p + 4) ≤ NLMSG_GOODSIZE)
    (enough : weightedGetterReceives d p nodes ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0), .ok
          (jsonPaginationResult (mixedFwmarkBase d mark)
            {p with presharedKey := psk, persistentKeepaliveInterval := interval}
            (ids.map (fun id => dumpNodeJson (nodes id))))) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ current reset, s.wg.device = some current ∧
          MixedFwmarkEffect d mark pid p psk interval reset current) :=
  mixed_fwmark_scalar_weighted_pagination_get_after_set d mark key psk interval bad pid p nodes ids sock
    peers net found resident live bounded down listed fresh readable header nest enough idle empty

/-- Actual established-identity private-key set followed by the whole weighted
getter on normal completion. Size, freshness, count and JSON are based on the
effective post-key identity, including null-key behavior. Actual expiry and
ordered key effects remain in the final Device; clock/reference Stops are
retained. Arbitrary endpoints and stored widths use original serialization,
without inferring valid IPv6 or global allowed-IP ownership. -/
theorem original_private_key_weighted_pagination (d : Device) (key : Key) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (members : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (fresh : weightedGetterFresh (keyReadbackBase d key) p nodes ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace (keyReadbackBase d key) + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace (keyReadbackBase d key) + (peerFixedSpace p + 4) ≤ NLMSG_GOODSIZE)
    (enough : weightedGetterReceives (keyReadbackBase d key) p nodes ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0, .ok (jsonPaginationResult (keyReadbackBase d key) p (ids.map (fun id => dumpNodeJson (nodes id))))) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ now, s.wg.device = some (keyReadbackDevice d key pid p now)) :=
  rotation_weighted_pagination_get_after_set d key pid p nodes ids sock established changed absent
    members resident listed fresh readable header nest enough idle empty

/-- Exact normal effects of the original peer endpoint request, including
existing-peer UPDATE_ONLY, ignored invalid encodings, equality/no-write and
balanced reference stores. This does not assert reset-record availability. -/
theorem original_peer_endpoint_set (key : Key) (a : EndpointAttr) (updateOnly : Bool)
    (pid : PeerId) (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Campaign2.Ensures (setPeerCmd (endpointPeerAttrs key a updateOnly))
      (fun s => s.wg.device = some d)
      (fun ret s => ret = 0 ∧ ∃ reset, s.wg.device = some (endpointSetterDevice d pid p a reset)) := by
  intro entry ambient ret final after pre run
  obtain ⟨code, reset, device, _⟩ := setPeer_endpoint_down key a updateOnly pid d p found
    resident live bounded down entry.nlSock7 entry.fixtureNetDevices entry ambient ret final after
    ⟨pre, rfl, rfl⟩ run
  exact ⟨code, reset, device⟩

/-- Normal original device set/get composition. Effective endpoint equality
preserves old flowinfo; malformed later-peer rejection retains preceding writes.
The getter uses the effective post-set endpoint's weighted capacities. -/
theorem original_endpoint_weighted_get_after_set (d : Device) (key : Key) (a : EndpointAttr)
    (updateOnly bad : Bool) (pid : PeerId) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid])
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount)
    (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace (endpointApplied p a) + 4) ≤ NLMSG_GOODSIZE)
    (fresh : weightedGetterFresh d (endpointApplied p a) nodes ids)
    (within : weightedGetterReceives d (endpointApplied p a) nodes ids ≤ 4096)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (endpointDeviceAttrs d key a updateOnly bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0), .ok (jsonPaginationResult d (endpointApplied p a)
          (ids.map (fun id => dumpNodeJson (nodes id))))) ∧
        s.wg.nlSock7 = {sock with queue := [], ctx := {hasWg := true}, prevSeq := d.deviceUpdateGen + 1, dumpDoneErrno := 0, cbRunning := false} ∧
        ∃ reset, s.wg.device = some
          (endpointSetterDevice {d with deviceUpdateGen := d.deviceUpdateGen + 1} pid p a reset)) :=
  endpoint_weighted_get_after_set d key a updateOnly bad pid p nodes ids sock peers found resident live bounded down listed readable header nest fresh within idle empty


/-- Original resident-peer serialization with no stored allowed-IP entries,
for every initial room. Exact capacity gives the original fixed attributes and
residual room; shortage cancels to the original skb and context. Only the
allowed-IP cursor and sequence reset on completion. -/
theorem original_peer_dump_fixed_room (pid : PeerId) (d : Device) (p : Peer)
    (ctx : DumpCtx) (skb : NlSkb) (resident : d.peers[pid]? = some p)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = []) :
    Campaign2.Returns (getPeerDump pid ctx skb) (fun s => s.wg.device = some d)
      (fun result s => s.wg.device = some d ∧ result = fixedPeerResult p ctx skb) :=
  getPeerDump_fixed_room pid d p ctx skb resident fresh empty

/-- One original normal callback: exact completed prefix and ordered cursor references.
No initial capacity, reference bound, live flag, cursor membership or sequence
consistency is assumed. Last-reference Stops remain outside normal completion. -/
theorem original_cursor_callback_normal (d : Device) (peers : PeerId → Peer) (ctx : DumpCtx)
    (prev : Nat) (skb : NlSkb)
    (residents : ∀ pid ∈ cursorSelected d ctx, d.peers[pid]? = some (peers pid))
    (empty : ∀ pid ∈ cursorSelected d ctx, (peers pid).allowedipsList = [])
    (fresh : ctx.nextAllowedip = none)
    (oldResident : ∀ pid, ctx.nextPeer = some pid → ∃ p, d.peers[pid]? = some p) :
    let header := cursorHeaderSkb d ctx skb
    let state := cursorBodyState d peers ctx {header with room := header.room-4}
    Campaign2.Ensures (wgGetDeviceDump ctx prev skb) (fun s => s.wg.device = some d)
      (fun result s => result = cursorCallResult d (2 + if prev != 0 && prev != d.deviceUpdateGen then 16 else 0)
          (if ctx.nextPeer.isNone then deviceFixedAttrs d else [])
          state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2 ∧
        s.wg.device = some (cursorReleased (cursorAcquired d (if state.2.2.2.1 then none else state.2.1)) state.1.nextPeer)) :=
  wgGetDeviceDump_cursor_normal d peers ctx prev skb residents empty fresh oldResident

/-- The original getter coalesces two complete-peer DATA pages into canonical
JSON, with actual endpoint serialization and inline or separate DONE. Only the boundary
cursor needs liveness and reference bounds; later repeated peer IDs remain
allowed. The exact final Device records acquisition followed by release, while
its peer lookups and all other Device fields agree with the entry Device. -/
theorem original_two_page_empty_ips_getter (d : Device) (peers : PeerId → Peer) (sock : NlSock)
    (before : List PeerId) (cursor next : PeerId) (tail : List PeerId)
    (members : d.peerList = (before ++ [cursor]) ++ next :: tail)
    (fresh : cursor ∉ before)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (emptyIps : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (live : (peers cursor).isDead = false)
    (positive : 0 < (peers cursor).refcount) (bounded : (peers cursor).refcount+1 < 2^31)
    (firstFits : devicePrefixSpace d + multiPeerSpace peers (before ++ [cursor]) ≤ NLMSG_GOODSIZE)
    (firstFull : NLMSG_GOODSIZE < devicePrefixSpace d + multiPeerSpace peers (before ++ [cursor]) + peerFixedSpace (peers next))
    (lastFits : 24 + multiPeerSpace peers (next::tail) ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (multiPeerJson d peers) ∧
        s.wg.device = some (cursorReleased (cursorAcquired d (some cursor)) (some cursor)) ∧
        s.wg.nlSock7 = socketReadbackFinal sock d) :=
  two_pages_getter_returns d peers sock before cursor next tail members fresh residents emptyIps
    live positive bounded firstFits firstFull lastFits idle emptyQueue

/-- The original finite empty-IP peer getter, with every callback and receive
derived from its canonical plan and actual boundary data. -/
theorem original_finite_empty_ips_getter (d : Device) (peers : PeerId → Peer) (sock : NlSock)
    (residents : ∀ id ∈ d.peerList, d.peers[id]? = some (peers id))
    (empty : ∀ id ∈ d.peerList, (peers id).allowedipsList = [])
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (firstFits : ∀ id rest, d.peerList = id :: rest →
      peerFixedSpace (peers id) ≤ NLMSG_GOODSIZE-devicePrefixSpace d)
    (fresh : peerPageBoundaryFresh [] (peerPages peers d d.peerList))
    (cursorData : PeerPageCursorData peers (peerPages peers d d.peerList))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
    (within : peerPageReceiveCount peers d d.peerList ≤ 4096) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (multiPeerJson d peers) ∧
        s.wg.device = some (peerGetterFinalDevice d peers) ∧
        s.wg.nlSock7 = socketReadbackFinal sock d ∧
        CursorHeld d (peerGetterFinalDevice d peers) none) := by
  exact peer_getter_returns d peers sock residents empty headerFits firstFits fresh cursorData idle emptyQueue within

/-- Actual scalar set/get across the canonical finite empty-IP peer pages.
A malformed second peer retains the first peer writes and returns -EINVAL.
The ordered getter cursor handoffs produce the stated final Device; boundary
freshness and cursor lifetime premises concern the effective post-set plan.
Empty/repeated lists and arbitrary endpoints are admitted subject to those
explicit plan conditions and the actual getter loop budget. -/
theorem original_scalar_paginated_multi_peer_get_after_set (d : Device) (peers : PeerId → Peer)
    (key psk : Key) (interval : Nat) (bad : Bool) (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount + 1 < 2 ^ 31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = [])
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let updated := scalarRequestDevice d pid (peers pid) psk interval
    let configured := scalarPeerView peers pid psk interval
    devicePrefixSpace updated ≤ NLMSG_GOODSIZE →
    (∀ q rest, updated.peerList = q :: rest →
      peerFixedSpace (configured q) ≤ NLMSG_GOODSIZE-devicePrefixSpace updated) →
    peerPageBoundaryFresh [] (peerPages configured updated updated.peerList) →
    PeerPageCursorData configured (peerPages configured updated updated.peerList) →
    peerPageReceiveCount configured updated updated.peerList ≤ 4096 →
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0),.ok (multiPeerJson updated configured)) ∧
        s.wg.device = some (peerGetterFinalDevice updated configured) ∧
        s.wg.nlSock7 = socketReadbackFinal sock updated ∧
        CursorHeld updated (peerGetterFinalDevice updated configured) none) :=
  scalar_paginated_peers_get_after_set d peers key psk interval bad pid sock
    found resident live bounded down residents emptyIps idle emptyQueue

/-- Actual fwmark and selected-peer scalar writes followed by complete finite
empty-IP peer pagination. Every list occurrence is returned in order, including
duplicates and arbitrary endpoint serialization; an unlisted target is changed
only in the Device. Hidden reset Stops and earlier writes before later EINVAL
remain. The setter successor and the getter's ordered cursor writes are distinct;
no raw peer-map equality, callback success or readiness premise is supplied. -/
theorem original_mixed_peer_pages_get_after_set (d : Device) (peers : PeerId → Peer)
    (mark : Nat) (key psk : Key) (interval : Nat) (bad : Bool) (pid : PeerId) (sock : NlSock)
    (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount + 1 < 2 ^ 31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = [])
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (firstFits : ∀ q rest, d.peerList = q :: rest →
      peerFixedSpace (peers q) ≤ NLMSG_GOODSIZE-devicePrefixSpace d)
    (fresh : peerPageBoundaryFresh [] (peerPages peers d d.peerList))
    (cursorData : PeerPageCursorData peers (peerPages peers d d.peerList))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
    (within : peerPageReceiveCount peers d d.peerList ≤ 4096) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        result = ((if bad then -EINVAL else 0),.ok
          (multiPeerJson (mixedFwmarkBase d mark) (scalarPeerView peers pid psk interval))) ∧
        s.wg.nlSock7 = {sock with queue := [],ctx := {hasWg := true},prevSeq := d.deviceUpdateGen + 1,dumpDoneErrno := 0,cbRunning := false} ∧
        ∃ postSet values, MultiMixedEffect d mark pid psk interval postSet ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          s.wg.device = some (peerGetterFinalDevice postSet values) ∧
          CursorHeld postSet (peerGetterFinalDevice postSet values) none) := by
  exact multi_mixed_pages_get_after_set d peers mark key psk interval bad pid sock net
    found resident live bounded down residents emptyIps headerFits firstFits fresh cursorData
    idle emptyQueue within

/-- Actual private-key rotation then canonical finite empty-IP peer readback.
The established-identity path keeps the effective clamped/null identity,
ordered expiry effects and all source Stops. On normal return the getter
reflects every peer occurrence and ends at its exact cursor-handoff Device;
installation effects describe the actual intermediate Device, not the final
raw peer map. Only computed nonfinal cursors need the stated lifetime data. -/
theorem original_key_paginated_multi_peer_get_after_set (d : Device) (peers : PeerId → Peer)
    (key : Key) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = [])
    (headerFits : devicePrefixSpace (keyReadbackBase d key) ≤ NLMSG_GOODSIZE)
    (firstFits : ∀ q rest, d.peerList = q :: rest →
      peerFixedSpace (peers q) ≤ NLMSG_GOODSIZE-devicePrefixSpace (keyReadbackBase d key))
    (fresh : peerPageBoundaryFresh [] (peerPages peers (keyReadbackBase d key) d.peerList))
    (cursorData : PeerPageCursorData peers (peerPages peers (keyReadbackBase d key) d.peerList))
    (within : peerPageReceiveCount peers (keyReadbackBase d key) d.peerList ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0,.ok (multiPeerJson (keyReadbackBase d key) peers)) ∧
        ∃ postSet observations values,
          ObservedKeyPeerRun false (keyReadbackBase d key) d.peerList observations postSet ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (peerGetterFinalDevice postSet values) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (peerGetterFinalDevice postSet values) none) :=
  key_paginated_peers_get_after_set d peers key sock established changed absent
    residents emptyIps headerFits firstFits fresh cursorData within idle emptyQueue

/-- Complete original finite peer/allowed-IP getter under computed static
boundary, capacity and lifetime conditions; all execution is derived. -/
theorem original_finite_mixed_getter (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (sock : NlSock)
    (ready : MixedPageReady d peers nodes (mixedInitialRows d peers) {hasWg := true})
    (residents : ∀ id ∈ d.peerList, d.peers[id]? = some (peers id))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList,
      d.nodes[id]? = some (nodes id))
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh d peers
      (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready))
    (cursorData : MixedPlanCursorData d
      (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
    (within : mixedPageReceiveCount
      (mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready) ≤ 4096) :
    let pages := mixedPages d peers nodes (mixedInitialRows d peers) {hasWg := true} ready
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (mixedGetterJson d peers nodes) ∧
        s.wg.device = some (mixedPagesDevice d pages) ∧
        s.wg.nlSock7 = socketReadbackFinal sock d ∧
        CursorHeld d (mixedPagesDevice d pages) none) :=
  mixed_getter_returns d peers nodes sock ready residents readable headerFits
    fresh cursorData idle emptyQueue within

/-- Actual existing-peer scalar setter followed by the complete finite mixed
peer/allowed-IP getter, including retained first-peer writes before later EINVAL.
The native getter returns every original occurrence and stored-width/endpoint
serialization under the computed successor's static progress, boundary freshness,
cursor-reference and finite receive-budget conditions. The exact final Device
retains ordered cursor handoffs; no callback-success premise is supplied. -/
theorem original_scalar_mixed_pagination_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (key psk : Key) (interval : Nat) (bad : Bool)
    (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount+1 < 2^31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList, d.nodes[id]? = some (nodes id))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let updated := scalarRequestDevice d pid (peers pid) psk interval
    let configured := scalarPeerView peers pid psk interval
    ∀ ready : MixedPageReady updated configured nodes (mixedInitialRows updated configured) {hasWg := true},
    devicePrefixSpace updated ≤ NLMSG_GOODSIZE →
    MixedPlanFresh updated configured
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    MixedPlanCursorData updated
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    mixedPageReceiveCount
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) ≤ 4096 →
    Campaign2.Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        let pages := mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready
        result = ((if bad then -EINVAL else 0),.ok (mixedGetterJson updated configured nodes)) ∧
        s.wg.device = some (mixedPagesDevice updated pages) ∧
        s.wg.nlSock7 = socketReadbackFinal sock updated ∧
        CursorHeld updated (mixedPagesDevice updated pages) none) :=
  scalar_mixed_get_after_set d peers nodes key psk interval bad pid sock
    found resident live bounded down residents readable idle emptyQueue

/-- On normal return, actual changed-key installation followed by full finite
mixed peer/allowed-IP readback exposes the effective installed identity and
ordered peer/node serialization. Actual expiry observations and final cursor
handoffs remain explicit; no global ownership or initialized-history claim. -/
theorem original_key_mixed_get_after_set (d : Device) (peers : PeerId → Peer) (nodes : NodeId → AipNode)
    (key : Key) (sock : NlSock)
    (established : d.staticIdentity.hasIdentity = true)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (keyReadbackBase d key) peers nodes
      (mixedInitialRows (keyReadbackBase d key) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (keyReadbackBase d key) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (keyReadbackBase d key) peers
      (mixedPages (keyReadbackBase d key) peers nodes (mixedInitialRows (keyReadbackBase d key) peers)
        {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (keyReadbackBase d key)
      (mixedPages (keyReadbackBase d key) peers nodes (mixedInitialRows (keyReadbackBase d key) peers)
        {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (keyReadbackBase d key) peers nodes (mixedInitialRows (keyReadbackBase d key) peers)
        {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let pages := mixedPages (keyReadbackBase d key) peers nodes
      (mixedInitialRows (keyReadbackBase d key) peers) {hasWg := true} ready
    Campaign2.Ensures (do
      let ret ← wgSetDevice (privateKeyAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = (0,.ok (mixedGetterJson (keyReadbackBase d key) peers nodes)) ∧
        ∃ postSet observations, ∃ values : PeerId → Peer,
          ObservedKeyPeerRun false (keyReadbackBase d key) d.peerList observations postSet ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) :=
  key_mixed_get_after_set d peers nodes key sock established changed absent residents readable ready headerFits fresh cursorData within idle emptyQueue

/-- Actual endpoint configuration followed by the complete finite mixed getter.
Static page premises use the pure successor with no reset timestamp; any actual
reset preserves those inputs. Earlier writes before later EINVAL, ignored endpoint
encodings, equality-retained fields and record-driven Stops remain unchanged. -/
theorem original_endpoint_mixed_pagination_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (key : Key) (a : EndpointAttr)
    (updateOnly bad : Bool) (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount+1 < 2^31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList, d.nodes[id]? = some (nodes id))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let base := {d with deviceUpdateGen := d.deviceUpdateGen+1}
    let updated := endpointSetterDevice base pid (peers pid) a none
    let configured := fun q => if q = pid then endpointAttributePeer (peers q) a none else peers q
    ∀ ready : MixedPageReady updated configured nodes (mixedInitialRows updated configured) {hasWg := true},
    devicePrefixSpace updated ≤ NLMSG_GOODSIZE →
    MixedPlanFresh updated configured
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    MixedPlanCursorData updated
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    mixedPageReceiveCount
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) ≤ 4096 →
    Campaign2.Ensures (do
      let ret ← wgSetDevice (endpointDeviceAttrs d key a updateOnly bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        let pages := mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready
        result = ((if bad then -EINVAL else 0),.ok (mixedGetterJson updated configured nodes)) ∧
        ∃ reset, let postSet := endpointSetterDevice base pid (peers pid) a reset
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) :=
  endpoint_mixed_get_after_set d peers nodes key a updateOnly bad pid sock
    found resident live bounded down residents readable idle emptyQueue

/-- Actual fwmark/source reset and scalar setter followed by the full finite
mixed peer/allowed-IP getter. Normal returns retain earlier mutations before
later EINVAL; hidden reset Stops remain outside this partial contract. Static
plan conditions concern the explicit configured successor. The final Device
is the ordered cursor handoff fold over the same actual setter successor,
which retains MultiMixedEffect; no callback-success premise is assumed. -/
theorem original_fwmark_scalar_mixed_pagination_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (mark : Nat) (key psk : Key) (interval : Nat)
    (bad : Bool) (pid : PeerId) (sock : NlSock)
    (net : d.creatingNet = true)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid))
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount+1 < 2^31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList, d.nodes[id]? = some (nodes id))
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let updated := scalarRequestDevice {d with fwmark := mark} pid (peers pid) psk interval
    let configured := scalarPeerView peers pid psk interval
    ∀ ready : MixedPageReady updated configured nodes (mixedInitialRows updated configured) {hasWg := true},
    devicePrefixSpace updated ≤ NLMSG_GOODSIZE →
    MixedPlanFresh updated configured
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    MixedPlanCursorData updated
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) →
    mixedPageReceiveCount
      (mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready) ≤ 4096 →
    Campaign2.Ensures (do
      let ret ← wgSetDevice (mixedFwmarkAttrs d mark key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s =>
        let pages := mixedPages updated configured nodes (mixedInitialRows updated configured) {hasWg := true} ready
        result = ((if bad then -EINVAL else 0),.ok (mixedGetterJson updated configured nodes)) ∧
        s.wg.nlSock7 = socketReadbackFinal sock updated ∧
        ∃ postSet, MultiMixedEffect d mark pid psk interval postSet ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) :=
  fwmark_scalar_mixed_get_after_set d peers nodes mark key psk interval bad pid sock
    net found resident live bounded down residents readable idle emptyQueue

/-- On normal return, a changed nonzero listen-port collision exposes the
retained fwmark/generation and actual source-clearing prefix through full finite
mixed peer/allowed-IP readback. The old listen-port/socket bindings remain;
later request attributes are bypassed. Actual cursor handoffs remain explicit. -/
theorem original_port_refusal_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (mark port : Nat) (flags : Option UInt32)
    (key : Option Key) (entries : Option (List PeerEntry)) (bound : Nat → Bool) (sock : NlSock)
    (supported : flags.getD 0 &&& ~~~WGDEVICE_F_ALL = 0)
    (net : d.creatingNet = true) (running : d.running = true)
    (nonzero : port ≠ 0) (changed : d.incomingPort ≠ port)
    (collision : (bound port || d.sock4 == some port || d.sock6 == some port) = true)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (portRefusalBase d mark) peers nodes
      (mixedInitialRows (portRefusalBase d mark) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (portRefusalBase d mark) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (portRefusalBase d mark) peers
      (mixedPages (portRefusalBase d mark) peers nodes (mixedInitialRows (portRefusalBase d mark) peers)
        {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (portRefusalBase d mark)
      (mixedPages (portRefusalBase d mark) peers nodes (mixedInitialRows (portRefusalBase d mark) peers)
        {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (portRefusalBase d mark) peers nodes (mixedInitialRows (portRefusalBase d mark) peers)
        {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let pages := mixedPages (portRefusalBase d mark) peers nodes
      (mixedInitialRows (portRefusalBase d mark) peers) {hasWg := true} ready
    Campaign2.Ensures (do
      let ret ← wgSetDevice (portRefusalAttrs d mark port flags key entries)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.portBound = bound ∧ s.wg.nlSock7 = sock)
      (fun result s => result = (-EADDRINUSE,.ok (mixedGetterJson (portRefusalBase d mark) peers nodes)) ∧
        ∃ postSet, ∃ values : PeerId → Peer,
          withoutPeers postSet = withoutPeers (portRefusalBase d mark) ∧
          ClearedPeerStore d postSet d.peerList ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) :=
  port_refusal_mixed_get_after_set d peers nodes mark port flags key entries bound sock supported net running
    nonzero changed collision residents readable ready headerFits fresh cursorData within idle emptyQueue

/-- On normal return, an actual nonzero port-only update and full finite mixed
readback expose the same-port, stopped-device, available-bind or collision
outcome. The exact UDP socket fields and changed-port source clearing remain
explicit at the actual post-set Device, followed by the getter's cursor effects. -/
theorem original_nonzero_port_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (port : Nat) (bound : Nat → Bool) (sock : NlSock)
    (nonzero : port ≠ 0) (net : d.creatingNet = true)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady ((nonzeroPortRequestOutcome d port bound).2) peers nodes
      (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers) {hasWg := true})
    (headerFits : devicePrefixSpace ((nonzeroPortRequestOutcome d port bound).2) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh ((nonzeroPortRequestOutcome d port bound).2) peers
      (mixedPages ((nonzeroPortRequestOutcome d port bound).2) peers nodes (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers)
        {hasWg := true} ready))
    (cursorData : MixedPlanCursorData ((nonzeroPortRequestOutcome d port bound).2)
      (mixedPages ((nonzeroPortRequestOutcome d port bound).2) peers nodes (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers)
        {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages ((nonzeroPortRequestOutcome d port bound).2) peers nodes (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers)
        {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let pages := mixedPages ((nonzeroPortRequestOutcome d port bound).2) peers nodes
      (mixedInitialRows ((nonzeroPortRequestOutcome d port bound).2) peers) {hasWg := true} ready
    Campaign2.Ensures (do
      let ret ← wgSetDevice (portAttrs d port)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.portBound = bound ∧ s.wg.nlSock7 = sock)
      (fun result s => result = ((nonzeroPortRequestOutcome d port bound).1,.ok (mixedGetterJson ((nonzeroPortRequestOutcome d port bound).2) peers nodes)) ∧
        ∃ postSet, ∃ values : PeerId → Peer,
          withoutPeers postSet = withoutPeers ((nonzeroPortRequestOutcome d port bound).2) ∧
          (if d.incomingPort = port then postSet = requestGeneration d
            else ClearedPeerStore d postSet d.peerList) ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) :=
  nonzero_port_mixed_get_after_set d peers nodes port bound sock nonzero net residents readable
    ready headerFits fresh cursorData within idle emptyQueue

/-- On normal return, a zero-port setter followed by full finite mixed readback
exposes the actual selected port and socket fields, or the unchanged/stopped
branch, with ordered source clearing and getter cursor effects. Missing draws,
random collisions and reset Stops are retained; no draw-success premise. -/
theorem original_zero_port_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (sock : NlSock) (net : d.creatingNet = true)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList, ∀ id ∈ (peers pid).allowedipsList, d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (requestGeneration d) peers nodes
      (mixedInitialRows (requestGeneration d) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (requestGeneration d) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (requestGeneration d) peers
      (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
        {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (requestGeneration d)
      (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
        {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (requestGeneration d) peers nodes (mixedInitialRows (requestGeneration d) peers)
        {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let pages := mixedPages (requestGeneration d) peers nodes
      (mixedInitialRows (requestGeneration d) peers) {hasWg := true} ready
    Campaign2.Ensures (do
      let ret ← wgSetDevice (portAttrs d 0)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.nlSock7 = sock)
      (fun result s => ∃ chosen, ZeroPortRequestChoice d chosen ∧
        result = (0,.ok (mixedGetterJson (zeroPortRequestDevice d chosen) peers nodes)) ∧
        ∃ postSet, ∃ values : PeerId → Peer,
          withoutPeers postSet = withoutPeers (zeroPortRequestDevice d chosen) ∧
          (if d.incomingPort = 0 then postSet = requestGeneration d
            else ClearedPeerStore d postSet d.peerList) ∧
          (∀ q ∈ d.peerList, postSet.peers[q]? = some (values q)) ∧
          (∀ q, keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
          s.wg.device = some (mixedPagesDevice postSet pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock postSet ∧
          CursorHeld postSet (mixedPagesDevice postSet pages) none) :=
  zero_port_mixed_get_after_set d peers nodes sock net residents readable ready headerFits
    fresh cursorData within idle emptyQueue

/-- Actual empty allowed-IP replacement followed by complete mixed readback.
All original peer occurrences remain, with every removed ID filtered from
their lists. Only readable nonremoved dump nodes need a non-null owner.
The normal-return setter derives its structural removal effect; the getter
runs on that same successor, with its exact ordered cursor effects. -/
theorem original_replacement_mixed_get_after_set (d : Device) (peers : PeerId → Peer)
    (nodes : NodeId → AipNode) (key : Key) (pid : PeerId) (sock : NlSock)
    (found : d.peerHashtable.find? (·.1 == key) = some (key,pid))
    (resident : d.peers[pid]? = some (peers pid)) (pairs : NodePairs d)
    (live : 0 < (peers pid).refcount) (bounded : (peers pid).refcount+1 < 2^31)
    (down : d.running = false)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (readable : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList, d.nodes[id]? = some (nodes id))
    (owned : ∀ q ∈ d.peerList, ∀ id ∈ (peers q).allowedipsList,
      id ∉ (peers pid).allowedipsList → (nodes id).peer.isSome = true)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    let ids := (peers pid).allowedipsList
    let baseline := replacementReadbackInputs d ids
    let configured := fun q => erasePeerList ids (peers q)
    ∀ ready : MixedPageReady baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true},
    devicePrefixSpace baseline ≤ NLMSG_GOODSIZE →
    MixedPlanFresh baseline configured
      (mixedPages baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true} ready) →
    MixedPlanCursorData baseline
      (mixedPages baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true} ready) →
    mixedPageReceiveCount
      (mixedPages baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true} ready) ≤ 4096 →
    Campaign2.Ensures (do
      let ret ← wgSetDevice (replaceAllowedipsDeviceAttrs d key)
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧ s.wg.nlSock7 = sock)
      (fun result s =>
        let pages := mixedPages baseline configured nodes (mixedInitialRows baseline configured) {hasWg := true} ready
        result = (0,.ok (mixedGetterJson baseline configured nodes)) ∧
        ∃ removed,
          RemovalEffect (withPeer (requestGeneration d) pid
            {peers pid with refcount := (peers pid).refcount+1}) ids removed ∧
          let current := generalReplacementDevice removed pid (peers pid)
          s.wg.device = some (mixedPagesDevice current pages) ∧
          s.wg.nlSock7 = socketReadbackFinal sock current ∧
          CursorHeld current (mixedPagesDevice current pages) none) :=
  replacement_mixed_get_after_set d peers nodes key pid sock found resident pairs live bounded down
    residents readable owned idle emptyQueue

/-- On normal return of the actual flag-only REPLACE_PEERS request, initial
routing coherence, node shape and listed residency justify the actual post-free
and first-pass observations. Both original removal passes and all Stops remain;
no final-state emptiness or successful completion is asserted.
Erasure is unconditional by observedReplacePeers_erase. -/
theorem original_replace_peers_initial (d : Device) (t4 t6 : AllowedIps.Tree)
    (hi : AllowedIps.RoutingInvariant d t4 t6) (pairs : NodePairs d)
    (listed : ListedResidents d d.peerList) :
    Campaign2.Product.Ensures (observedReplacePeers (byIndex d))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s.toSnapshot d)
      (fun result _ => ∃ cut, result = (some cut, 0) ∧
        AllowedIps.Cleared (requestGeneration d) cut.afterFree ∧
        cut.afterFree.peerList = d.peerList ∧
        ∃ marked, cut.afterMark.wg.device = some marked ∧
          DeadPassEffect cut.afterFree d.peerList marked ∧
          ∀ pid ∈ d.peerList, ∃ p, marked.peers[pid]? = some p ∧ p.isDead = true) :=
  observedReplacePeers_initial d t4 t6 hi pairs listed

/-- The original allowed-IP setter followed by fresh single-peer serialization
on an arbitrary represented trie, including guard and allocation refusals.
Success derives normalized all-peer list transfer. Actual output lists and
node widths determine cancellation, splitting and exact serialized content;
no final representation or successful-allocation assumption is needed. -/
theorem original_allowedip_routing_readback (d : Device) (t4 t6 : AllowedIps.Tree)
    (pid : PeerId) (p : Peer) (attrs : AllowedIpAttrs) (ctx : DumpCtx) (skb : NlSkb)
    (shape : AllowedIps.AddressShape attrs)
    (routing : AllowedIps.RoutingInvariant d t4 t6)
    (resident : d.peers[pid]? = some p)
    (fresh : ctx.nextAllowedip = none) (sequence : ctx.allowedipsSeq = 0) :
    Campaign2.Ensures (setAllowedipThenGetPeerDump pid attrs ctx skb)
      (fun s => s.wg.device = some d)
      (fun result s => ∃ out next, s.wg.device = some out ∧
        out.peers[pid]? = some next ∧
        AllowedipRoutingEffect d out t4 t6 pid attrs result.1 ∧
        (result.1 = 0 → AllowedipMoved d out t4 t6 pid attrs) ∧
        result.2 = weightedPeerResult out (routingReadNode out) next ctx skb next.allowedipsList) :=
  allowedip_routing_readback d t4 t6 pid p attrs ctx skb shape routing resident fresh sequence

/-- Every normal original allowed-IP setter retains configured, resident owners
for both represented families from initial ownership and list residency.
Invalid attributes and ENOMEM retain their actual effects; no final
representation or successful-allocation premise is supplied. -/
theorem original_allowedip_owner_coherence (d : Device) (t4 t6 : AllowedIps.Tree)
    (pid : PeerId) (p : Peer) (attrs : AllowedIpAttrs)
    (shape : AllowedIps.AddressShape attrs)
    (routing : AllowedIps.RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6) (selected : pid ∈ d.peerList)
    (resident : d.peers[pid]? = some p)
    (listed : ∀ q ∈ d.peerList, ∃ p, d.peers[q]? = some p) :
    Campaign2.Ensures (setAllowedip pid attrs) (fun s => s.wg.device = some d)
      (fun ret s => ∃ out u4 u6, s.wg.device = some out ∧
        AllowedipRoutingEffect d out t4 t6 pid attrs ret ∧
        AllowedIps.RoutingInvariant out u4 u6 ∧ ConfiguredOwners out u4 u6 ∧
        ResidentOwnerLists out u4 u6) :=
  setAllowedip_resident_owners d t4 t6 pid p attrs shape routing owners selected resident listed


/-- The original initialized runner keeps exactly its JSON or indexed Stop
while retaining valid completed routing changes even before a later Stop.
Parsed attributes supply the address-shape premise. -/
theorem original_initialized_configuration_history (input : Lean.Json)
    (trace : Runner.Trace) (parsed : Runner.parseTrace input = .ok trace)
    (placeholders : Bool) :
    (InitializedRouting.inspection trace placeholders).outcome.map Prod.fst =
      Runner.executeTrace trace placeholders ∧
    AllowedIps.CompletionSafe ([],[])
      (InitializedRouting.inspection trace placeholders).routing :=
  ⟨InitializedRouting.inspection_json trace placeholders,
    InitializedRouting.inspection_safe trace
      (Configuration.parseTrace_shape input trace parsed) placeholders⟩

/-- A normal initialized execution has one actual endpoint carrying the
routing fold, coherent resident base list, index invariant and residual account.
Raw routing owners' membership in that base list is a separate obligation. -/
theorem original_initialized_configuration_endpoint (input : Lean.Json)
    (trace : Runner.Trace) (parsed : Runner.parseTrace input = .ok trace)
    (placeholders : Bool) (json : Lean.Json)
    (run : Runner.executeTrace trace placeholders = .ok json) :
    ∃ final, (InitializedRouting.inspection trace placeholders).outcome = .ok (json,final) ∧
      AllowedIps.CompletionSafe ([],[]) (InitializedRouting.inspection trace placeholders).routing ∧
      InitializedRouting.RoutingAt (InitializedRouting.inspection trace placeholders).routing final ∧
      InitializedRouting.BaseReady final ∧ Index.View.IndexCore final.toSnapshot ∧
      Index.InitializedBounds.EndpointSafe final.toSnapshot ∧
      Index.ReachedInitialized.ActualAccount trace placeholders json final :=
  InitializedRouting.parsed_accepted input trace parsed placeholders json run

/-- The actual complete peer removal retains configured ownership of all
represented routes at normal return, including through queued cleanup and
reference payments. No empty-work or supplied successor-state premise is used. -/
theorem original_peer_remove_configured_owners (d : Device) (t4 t6 : AllowedIps.Tree)
    (peer : Option PeerId) (routing : AllowedIps.RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6) :
    Campaign2.Ensures (peerRemove peer) (fun s => s.wg.device = some d)
      (fun _ s => ∃ out u4 u6, s.wg.device = some out ∧
        AllowedIps.RoutingInvariant out u4 u6 ∧ ConfiguredOwners out u4 u6) :=
  peerRemove_configured_owners d t4 t6 peer routing owners

/-- The original flag-only replacement completes both saved removal passes and
their queued work. A normal return derives zero status and an empty configured
peer list, public-key table and represented routes from initial funding,
stability, base coherence and routing. Allocated stores need not be empty. -/
theorem original_replace_peers_completion (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations)
    (tables : AllowedIps.FlatTable × AllowedIps.FlatTable) (d : Device) :
    Campaign2.Ensures (wgSetDevice (replacePeersAttrs (byIndex d)))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧
        ReplaceCompletion.View.Input cs loans tables s)
      (fun result s => result = 0 ∧ ReplaceCompletion.View.Empty s) :=
  ReplaceCompletion.request_completion cs loans tables d

/-- Actual whole bulk removal derives the same empty configured endpoint
through its real cleanup, without requiring initially empty work queues. -/
theorem original_peer_remove_all_completion (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations)
    (tables : AllowedIps.FlatTable × AllowedIps.FlatTable) :
    Campaign2.Ensures peerRemoveAll (ReplaceCompletion.View.Input cs loans tables)
      (fun _ s => ReplaceCompletion.View.Empty s) :=
  ReplaceCompletion.removal_completion cs loans tables


/-- Normal peer creation preserves represented configured owners, including
allocation refusal. Success publishes the actual selected slot in the configured
list; neither a successor representation nor allocation success is assumed. -/
theorem original_peer_create_configured_owners (key : Key) (psk : Option Key) :
    Campaign2.Ensures (peerCreate key psk) OwnerConfiguration.ProjectedReady
      (fun result s => OwnerConfiguration.ProjectedReady s ∧
        ∀ pid, result = .ok pid → ∃ d, s.wg.device = some d ∧ pid ∈ d.peerList) :=
  OwnerConfiguration.original_create key psk

/-- Original allowed-IP removal retains configured route ownership, deriving
its resident target from the actual normal run. -/
theorem original_remove_allowedips_configured_owners (pid : PeerId) :
    Campaign2.Ensures (removeByPeer pid) OwnerConfiguration.ProjectedReady
      (fun _ => OwnerConfiguration.ProjectedReady) :=
  OwnerConfiguration.original_removeByPeer pid

/-- The actual mixed allowed-IP, keepalive and staged-send tail preserves
configured route ownership and pays its selected caller reference on every
normal return, including malformed attributes and negative insertion results. -/
theorem original_peer_tail_configured_owners (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (paid : Queues.RxCredits.Owner)
    (attrs : PeerAttrs) (shape : Configuration.PeerAddressShape attrs) :
    Campaign2.Ensures (Configuration.peerConfigTailSource attrs (some paid.slot) paid.slot)
      (OwnerConfiguration.ProjectedSelected cs (paid :: loans) paid.slot)
      (fun _ => OwnerConfiguration.ProjectedEntry cs loans) :=
  OwnerConfiguration.original_tail cs loans paid attrs shape


/-- A configuration endpoint with its actual reference account has resident
configured route owners and exact owner-list membership for both families.
The representation may be supplied by another same-endpoint routing proof:
structural uniqueness identifies it with the ownership witness. -/
theorem original_configuration_boundary_owners (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (s : Campaign2.Snapshot)
    (d : Device) (t4 t6 : AllowedIps.Tree)
    (entry : OwnerConfiguration.ProjectedEntry cs loans s)
    (device : s.wg.device = some d)
    (routing : AllowedIps.RoutingInvariant d t4 t6) :
    ConfiguredOwners d t4 t6 ∧ ResidentOwnerLists d t4 t6 :=
  OwnerConfiguration.projected_entry_resident cs loans s d t4 t6 entry device routing


/-- The complete original peer command retains its actual account and
configured routing ownership through lookup, creation, update-only, removal
and normal refusals. Every exact final representation consequently has resident
configured owners and their node-list membership; no final-state premise is used. -/
theorem original_peer_command_configured_owners (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : PeerAttrs)
    (shape : Configuration.PeerAddressShape attrs) :
    Campaign2.Ensures (setPeerCmd attrs) (OwnerConfiguration.ProjectedEntry cs loans)
      (fun _ s => OwnerConfiguration.ProjectedEntry cs loans s ∧
        ∀ d t4 t6, s.wg.device = some d → AllowedIps.RoutingInvariant d t4 t6 →
          ConfiguredOwners d t4 t6 ∧ ResidentOwnerLists d t4 t6) := by
  intro g a result v b pre run
  have after := OwnerConfiguration.original_command cs loans attrs shape
    g a result v b pre run
  exact ⟨after, fun d t4 t6 device routing =>
    OwnerConfiguration.projected_entry_resident cs loans _ d t4 t6 after device routing⟩



/-- The actual queued replacement and complete getter return the generation-
adjusted empty-peer JSON. Initial funding and structural coherence supply the
cleanup result; no empty-work or preselected successor is assumed. -/
theorem original_queued_replace_peers_get_after_set
    (cs : Queues.RxCredits.Ledger) (loans : Queues.RxCredits.Reservations)
    (tables : AllowedIps.FlatTable × AllowedIps.FlatTable) (d : Device) (sock : NlSock)
    (room : devicePrefixSpace (requestGeneration d) + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (queue : sock.queue = []) :
    Campaign2.Ensures (do
      let ret ← wgSetDevice (replacePeersAttrs (byIndex d))
      let value ← wgGetDevice (byIndex d)
      pure (ret,value))
      (fun s => s.wg.device=some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.nlSock7=sock ∧ ReplaceCompletion.View.Input cs loans tables s)
      (fun result s => result=(0,.ok (emptyPeersJson (requestGeneration d))) ∧
        ReplaceCompletion.View.Empty s ∧
        s.wg.nlSock7=socketReadbackFinal sock (requestGeneration d)) :=
  replacement_queued_get_after_set cs loans tables d sock room idle queue


/-- The complete mixed device setter retains configured ownership and its
actual reference account on every normal path, including ordered peer errors,
private-key conflict cleanup, replacement and listen-port refusal. -/
theorem original_device_command_configured_owners (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (shape : Configuration.DeviceAddressShape attrs) :
    Campaign2.Ensures (wgSetDevice attrs) (OwnerConfiguration.ProjectedEntry cs loans)
      (fun _ s => OwnerConfiguration.ProjectedEntry cs loans s ∧
        ∀ d t4 t6, s.wg.device = some d → AllowedIps.RoutingInvariant d t4 t6 →
          ConfiguredOwners d t4 t6 ∧ ResidentOwnerLists d t4 t6) := by
  intro g a result v b pre run
  have after := OwnerConfiguration.original_device cs loans attrs shape
    g a result v b pre run
  exact ⟨after, fun d t4 t6 device routing =>
    OwnerConfiguration.projected_entry_resident cs loans _ d t4 t6 after device routing⟩

/-- Every normal queued replacement establishes the actual successor state
needed for empty-peer readback; completion of the combined program is not assumed. -/
theorem original_queued_replace_peers_getter_ready
    (cs : Queues.RxCredits.Ledger) (loans : Queues.RxCredits.Reservations)
    (tables : AllowedIps.FlatTable × AllowedIps.FlatTable) (d : Device) (sock : NlSock) :
    Campaign2.Ensures (wgSetDevice (replacePeersAttrs (byIndex d)))
      (fun s => s.wg.device=some d ∧ ClaimView.selectsDevice s d ∧
        s.wg.nlSock7=sock ∧ ReplaceCompletion.View.Input cs loans tables s)
      (fun ret s => ret=0 ∧ ReplacementReadbackReady (requestGeneration d) sock s) :=
  replacement_queued_getter_ready cs loans tables d sock

/-- The derived replacement successor admits the actual complete getter under
the initial static room and socket bounds, for every concrete state realization. -/
theorem original_replacement_ready_getter_returns (d : Device) (sock : NlSock)
    (room : devicePrefixSpace d + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (queue : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d)) (ReplacementReadbackReady d sock)
      (fun value s => value=.ok (emptyPeersJson d) ∧
        ReplaceCompletion.View.Empty s ∧ s.wg.nlSock7=socketReadbackFinal sock d) :=
  replacement_ready_getter_returns d sock room idle queue


/-- A valid REMOVE_ME command follows actual queued cleanup and bypasses later
attributes, including malformed entries. Its normal endpoint has exact configured
list/table filtering and no represented route owned by the removed peer. -/
theorem original_queued_remove_peer_command (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations)
    (attrs : PeerAttrs) (key : Key) (flags : UInt32) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key) (flagattr : attrs.flags=some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>OwnerConfiguration.ProjectedEntry cs loans s ∧ s.wg.device=some before)
      (fun ret s=>ret=0 ∧ OwnerConfiguration.ProjectedEntry cs loans s ∧
        ∃ after,s.wg.device=some after ∧ QueuedRemove.Effect before pid after) :=
  QueuedRemove.original_command cs loans attrs key flags pid before
    pubkey flagattr valid protocol remove found

/-- Every original mixed device-request outcome has its exact completed-call
certificate: ordered stages, actual receipts and linked generation entry.
Earlier completed receipts remain visible when a later helper stops. -/
theorem original_mixed_device_request_certificate (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _ => True)
      (fun entry outcome => ∃ result : RequestOrder.Inspection,
        result.outcome = outcome ∧ RequestOrder.Certificate attrs entry result) :=
  RequestOrder.original_request_certificate attrs

/-- Completed peer commands occupy their original input-list positions.
Malformed entries and a first negative result cut off later peer commands. -/
theorem original_mixed_device_peer_position (attrs : DeviceAttrs)
    (entry : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (facts : RequestOrder.Certificate attrs entry result)
    (i : Nat) (r : RequestOrder.Receipt) (p : PeerAttrs)
    (selected : (RequestOrder.peerReceipts result.receipts)[i]? = some r)
    (kind : r.kind = .peer p) :
    (attrs.peers.getD [])[i]? = some (.attrs p) :=
  RequestOrder.certificate_peer_position attrs entry result facts i r p selected kind

/-- The first completed negative peer result is the last completed peer
command, including in a request whose later enclosing computation stops. -/
theorem original_mixed_device_negative_peer_cutoff (attrs : DeviceAttrs)
    (entry : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (facts : RequestOrder.Certificate attrs entry result) (r : RequestOrder.Receipt)
    (member : r ∈ RequestOrder.peerReceipts result.receipts) (negative : r.result < 0) :
    ∃ before, RequestOrder.peerReceipts result.receipts = before ++ [r] :=
  RequestOrder.request_negative_peer_last attrs result.receipts facts.1.2.2.1 r member negative

/-- A nonempty actual request certificate begins with its generation action.
Its before-WG equals request entry; the optional device generation alone changes,
and the action preserves its Ambient state. -/
theorem original_mixed_device_generation_entry (attrs : DeviceAttrs)
    (entry : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (facts : RequestOrder.Certificate attrs entry result)
    (nonempty : result.receipts ≠ []) :
    ∃ r rest, result.receipts = r :: rest ∧ RequestOrder.EntryReceipt attrs entry.wg r :=
  RequestOrder.certificate_entry attrs entry result facts nonempty


/-- Parsed initialized executions derive represented, configured, resident route
owners at their actual final snapshot in both placeholder modes. -/
theorem parsed_initialized_configuration_ownership (input : Lean.Json) (trace : Runner.Trace)
    (parsed : Runner.parseTrace input=.ok trace) (placeholders : Bool) (json : Lean.Json)
    (run : Runner.executeTrace trace placeholders=.ok json) :
    ∃ final, (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final) ∧
      InitializedOwner.OwnershipAt final :=
  InitializedOwner.parsed_accepted input trace parsed placeholders json run

/-- The ownership endpoint is the same projected snapshot retained by the actual
initialized routing/account inspection, without a supplied invariant. -/
theorem original_initialized_configuration_ownership (trace : Runner.Trace)
    (shape : Configuration.TraceAddressShape trace) (placeholders : Bool)
    (json : Lean.Json) (final : Campaign2.Product.Snapshot)
    (run : (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final)) :
    InitializedOwner.OwnershipAt final :=
  InitializedOwner.normal trace shape placeholders json final run

/-- Arbitrary mixed requests expose their actual completed-stage certificate and
the whole normal endpoint relation for any completed nonzero port result. -/
theorem original_mixed_device_refusal_certificate (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _ => True)
      (fun entry outcome => ∃ result : RequestOrder.Inspection,
        result.outcome = outcome ∧ RequestOrder.Certificate attrs entry result ∧
        RequestOrder.RefusalFacts result) :=
  RequestOrder.original_request_refusal_certificate attrs

/-- A same-request nonzero port receipt determines the exact normal return and
entire final WG projection. Ambient is not asserted equal. -/
theorem original_mixed_device_port_refusal (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : RequestOrder.Inspection) (facts : RequestOrder.Certificate attrs entry result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : RequestOrder.Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind=.port port) (nonzero : r.result ≠ 0) :
    ret=r.result ∧ final.wg=r.after.wg :=
  RequestOrder.certificate_port_refusal attrs entry result facts ret final normal
    r member port kind nonzero

/-- Source clearing changes just the selected peer's source/cache fields at the
actual completed cut, even if the enclosing request later stops. -/
theorem original_mixed_device_clear_source (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : RequestOrder.Inspection) (facts : RequestOrder.Certificate attrs initial result)
    (r : RequestOrder.Receipt) (member : r ∈ result.receipts) (pid : PeerId)
    (kind : r.kind=.clearSource pid) (d : Device) (p : Peer)
    (resident : d.peers[pid]?=some p) (entry : r.before.wg.device=some d) :
    r.result=0 ∧ ∃ d' reset, r.after.wg.device=some d' ∧
      d'={d with peers:=d'.peers} ∧
      d'.peers[pid]?=some (clearedSource p reset) ∧
      ∀ q, q ≠ pid → d'.peers[q]?=d.peers[q]? :=
  RequestOrder.certificate_clear_source attrs initial result facts r member pid kind
    d p resident entry

/-- A completed nonzero-port call retains its exact unchanged-port or socket
outcome, relative to that call's actual entry inside the mixed request. -/
theorem original_mixed_device_nonzero_port_effects (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (facts : RequestOrder.Certificate attrs initial result)
    (r : RequestOrder.Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind=.port port) (d : Device) (nonzero : port ≠ 0)
    (entry : r.before.wg.device=some d) :
    if d.incomingPort=port then r.result=0 ∧ r.after.wg.device=some d
    else r.result=(portOutcome d port r.before.wg.portBound).1 ∧
      r.after.wg.device.map withoutPeers=
        some (withoutPeers (portOutcome d port r.before.wg.portBound).2) ∧
      ClaimView.clearedPeers d r.after.wg.toCore d.peerList :=
  RequestOrder.certificate_nonzero_port_effects attrs initial result facts r member
    port kind d nonzero entry

/-- A completed zero-port call retains the exact unchanged/stopped/allocation
cases. Creating-namespace membership remains the concrete entry condition. -/
theorem original_mixed_device_zero_port_effects (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (facts : RequestOrder.Certificate attrs initial result)
    (r : RequestOrder.Receipt) (member : r ∈ result.receipts) (kind : r.kind=.port 0)
    (d : Device) (net : d.creatingNet=true) (entry : r.before.wg.device=some d) :
    r.result=0 ∧ ClaimView.zeroPortEffects d r.after :=
  RequestOrder.certificate_zero_port_effects attrs initial result facts r member kind d net entry

/-- A refused nonzero port is the final normal device effect, including exact
socket code, non-peer device fields and source clearing. -/
theorem original_mixed_device_nonzero_port_refusal (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (facts : RequestOrder.Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : RequestOrder.Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind=.port port) (d : Device) (nonzero : port ≠ 0)
    (entry : r.before.wg.device=some d) (refused : r.result ≠ 0) :
    ret=(portOutcome d port r.before.wg.portBound).1 ∧
      final.wg.device.map withoutPeers=
        some (withoutPeers (portOutcome d port r.before.wg.portBound).2) ∧
      ClaimView.clearedPeers d final.wg.toCore d.peerList :=
  RequestOrder.certificate_nonzero_port_refusal attrs initial result facts ret final normal
    r member port kind d nonzero entry refused


/-- Initialized endpoint coherence supplies actual peer/node reads and unique serialized lists. This does not assert getter completion. -/
theorem original_initialized_dump_readable (trace : Runner.Trace)
    (shape : Configuration.TraceAddressShape trace) (placeholders : Bool)
    (json : Lean.Json) (final : Campaign2.Product.Snapshot)
    (run : (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final))
    (d : Device) (present : final.wg.device=some d) : DeviceDumpReadable d :=
  initialized_dump_readable trace shape placeholders json final run d present

/-- The canonical complete getter derives pagination freshness from coherent data. Page capacity, cursor reference bounds, socket readiness and receive budget remain explicit. -/
theorem original_readable_mixed_getter_returns (d : Device) (sock : NlSock)
    (data : DeviceDumpReadable d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : sock.cbRunning=false) (emptyQueue : sock.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s=>s.wg.device=some d ∧ s.wg.nlSock7=sock ∧ ClaimView.selectsDevice s d)
      (fun result s=>result=.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d)) ∧
        s.wg.device=some (mixedPagesDevice d pages) ∧
        s.wg.nlSock7=socketReadbackFinal sock d ∧ CursorHeld d (mixedPagesDevice d pages) none) :=
  readable_mixed_getter_returns d sock data ready headerFits cursorData idle emptyQueue within

/-- Every normal arbitrary peer command preserves the device getter header and socket/selector observation, including errno returns. -/
theorem original_peer_command_getter_metadata (attrs : PeerAttrs) (entry : GetterMetadata) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>getterMetadataObservation s=entry)
      (fun _ s=>getterMetadataObservation s=entry) :=
  setPeerCmd_getterMetadata attrs entry

/-- The actual complete key stage classifies absent/unchanged, public generation, funded collision cleanup and ordered installation, including first identity. -/
theorem original_configuration_key_stage (cs : Queues.RxCredits.Ledger) (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (before : Device) :
    Campaign2.Ensures (RequestOrder.keyStage attrs)
      (fun s=>OwnerConfiguration.ProjectedEntry cs loans s ∧ s.wg.device=some before)
      (fun ret s=>ret=0 ∧ OwnerConfiguration.ProjectedEntry cs loans s ∧
        ∃ after,s.wg.device=some after ∧ KeyStage.Effect attrs before after) :=
  KeyStage.original_stage cs loans attrs before

/-- A same-request completed key stage retains its all-branch effects before later Stops. Its account premise is explicitly at the recorded stage entry. -/
theorem original_mixed_device_key_stage (cs : Queues.RxCredits.Ledger) (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial result)
    (r : RequestOrder.Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (before : Device) (pre : OwnerConfiguration.ProjectedEntry cs loans r.before)
    (device : r.before.wg.device=some before) :
    r.result=0 ∧ OwnerConfiguration.ProjectedEntry cs loans r.after ∧
      ∃ after,r.after.wg.device=some after ∧ KeyStage.Effect attrs before after :=
  KeyStage.certificate_effect cs loans attrs initial result certificate r member kind before pre device

/-- Every arbitrary request outcome retains original-entry field continuity at each completed port receipt. -/
theorem original_mixed_device_input_certificate (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _ => True)
      (fun entry outcome => ∃ result : RequestOrder.Inspection,
        result.outcome = outcome ∧ RequestOrder.Certificate attrs entry result ∧
          RequestOrder.InputHistory attrs entry.wg result.receipts) :=
  RequestOrder.original_request_input_certificate attrs

/-- A completed port receipt starts after the actual generation/fwmark/source-clear prefix of this same request. -/
theorem original_mixed_device_port_input (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : RequestOrder.Inspection) (facts : RequestOrder.Certificate attrs entry result)
    (r : RequestOrder.Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind = .port port) : RequestOrder.PortInput attrs entry.wg r :=
  RequestOrder.certificate_port_input attrs entry result facts r member port kind

/-- A normal refused nonzero-port request has the original entry's generation/fwmark-adjusted header, exact source clearing and unchanged bind/socket/selector context. -/
theorem original_mixed_device_initial_port_refusal (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : RequestOrder.Inspection) (facts : RequestOrder.Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome = .ok (ret,final))
    (d : Device) (entry : initial.wg.device = some d)
    (r : RequestOrder.Receipt) (member : r ∈ result.receipts) (port : Nat)
    (kind : r.kind = .port port) (nonzero : port ≠ 0) (refused : r.result ≠ 0) :
    ret = (portOutcome (RequestOrder.prefixDevice attrs d) port initial.wg.portBound).1 ∧
      final.wg.device.map withoutPeers = some (withoutPeers (RequestOrder.prefixDevice attrs d)) ∧
      ClaimView.clearedPeers d final.wg.toCore d.peerList ∧
      final.wg.portBound = initial.wg.portBound ∧
      final.wg.nlSock7 = initial.wg.nlSock7 ∧
      final.wg.fixtureNetDevices = initial.wg.fixtureNetDevices :=
  RequestOrder.certificate_initial_port_refusal attrs initial result facts ret final normal d entry r member port kind nonzero refused


/-- The actual initialized endpoint supplies readable and fresh mixed getter data; static space, reference, socket and receive bounds remain explicit. -/
theorem original_initialized_mixed_readback (trace : Runner.Trace)
    (shape : Configuration.TraceAddressShape trace) (placeholders : Bool)
    (json : Lean.Json) (final : Campaign2.Product.Snapshot)
    (run : (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final))
    (d : Device) (present : final.wg.device=some d)
    (selected : ClaimView.selectsDevice final.toSnapshot d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : final.wg.nlSock7.cbRunning=false) (emptyQueue : final.wg.nlSock7.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s=>s=final.toSnapshot)
      (fun result s=>result=.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d)) ∧
        s.wg.device=some (mixedPagesDevice d pages) ∧
        s.wg.nlSock7=socketReadbackFinal final.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d pages) none) :=
  initialized_mixed_readback trace shape placeholders json final run d present selected ready headerFits cursorData idle emptyQueue within

/-- Every completed key stage of an arbitrary original request has its account and exact all-branch effect derived from funding at the outer entry, including before later Stops. -/
theorem original_mixed_device_funded_key_effects (cs : Queues.RxCredits.Ledger) (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (OwnerConfiguration.ProjectedEntry cs loans)
      (fun initial outcome=>∃ result : RequestOrder.Inspection,
        result.outcome=outcome ∧ RequestOrder.Certificate attrs initial result ∧ KeyStage.RequestEffects cs loans attrs result) :=
  KeyStage.original_request_effects cs loans attrs

/-- Completed key and peer receipts agree on getter metadata; on normal return they agree with the actual final metadata. Stops retain completed receipt consistency. -/
theorem original_mixed_device_metadata_certificate (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _=>True)
      (fun entry outcome=>∃result : RequestOrder.Inspection,
        result.outcome=outcome ∧ RequestOrder.Certificate attrs entry result ∧ RequestOrder.MetadataFacts result) :=
  RequestOrder.original_request_metadata attrs

/-- The getter metadata after any completed key stage is exactly the normal whole request's final metadata. -/
theorem original_mixed_device_key_final_metadata (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : RequestOrder.Inspection) (facts : RequestOrder.Certificate attrs entry result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : RequestOrder.Receipt) (member : r ∈ result.receipts) (kind : r.kind=.keyStage) :
    getterMetadataObservation r.after=getterMetadataObservation final :=
  RequestOrder.certificate_key_final_metadata attrs entry result facts ret final normal r member kind

/-- Each completed peer command's entry and exit getter metadata equals the normal whole request's final metadata. -/
theorem original_mixed_device_peer_final_metadata (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : RequestOrder.Inspection) (facts : RequestOrder.Certificate attrs entry result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : RequestOrder.Receipt) (member : r ∈ result.receipts) (p : PeerAttrs) (kind : r.kind=.peer p) :
    getterMetadataObservation r.before=getterMetadataObservation final ∧
      getterMetadataObservation r.after=getterMetadataObservation final :=
  RequestOrder.certificate_peer_final_metadata attrs entry result facts ret final normal r member p kind

/-- An actual arbitrary setter/getter pair returns the computed committed prefix JSON and cursor effects when its same-run certificate contains a normal nonzero-port refusal. Other outcomes retain their exact provenance. -/
theorem original_mixed_device_refusal_readback (attrs : DeviceAttrs) (d : Device)
    (peers : PeerId → Peer) (nodes : NodeId → AipNode) (sock : NlSock)

    (residents : ∀ q ∈ d.peerList,d.peers[q]? = some (peers q))
    (readable : ∀ pid ∈ d.peerList,∀ id ∈ (peers pid).allowedipsList,
      d.nodes[id]? = some (nodes id))
    (ready : MixedPageReady (RequestOrder.prefixDevice attrs d) peers nodes
      (mixedInitialRows (RequestOrder.prefixDevice attrs d) peers) {hasWg := true})
    (headerFits : devicePrefixSpace (RequestOrder.prefixDevice attrs d) ≤ NLMSG_GOODSIZE)
    (fresh : MixedPlanFresh (RequestOrder.prefixDevice attrs d) peers
      (mixedPages (RequestOrder.prefixDevice attrs d) peers nodes
        (mixedInitialRows (RequestOrder.prefixDevice attrs d) peers) {hasWg := true} ready))
    (cursorData : MixedPlanCursorData (RequestOrder.prefixDevice attrs d)
      (mixedPages (RequestOrder.prefixDevice attrs d) peers nodes
        (mixedInitialRows (RequestOrder.prefixDevice attrs d) peers) {hasWg := true} ready))
    (within : mixedPageReceiveCount
      (mixedPages (RequestOrder.prefixDevice attrs d) peers nodes
        (mixedInitialRows (RequestOrder.prefixDevice attrs d) peers) {hasWg := true} ready) ≤ 4096)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = [])
:
    let pages := mixedPages (RequestOrder.prefixDevice attrs d) peers nodes
      (mixedInitialRows (RequestOrder.prefixDevice attrs d) peers) {hasWg := true} ready
    Campaign2.Observes (do
      let ret ← wgSetDevice attrs
      let dump ← wgGetDevice (byIndex d)
      pure (ret,dump))
      (fun s => s.wg.device = some d ∧ ClaimView.selectsDevice s d ∧ s.wg.nlSock7 = sock)
      (fun initial outcome => ∃ inspected : RequestOrder.Inspection,
        RequestOrder.Certificate attrs initial inspected ∧ RequestOrder.ReadbackMatches attrs d initial inspected outcome ∧
        ∀ ret middle, inspected.outcome = .ok (ret,middle) →
          ∀ r ∈ inspected.receipts, ∀ port, r.kind = .port port → port ≠ 0 → r.result ≠ 0 →
            ret = (portOutcome (RequestOrder.prefixDevice attrs d) port initial.wg.portBound).1 ∧
            ∃ final, outcome = .ok ((ret,.ok (mixedGetterJson (RequestOrder.prefixDevice attrs d) peers nodes)),final) ∧
              RequestOrder.MixedRefusalReadback attrs d peers nodes sock pages
                (.ok (mixedGetterJson (RequestOrder.prefixDevice attrs d) peers nodes)) final) :=
  RequestOrder.original_refusal_mixed_readback attrs d peers nodes sock residents readable ready headerFits fresh cursorData within idle emptyQueue


/-- Every normal arbitrary setter preserves its optional device-associated socket and selector-table observation. -/
theorem original_configuration_getter_context (attrs : DeviceAttrs) (initial : GetterContext.Context) :
    Campaign2.Ensures (wgSetDevice attrs) (fun s=>GetterContext.observation s=initial)
      (fun _ s=>GetterContext.observation s=initial) :=
  GetterContext.original_request_context attrs initial

/-- A normally returned arbitrary setter preserves device presence and the actual getter socket and selector table from a resident entry. -/
theorem original_configuration_resident_getter_context (attrs : DeviceAttrs) (sock : NlSock)
    (fixtures : FixtureDevices) :
    Campaign2.Ensures (wgSetDevice attrs)
      (fun s=>s.wg.device.isSome=true ∧ s.wg.nlSock7=sock ∧ s.wg.fixtureNetDevices=fixtures)
      (fun _ s=>s.wg.device.isSome=true ∧ s.wg.nlSock7=sock ∧ s.wg.fixtureNetDevices=fixtures) :=
  GetterContext.original_request_resident_context attrs sock fixtures

/-- A same-request completed funded key stage determines the normal final identity after arbitrary later peer attributes, retaining the actual collision-removal baseline. -/
theorem original_mixed_device_final_identity (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : RequestOrder.Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage) :
    ∃ before after, r.before.wg.device=some before ∧ final.wg.device=some after ∧
      KeyStage.IdentityEffect attrs before after.staticIdentity :=
  KeyStage.certificate_final_identity cs loans attrs initial result certificate pre ret final normal r member kind

/-- The final private key follows the actual unchanged-key guard or installation clamp, and survives later peer attributes. -/
theorem original_mixed_device_final_private (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : RequestOrder.Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (key : Key) (given : attrs.privateKey=some key) :
    ∃ before after, r.before.wg.device=some before ∧ final.wg.device=some after ∧
      after.staticIdentity.staticPrivate=
        if before.staticIdentity.staticPrivate=key then key else clamp key :=
  KeyStage.certificate_final_private cs loans attrs initial result certificate pre ret final normal r member kind key given

/-- Toggling UPDATE_ONLY on an existing funded target preserves the whole original outcome, including Stops and logs; both requests explicitly supply flags. -/
theorem original_update_only_existing (cs : Queues.RxCredits.Ledger) (loans : Queues.RxCredits.Reservations)
    (attrs : PeerAttrs) (key : Key) (flags : UInt32) (pid : PeerId) (d : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (found : d.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Campaign2.AgreesOn (fun s=>OwnerConfiguration.ProjectedEntry cs loans s ∧ s.wg.device=some d)
      (setPeerCmd {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)})
      (setPeerCmd {attrs with flags:=some flags}) :=
  UpdateOnly.original_existing cs loans attrs key flags pid d pubkey valid protocol found

/-- A valid UPDATE_ONLY command without a public-key table match returns zero and preserves WG state regardless of later attributes. -/
theorem original_update_only_absent (attrs : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : Campaign2.State) (d : Device)
    (device : initial.device=some d)
    (pubkey : attrs.publicKey=some key) (valid : flags &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (missing : d.peerHashtable.find? (·.1 == key)=none) :
    Campaign2.Returns
      (setPeerCmd {attrs with flags:=some (flags ||| WGPEER_F_UPDATE_ONLY)})
      (fun s=>s.wg=initial) (fun ret s=>ret=0 ∧ s.wg=initial) :=
  UpdateOnly.original_absent attrs key flags initial d device pubkey valid protocol missing

/-- The original peer command rejects missing public key, unsupported flags and unsupported protocol in that priority, preserving WG state. -/
theorem original_peer_validation_refusal (attrs : PeerAttrs) (code : Int)
    (refused : UpdateOnly.validationError attrs=some code) (initial : Campaign2.State) :
    Campaign2.Returns (setPeerCmd attrs) (fun s=>s.wg=initial)
      (fun ret s=>ret=code ∧ s.wg=initial) :=
  UpdateOnly.original_validation attrs code refused initial


/-- The original acquired-peer update has an exact completed PSK/endpoint cut before replacement, allowed-IP and send/payment work. Later Stops retain that cut; REMOVE_ME is excluded by the explicit branch premise. -/
theorem original_acquired_peer_scalar_prefix (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (keep : flags &&& WGPEER_F_REMOVE_ME = 0)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Campaign2.Observes (peerConfigUpdateSource attrs peer flags psk pid)
      (fun s=>s.wg.device=some d)
      (fun initial outcome=>∃result,ScalarPrefix.Matches attrs peer flags psk pid initial result ∧
        result.outcome=outcome ∧ ScalarPrefix.Facts attrs psk pid d p initial result) :=
  ScalarPrefix.original_update_outcome attrs peer flags psk pid keep d p resident

/-- Actual staged sending retains the incarnation, PSK, keepalive interval and full endpoint of every surviving peer; survival is not assumed or asserted. -/
theorem original_staged_peer_scalar_retention (pid : PeerId) (initial : PeerScalarRetention.Map) :
    Campaign2.Ensures (sendStagedPackets pid)
      (fun s=>PeerScalarRetention.observation s=initial)
      (fun _ s=>PeerScalarRetention.Retained initial (PeerScalarRetention.observation s)) :=
  PeerScalarRetention.staged pid initial

/-- Actual keepalive preparation retains the incarnation, PSK, keepalive interval and full endpoint of every surviving peer. -/
theorem original_keepalive_peer_scalar_retention (pid : PeerId) (initial : PeerScalarRetention.Map) :
    Campaign2.Ensures (sendKeepalive pid)
      (fun s=>PeerScalarRetention.observation s=initial)
      (fun _ s=>PeerScalarRetention.Retained initial (PeerScalarRetention.observation s)) :=
  PeerScalarRetention.keepalive pid initial

/-- An actual mixed setter/getter pair reads the final key-stage identity and exact mixed JSON/cursor effects under explicit coherent-data and static getter bounds; the actual key-stage entry and collision baseline remain explicit. -/
theorem original_mixed_device_key_readback (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (inspected : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial inspected)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (middle : Campaign2.Snapshot) (normal : inspected.outcome=.ok (ret,middle))
    (r : RequestOrder.Receipt) (member : r∈inspected.receipts) (kind : r.kind=.keyStage)
    (d : Device) (present : middle.wg.device=some d) (data : DeviceDumpReadable d)
    (selected : ClaimView.selectsDevice middle d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : middle.wg.nlSock7.cbRunning=false) (emptyQueue : middle.wg.nlSock7.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096)
    (outcome : Campaign2.Outcome (Int × Except Int Lean.Json))
    (matched : RequestOrder.ReadbackMatches attrs d initial inspected outcome) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    ∃ before, r.before.wg.device=some before ∧ KeyStage.IdentityEffect attrs before d.staticIdentity ∧
      ∃ final,outcome=.ok ((ret,.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d))),final) ∧
        final.wg.device=some (mixedPagesDevice d pages) ∧
        final.wg.nlSock7=socketReadbackFinal middle.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d pages) none :=
  certificate_key_mixed_readback cs loans attrs initial inspected certificate pre ret middle normal r member kind d present data selected ready headerFits cursorData idle emptyQueue within outcome matched


open AllowedOrder AllowedIps Configuration in
/-- The actual acquired update retains ordered allowed-IP completions, replacement/removal precedence and exact normal or stopped outcome for arbitrary attributes. -/
theorem original_acquired_allowed_ip_order (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    Campaign2.Observes (peerConfigUpdateSource attrs peer flags psk pid) (fun _=>True)
      (fun entry outcome=>∃result:Inspection,result.outcome=outcome ∧
        Facts attrs peer flags psk pid entry result) :=
  AllowedOrder.original_update_order attrs peer flags psk pid

open AllowedOrder AllowedIps Configuration in
/-- The same acquired update combines completion order with the exact represented routing fold under explicit initial routing and address-shape premises. -/
theorem original_acquired_routed_allowed_ip_order (tables : FlatTable×FlatTable) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    Campaign2.Observes (peerConfigUpdateSource attrs peer flags psk pid) (RoutedTarget tables pid)
      (fun entry outcome=>∃result:Inspection,result.outcome=outcome ∧
        Facts attrs peer flags psk pid entry result ∧ RoutedFacts tables result) :=
  AllowedOrder.original_update_routed_order tables attrs shape peer flags psk pid

open AllowedOrder AllowedIps Configuration in
/-- Every completed allowed-IP event occupies its actual input position in the original acquired update. -/
theorem original_allowed_ip_completion_position (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId)
    (entry : Campaign2.Snapshot) (result : Inspection)
    (facts : Facts attrs peer flags psk pid entry result)
    (i : Nat) (e : RoutingCompletion) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (allowedEvents result.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) :
    (attrs.allowedIps.getD [])[i]?=some (.attrs ip) :=
  AllowedOrder.certificate_allowed_position attrs peer flags psk pid entry result facts i e ip ret selected call

open AllowedOrder AllowedIps Configuration in
/-- The first negative completed allowed-IP result is the last completed allowed-IP event, including prefixes before later Stops. -/
theorem original_allowed_ip_negative_cutoff (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId)
    (entry : Campaign2.Snapshot) (result : Inspection)
    (facts : Facts attrs peer flags psk pid entry result)
    (i : Nat) (e : RoutingCompletion) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (allowedEvents result.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) (negative : ret<0) :
    i+1=(allowedEvents result.completions).length :=
  AllowedOrder.certificate_negative_last attrs peer flags psk pid entry result facts i e ip ret selected call negative

open ScalarFinish PeerScalarRetention Queues.RxCredits in
/-- The actual finish derives selected-peer survival from the same reference account, preserves its incarnation, PSK and full endpoint, writes the optional interval and pays the caller. -/
theorem original_acquired_finish_scalar_effect (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (ret : Int) (expected : Cell) :
    Campaign2.Ensures (Configuration.peerTailFinishSource attrs (some paid.slot) paid.slot ret)
      (FinishInput cs loans paid expected)
      (fun result s=>result=ret ∧ Index.View.ConfigurationInput cs loans s ∧
        observation s paid.slot=some (finishCell attrs expected)) :=
  ScalarFinish.original_finish cs loans paid attrs ret expected

open RequestOrder RequestOrder.KeyHeader in
/-- The original mixed request connects every completed key-stage entry to its actual original header and successful port receipt, including before later Stops. -/
theorem original_request_key_entry_history (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _=>True)
      (fun initial outcome=>∃ result : Inspection,result.outcome=outcome ∧
        Certificate attrs initial result ∧ History attrs initial.wg result.receipts) :=
  RequestOrder.KeyHeader.original_request attrs

open RequestOrder RequestOrder.KeyHeader in
/-- Every completed key-stage entry has the original name, index and identity, the single generation increment, selected mark and actual same-request port origin. -/
theorem original_request_key_entry_fields (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d) :
    ∃ current,r.before.wg.device=some current ∧ Fields attrs d current ∧
      PortOrigin attrs initial.wg result.receipts (some current.incomingPort) :=
  RequestOrder.KeyHeader.certificate_key_fields attrs initial result certificate r member key d device

open RequestOrder RequestOrder.KeyHeader in
/-- With no port attribute, the actual key-stage entry retains the original port along with the derived header fields. -/
theorem original_request_key_entry_unchanged_port (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (selected : attrs.listenPort=none) :
    ∃ current,r.before.wg.device=some current ∧ Fields attrs d current ∧
      current.incomingPort=d.incomingPort :=
  RequestOrder.KeyHeader.certificate_key_no_port attrs initial result certificate r member key d device selected

open RequestOrder RequestOrder.KeyHeader in
/-- A selected nonzero port is the exact actual key-stage entry port; no successful-request or initial namespace premise is supplied. -/
theorem original_request_key_entry_selected_port (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (port : Nat) (selected : attrs.listenPort=some port) (nonzero : port≠0) :
    ∃ current,r.before.wg.device=some current ∧ Fields attrs d current ∧
      current.incomingPort=port :=
  RequestOrder.KeyHeader.certificate_key_nonzero_port attrs initial result certificate r member key d device port selected nonzero

open RequestOrder RequestOrder.KeyHeader in
/-- Zero-port selection at an actual completed key stage follows the original same/down or running allocation branch, with the actual ephemeral bounds. -/
theorem original_request_key_entry_zero_port (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (selected : attrs.listenPort=some 0) :
    ∃ current,r.before.wg.device=some current ∧ Fields attrs d current ∧
      ZeroPortRequestChoice d current.incomingPort :=
  RequestOrder.KeyHeader.certificate_key_zero_port attrs initial result certificate r member key d device selected


open AllowedIps Configuration in
/-- The original whole peer command retains actual allowed-IP completion order and exact normal or stopped outcome for arbitrary attributes. -/
theorem original_peer_command_allowed_ip_order (attrs : PeerAttrs) :
    Campaign2.Observes (setPeerCmd attrs) (fun _=>True)
      (fun entry outcome=>∃result:AllowedOrder.Inspection,result.outcome=outcome ∧ CommandOrder.Facts attrs entry result) :=
  CommandOrder.original_command_order attrs

open AllowedIps Configuration in
/-- The same whole peer command combines actual completion order with the original exact routing fold under explicit shape and initial routing premises. -/
theorem original_peer_command_routed_order (tables : FlatTable×FlatTable) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) :
    Campaign2.Observes (setPeerCmd attrs)
      (fun s=>RoutedView (s.wg.device.map routingState) tables)
      (fun entry outcome=>∃result:AllowedOrder.Inspection,result.outcome=outcome ∧
        CommandOrder.Facts attrs entry result ∧ AllowedOrder.RoutedFacts tables result) :=
  CommandOrder.original_command_routed_order tables attrs shape

open AllowedIps Configuration in
/-- A nonempty original routing history has one source-selected target and the requested or actual new-peer replacement mask; empty histories do not identify acquisition. -/
theorem original_peer_command_routing_selection (attrs : PeerAttrs) (entry : Campaign2.Snapshot) (result : AllowedOrder.Inspection)
    (facts : CommandOrder.Facts attrs entry result) (nonempty : result.completions≠[]) :
    ∃pid effective, CommandOrder.EffectiveFlags (attrs.flags.getD 0) effective ∧
      AllowedOrder.UpdatePartial attrs (some pid) effective pid result.completions ∧
      match result.outcome with
      | .error _=>True
      | .ok (ret,_)=>AllowedOrder.UpdateFinished attrs (some pid) effective pid result.completions ret :=
  CommandOrder.certificate_selected attrs entry result facts nonempty

open AllowedIps Configuration in
/-- Whole-command allowed-IP completions correspond to their actual input attributes. -/
theorem original_peer_command_allowed_ip_position (attrs : PeerAttrs) (entry : Campaign2.Snapshot)
    (result : AllowedOrder.Inspection) (facts : CommandOrder.Facts attrs entry result)
    (i : Nat) (e : RoutingCompletion) (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (AllowedOrder.allowedEvents result.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) :
    (attrs.allowedIps.getD [])[i]?=some (.attrs ip) :=
  CommandOrder.certificate_allowed_position attrs entry result facts i e pid ip ret selected call

open AllowedIps Configuration in
/-- A negative actual allowed-IP completion is last in the original whole peer command, including prefixes before later Stops. -/
theorem original_peer_command_allowed_ip_cutoff (attrs : PeerAttrs) (entry : Campaign2.Snapshot)
    (result : AllowedOrder.Inspection) (facts : CommandOrder.Facts attrs entry result)
    (i : Nat) (e : RoutingCompletion) (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (selected : (AllowedOrder.allowedEvents result.completions)[i]?=some e)
    (call : e.call=.allowedIp pid ip ret) (negative : ret<0) :
    i+1=(AllowedOrder.allowedEvents result.completions).length :=
  CommandOrder.certificate_negative_last attrs entry result facts i e pid ip ret selected call negative

open ScalarTail ScalarFinish PeerScalarRetention Queues.RxCredits Configuration in
/-- The actual tail derives selected residency and stamped scalars; negative allowed-IP results retain the old interval, while nonnegative finish applies the requested interval. -/
theorem original_acquired_tail_scalar_effect (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (expected : Cell) :
    Campaign2.Ensures (Configuration.peerConfigTailSource attrs (some paid.slot) paid.slot)
      (FinishInput cs loans paid expected)
      (fun result s=>Index.View.ConfigurationInput cs loans s ∧
        observation s paid.slot=some (tailCell attrs result expected)) :=
  ScalarTail.original_tail cs loans paid attrs expected

open ScalarTail ScalarFinish PeerScalarRetention Queues.RxCredits Configuration in
/-- The complete non-removal acquired update has exact PSK/full-endpoint and return-dependent keepalive effects, with final residency derived from its same reference account. -/
theorem original_acquired_update_scalar_effect (cs : Ledger) (loans : Reservations) (paid : Owner)
    (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (keep : flags &&& WGPEER_F_REMOVE_ME=0)
    (d : Device) (p : Peer) (resident : d.peers[paid.slot]?=some p)
    (member : paid.slot∈d.peerList) :
    Campaign2.Ensures (Configuration.peerConfigUpdateSource attrs (some paid.slot) flags psk paid.slot)
      (fun s=>Index.View.ConfigurationInput cs (paid::loans) s ∧ s.wg.device=some d)
      (fun result s=>Index.View.ConfigurationInput cs loans s ∧
        observation s paid.slot=some (tailCell attrs result (prefixCell p psk attrs.endpoint))) :=
  ScalarTail.original_update cs loans paid attrs flags psk keep d p resident member

open RequestOrder RequestOrder.FinalHeader in
/-- Every normal request with a completed key stage has the original name/index, selected mark, one generation increment and exact actual port-selection effect after arbitrary later peer attributes. -/
theorem original_request_final_header_fields (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r∈result.receipts) (key : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d) :
    ∃ current,final.wg.device=some current ∧ Fields attrs d current ∧
      PortSelected attrs d current.incomingPort :=
  RequestOrder.FinalHeader.certificate_final_fields attrs initial result certificate ret final normal r member key d device

open RequestOrder RequestOrder.FinalHeader in
/-- The normal final private key follows the original-entry unchanged-byte guard or clamping, together with exact final header and port fields. -/
theorem original_request_final_private_from_entry (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (key : Key) (given : attrs.privateKey=some key) :
    ∃ current,final.wg.device=some current ∧ Fields attrs d current ∧
      PortSelected attrs d current.incomingPort ∧
      current.staticIdentity.staticPrivate=
        if d.staticIdentity.staticPrivate=key then key else clamp key :=
  RequestOrder.FinalHeader.certificate_final_private cs loans attrs initial result certificate pre ret final normal r member kind d device key given

open RequestOrder RequestOrder.FinalHeader in
/-- Absent or unchanged private-key attributes retain the full original identity through a completed key stage and arbitrary later peer attributes. -/
theorem original_request_final_unchanged_identity (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (d : Device) (device : initial.wg.device=some d)
    (unchanged : attrs.privateKey=none ∨ attrs.privateKey=some d.staticIdentity.staticPrivate) :
    ∃ current,final.wg.device=some current ∧ Fields attrs d current ∧
      PortSelected attrs d current.incomingPort ∧ current.staticIdentity=d.staticIdentity :=
  RequestOrder.FinalHeader.certificate_final_unchanged_identity cs loans attrs initial result certificate pre ret final normal r member kind d device unchanged

open _root_.Leanux.Proofs.WG.Config.OwnerConfiguration Queues.RxCredits in
/-- A coherent original request entry and actual normal setter endpoint derive readable configured peers and allowed-IP nodes; no final readability predicate is assumed. -/
theorem original_request_normal_dump_readable (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (shape : Configuration.DeviceAddressShape attrs)
    (initial : Campaign2.Snapshot) (result : RequestOrder.Inspection)
    (certificate : RequestOrder.Certificate attrs initial result)
    (pre : ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot)
    (normal : result.outcome=.ok (ret,final))
    (d : Device) (present : final.wg.device=some d) : DeviceDumpReadable d :=
  OwnerConfiguration.certificate_dump_readable cs loans attrs shape initial result certificate pre ret final normal d present

open RequestOrder RequestOrder.FinalHeader Configuration in
/-- The actual sequential mixed key setter/getter returns original-entry header/private effects and exact JSON/cursor output, deriving readable data and transporting the initial selector/socket under explicit static page bounds. -/
theorem original_coherent_mixed_key_readback (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs)
    (initial : Campaign2.Snapshot) (inspected : Inspection)
    (certificate : Certificate attrs initial inspected)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (middle : Campaign2.Snapshot) (normal : inspected.outcome=.ok (ret,middle))
    (r : Receipt) (member : r∈inspected.receipts) (kind : r.kind=.keyStage)
    (before : Device) (first : initial.wg.device=some before)
    (selected : ClaimView.selectsDevice initial before)
    (key : Key) (given : attrs.privateKey=some key)
    (d : Device) (present : middle.wg.device=some d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : initial.wg.nlSock7.cbRunning=false) (emptyQueue : initial.wg.nlSock7.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096)
    (outcome : Campaign2.Outcome (Int × Except Int Lean.Json))
    (matched : ReadbackMatches attrs d initial inspected outcome) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    Fields attrs before d ∧ PortSelected attrs before d.incomingPort ∧
      d.staticIdentity.staticPrivate=
        (if before.staticIdentity.staticPrivate=key then key else clamp key) ∧
      ∃ final,outcome=.ok ((ret,.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d))),final) ∧
        final.wg.device=some (mixedPagesDevice d pages) ∧
        final.wg.nlSock7=socketReadbackFinal initial.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d pages) none :=
  RequestOrder.FinalHeader.certificate_coherent_mixed_readback cs loans attrs shape initial inspected certificate pre ret middle normal r member kind before first selected key given d present ready headerFits cursorData idle emptyQueue within outcome matched

open RequestOrder Configuration AllowedIps in
/-- Every completed peer receipt in the original mixed request has its own same-run nested routing inspection and exact outer input position; original Stops remain unchanged. -/
theorem original_request_nested_routing (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _=>True)
      (fun entry outcome=>∃result:Inspection,result.outcome=outcome ∧
        Certificate attrs entry result ∧ NestedCommands attrs result) :=
  RequestOrder.original_request_nested_commands attrs


open RequestOrder Configuration AllowedIps in
/-- A negative completed allowed-IP call determines the enclosing peer return and makes that peer the final completed peer command of the same request. -/
theorem original_request_nested_negative_cutoff (attrs : DeviceAttrs) (entry : Campaign2.Snapshot)
    (result : Inspection) (facts : Certificate attrs entry result)
    (i : Nat) (r : Receipt) (p : PeerAttrs)
    (selected : (peerReceipts result.receipts)[i]?=some r)
    (nested : AllowedOrder.Inspection) (point : PeerCommandFacts r p nested)
    (e : RoutingCompletion) (member : e∈AllowedOrder.allowedEvents nested.completions)
    (pid : PeerId) (ip : AllowedIpAttrs) (ret : Int)
    (call : e.call=.allowedIp pid ip ret) (negative : ret<0) :
    r.result=ret ∧ ∃before,peerReceipts result.receipts=before++[r] :=
  RequestOrder.certificate_nested_negative_peer_last attrs entry result facts i r p selected nested point e member pid ip ret call negative


open ScalarCommand PeerScalarRetention Queues.RxCredits Configuration in
/-- An existing selected peer has the exact stamped scalar result of the original public command; initial ownership supplies the reference funding and negative allowed-IP exits retain the prior interval. -/
theorem original_existing_peer_command_scalars (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>OwnerConfiguration.ProjectedEntry cs loans s ∧ s.wg.device=some before)
      (fun ret s=>Index.View.ConfigurationInput cs loans s ∧
        ∃ p,before.peers[pid]?=some p ∧
          observation s pid=some (ScalarTail.tailCell attrs ret
            (ScalarTail.prefixCell p attrs.presharedKey attrs.endpoint))) :=
  ScalarCommand.original_existing_command cs loans attrs key pid before pubkey valid protocol keep found


open RequestOrder RequestOrder.WgLinks in
/-- Completed key and peer receipts of the original request form an actual WireGuard-state chain; only a normal outcome identifies its endpoint with the final state. -/
theorem original_request_wireguard_receipt_links (attrs : DeviceAttrs) :
    Campaign2.Observes (wgSetDevice attrs) (fun _=>True)
      (fun initial outcome=>∃result:Inspection,result.outcome=outcome ∧
        Certificate attrs initial result ∧ Facts result) :=
  RequestOrder.WgLinks.original_request_wg_links attrs


open RequestOrder RequestOrder.WgLinks in
/-- The normal final WireGuard state is reached by the completed peer-receipt chain beginning at this request's completed key stage. -/
theorem original_request_final_peer_chain (attrs : DeviceAttrs) (initial : Campaign2.Snapshot)
    (result : Inspection) (certificate : Certificate attrs initial result)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (key : Receipt) (member : key∈result.receipts) (kind : key.kind=.keyStage) :
    Chain key.after.wg (peerReceipts result.receipts) final.wg :=
  RequestOrder.WgLinks.certificate_final_chain attrs initial result certificate ret final normal key member kind


open RequestOrder RequestOrder.FinalHeader in
/-- Arbitrary optional private-key attributes yield the original-entry retained or guarded-clamped private bytes, together with exact final header and port effects. -/
theorem original_request_optional_private_effect (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (final : Campaign2.Snapshot) (normal : result.outcome=.ok (ret,final))
    (r : Receipt) (member : r∈result.receipts) (kind : r.kind=.keyStage)
    (before : Device) (first : initial.wg.device=some before)
    (current : Device) (present : final.wg.device=some current) :
    Fields attrs before current ∧ PortSelected attrs before current.incomingPort ∧
      current.staticIdentity.staticPrivate=requestedPrivate attrs before :=
  RequestOrder.FinalHeader.certificate_requested_private cs loans attrs initial result certificate pre ret final normal r member kind before first current present


open RequestOrder RequestOrder.FinalHeader Configuration in
/-- The original mixed setter/getter pair with any optional private key returns exact requested header/key fields and serialized final data under explicit static pagination and socket bounds; readability is derived. -/
theorem original_coherent_mixed_request_readback (cs : Queues.RxCredits.Ledger)
    (loans : Queues.RxCredits.Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs)
    (initial : Campaign2.Snapshot) (inspected : Inspection)
    (certificate : Certificate attrs initial inspected)
    (pre : OwnerConfiguration.ProjectedEntry cs loans initial)
    (ret : Int) (middle : Campaign2.Snapshot) (normal : inspected.outcome=.ok (ret,middle))
    (r : Receipt) (member : r∈inspected.receipts) (kind : r.kind=.keyStage)
    (before : Device) (first : initial.wg.device=some before)
    (selected : ClaimView.selectsDevice initial before)
    (d : Device) (present : middle.wg.device=some d)
    (ready : MixedPageReady d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true})
    (headerFits : devicePrefixSpace d ≤ NLMSG_GOODSIZE)
    (cursorData : MixedPlanCursorData d
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready))
    (idle : initial.wg.nlSock7.cbRunning=false) (emptyQueue : initial.wg.nlSock7.queue=[])
    (within : mixedPageReceiveCount
      (mixedPages d (routingReadPeer d) (routingReadNode d)
        (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready) ≤ 4096)
    (outcome : Campaign2.Outcome (Int × Except Int Lean.Json))
    (matched : ReadbackMatches attrs d initial inspected outcome) :
    let pages := mixedPages d (routingReadPeer d) (routingReadNode d)
      (mixedInitialRows d (routingReadPeer d)) {hasWg:=true} ready
    Fields attrs before d ∧ PortSelected attrs before d.incomingPort ∧
      d.staticIdentity.staticPrivate=requestedPrivate attrs before ∧
      ∃ final,outcome=.ok ((ret,.ok (mixedGetterJson d (routingReadPeer d) (routingReadNode d))),final) ∧
        final.wg.device=some (mixedPagesDevice d pages) ∧
        final.wg.nlSock7=socketReadbackFinal initial.wg.nlSock7 d ∧
        CursorHeld d (mixedPagesDevice d pages) none :=
  RequestOrder.FinalHeader.certificate_requested_mixed_readback cs loans attrs shape initial inspected certificate pre ret middle normal r member kind before first selected d present ready headerFits cursorData idle emptyQueue within outcome matched

end Leanux.Proofs.WG.Config
