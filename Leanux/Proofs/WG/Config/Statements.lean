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
    rfl
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
    rfl
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

end Leanux.Proofs.WG.Config
