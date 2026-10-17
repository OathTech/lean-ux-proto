import Leanux.Proofs.WG.Config.ClaimView
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Config.Identity
import Leanux.Proofs.WG.Config.Port
import Leanux.Proofs.WG.Config.RoundTrip
import Leanux.Proofs.WG.Config.DeviceScalars
import Leanux.Proofs.WG.Config.RoundTripReturns

/-! Configuration leaf claims over the campaign WireGuard projection. -/
namespace Leanux.Proofs.WG.Config.SourceClaims
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The private-key leaf clamps the stored key, uses generation's identity
flag, and retains the previous public bytes when the null-secret arm writes none. -/
theorem original_static_identity (key : Key) (d : Device) :
    Campaign2.Ensures (setStaticIdentityPrivateKey key) (fun w => w.wg.device = some d)
      (fun _ w => w.wg.device = some { d with staticIdentity := identityAfter key d.staticIdentity }) :=
  setStaticIdentity_exact key d


/-- Static-static precomputation updates exactly the resident peer's DH
field; absent identity or a null result stores 32 zero bytes. -/
theorem original_static_precomputation (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (precomputeStaticStatic pid) (fun w => w.wg.device = some d)
      (fun _ w => w.peerAt pid = some
        { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p }) :=
  precomputeStaticStatic_exact pid d p resident


/-- A normal listen-port update while down stores the requested port and
preserves both socket pointers and down status; it may clear endpoint caches. -/
theorem original_down_port (port old : Nat) (sock4 sock6 : Option Nat) :
    Campaign2.Ensures (setPort port)
      (fun w => ClaimView.portState w.wg.toCore = some (old, sock4, sock6, false))
      (fun ret w => ret = 0 ∧ ClaimView.portState w.wg.toCore = some (port, sock4, sock6, false)) :=
  setPort_down port old sock4 sock6


/-- At the acquired-peer stage, removal takes precedence over every
attribute update; the equation includes the subsequent peer put. -/
theorem original_acquired_remove_precedence (a : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) (remove : flags &&& WGPEER_F_REMOVE_ME ≠ 0) :
    peerConfigUpdateSource a peer flags psk pid = (do
      _ ← branch .peerRemoveMe true
      peerRemove peer
      peerPut peer
      _ ← branch .peerZeroPsk a.presharedKey.isSome
      pure 0) :=
  peerUpdate_remove_source a peer flags psk pid remove


/-- The validation, lookup and acquired-peer stages used above are exactly
the original peer setter, including every return and Stop. -/
theorem original_peer_set_source (a : PeerAttrs) : setPeerCmdSource a = setPeerCmd a :=
  setPeerCmd_source a


/-- For an existing peer with positive reference count while down, normal completion stores the
preshared key and keepalive interval through the exact device updates. -/
theorem original_peer_scalars_down (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (down : d.running = false) :
    Campaign2.Ensures (setPeerCmd (scalarAttrs key psk interval)) (fun w => w.wg.device = some d)
      (fun ret w => ret = 0 ∧ w.wg.device = some (scalarDevice d pid p psk interval)) :=
  setPeer_scalars_down key psk interval pid d p found resident live down


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
  getPeerDump_no_allowedips pid p ctx skb fresh empty room


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
  scalars_get_after_set key psk interval pid d p ctx skb found resident live down fresh empty room


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
  setDevice_partial d key psk interval pid p found resident live bounded down


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
  partial_get_after_set d key psk interval pid p ctx skb found resident live bounded down fresh empty room


/-- The stopped-device scalar setter returns normally and establishes the
exact device update when the peer reference count is positive and cannot overflow. -/
theorem original_peer_scalars_return (key psk : Key) (interval : Nat) (pid : PeerId)
    (d : Device) (p : Peer)
    (found : d.peerHashtable.find? (·.1 == key) = some (key, pid))
    (resident : d.peers[pid]? = some p) (live : 0 < p.refcount) (bounded : p.refcount + 1 < 2 ^ 31) (down : d.running = false) :
    Campaign2.Returns (setPeerCmd (scalarAttrs key psk interval)) (fun w => w.wg.device = some d)
      (fun ret w => ret = 0 ∧ w.wg.device = some (scalarDevice d pid p psk interval)) :=
  setPeer_scalars_down_returns key psk interval pid d p found resident live bounded down


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
  scalars_get_after_set_returns key psk interval pid d p ctx skb found resident live bounded down fresh empty room


end Leanux.Proofs.WG.Config.SourceClaims
