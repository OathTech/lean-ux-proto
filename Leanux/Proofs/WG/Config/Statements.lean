import Leanux.Proofs.WG.Config.Identity
import Leanux.Proofs.WG.Config.Port
import Leanux.Proofs.WG.Config.RoundTrip
import Leanux.Proofs.WG.Config.DeviceScalars
import Leanux.Proofs.WG.Config.RoundTripReturns
import Leanux.Proofs.WG.Config.Fwmark
import Leanux.Proofs.WG.Config.ClearedSources
import Leanux.Proofs.WG.Config.SocketPorts
import Leanux.Proofs.WG.Config.FwmarkEffects
import Leanux.Proofs.WG.Config.DevicePorts
import Leanux.Proofs.WG.Config.RandomPort
import Leanux.Proofs.WG.Config.ZeroPort
import Leanux.Proofs.WG.Config.RecordedPort
import Leanux.Proofs.WG.Config.ExpiryEffects
import Leanux.Proofs.WG.Config.ExpiryClock
import Leanux.Proofs.WG.Config.KeyInstall
import Leanux.Proofs.WG.Config.KeyInstallEffects
import Leanux.Proofs.WG.Config.DumpCancellation
import Leanux.Proofs.WG.Config.KeyRequest
import Leanux.Proofs.WG.Config.Getter
import Leanux.Proofs.WG.Config.ScalarGetter

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- Invalid allowed-IP family, length, prefix or missing attributes return
EINVAL and leave the kernel unchanged; records of the tests are still emitted. -/
theorem original_invalid_allowedip (pid : PeerId) (ip : AllowedIpAttrs)
    (invalid : ¬ validAllowedIp ip) (initial : Kernel) :
    Ensures (setAllowedip pid ip) (fun w => w.k = initial)
      (fun ret w => ret = -EINVAL ∧ w.k = initial) :=
  setAllowedip_rejected pid ip invalid initial

/-- With sufficient tailroom, the original allowed-IP dump emits exactly
its family/address/prefix fields, preserves the kernel and consumes their space. -/
theorem original_allowedip_dump (skb : NlSkb) (family masked cidr : Nat)
    (room : allowedIpSpace family ≤ skb.room) (initial : Kernel) :
    Ensures (getAllowedips skb family masked cidr) (fun w => w.k = initial)
      (fun result w => w.k = initial ∧ result =
        ({ skb with room := skb.room - allowedIpSpace family },
          some (Lean.Json.mkObj [("family", Lean.toJson family),
            ("addr", Lean.toJson (hexBE masked (if family = 6 then 16 else 4))),
            ("cidr", Lean.toJson cidr)]))) :=
  getAllowedips_exact skb family masked cidr room initial

/-- The private-key leaf clamps the stored key, uses generation's identity
flag, and retains the previous public bytes when the null-secret arm writes none. -/
theorem original_static_identity (key : Key) (d : Device) :
    Ensures (setStaticIdentityPrivateKey key) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with staticIdentity := identityAfter key d.staticIdentity }) :=
  setStaticIdentity_exact key d

/-- Static-static precomputation updates exactly the resident peer's DH
field; absent identity or a null result stores 32 zero bytes. -/
theorem original_static_precomputation (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (precomputeStaticStatic pid) (fun w => w.k.wg = some d)
      (fun _ w => peerAt w pid = some
        { p with precomputedStaticStatic := precomputedAfter d.staticIdentity p }) :=
  precomputeStaticStatic_exact pid d p resident

/-- A normal listen-port update while down stores the requested port and
preserves both socket pointers and down status; it may clear endpoint caches. -/
theorem original_down_port (port old : Nat) (sock4 sock6 : Option Nat) :
    Ensures (setPort port)
      (fun w => portState w.k = some (old, sock4, sock6, false))
      (fun ret w => ret = 0 ∧ portState w.k = some (port, sock4, sock6, false)) :=
  setPort_down port old sock4 sock6

/-- For a missing public key, valid remove or update-only requests return zero
and preserve the kernel on normal completion. -/
theorem original_absent_remove_update (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : Kernel) (d : Device)
    (device : initial.wg = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (noCreate : flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) ≠ 0) :
    Ensures (setPeerCmd a) (fun w => w.k = initial)
      (fun ret w => ret = 0 ∧ w.k = initial) :=
  setPeer_absent_remove_update a key flags initial d device missing pubkey flagattr valid protocol noCreate

/-- An unknown peer flag with a supplied public key returns EOPNOTSUPP
and preserves the kernel on normal completion. -/
theorem original_invalid_peer_flags (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (invalid : flags &&& ~~~WGPEER_F_ALL ≠ 0) (initial : Kernel) :
    Ensures (setPeerCmd a) (fun w => w.k = initial)
      (fun ret w => ret = -EOPNOTSUPP ∧ w.k = initial) :=
  setPeer_invalid_flags a key flags pubkey flagattr invalid initial

/-- A supplied unsupported protocol version, after valid flags, returns
EPFNOSUPPORT and preserves the kernel on normal completion. -/
theorem original_invalid_peer_protocol (a : PeerAttrs) (key : Key) (flags : UInt32)
    (version : Nat) (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = some version) (invalid : version ≠ 1)
    (initial : Kernel) :
    Ensures (setPeerCmd a) (fun w => w.k = initial)
      (fun ret w => ret = -EPFNOSUPPORT ∧ w.k = initial) :=
  setPeer_invalid_protocol a key flags version pubkey flagattr valid protocol invalid initial

/-- A valid request for the device identity, absent from the public-key table,
returns zero without changing the kernel on normal completion. -/
theorem original_absent_self_peer (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : Kernel) (d : Device)
    (device : initial.wg = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (identity : d.staticIdentity.hasIdentity = true) (self : key = d.staticIdentity.staticPublic) :
    Ensures (setPeerCmd a) (fun w => w.k = initial)
      (fun ret w => ret = 0 ∧ w.k = initial) :=
  setPeer_absent_self a key flags initial d device missing pubkey flagattr valid protocol identity self

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
    Ensures (setPeerCmd (scalarAttrs key psk interval)) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some (scalarDevice d pid p psk interval)) :=
  setPeer_scalars_down key psk interval pid d p found resident live down

/-- For a resident peer without allowed IPs, a fresh peer chunk with at least 168 bytes of
room serializes its fixed fields and preserves that peer on normal completion. -/
theorem original_fresh_peer_dump (pid : PeerId) (p : Peer) (ctx : DumpCtx) (skb : NlSkb)
    (fresh : ctx.nextAllowedip = none) (empty : p.allowedipsList = [])
    (room : 168 ≤ skb.room) :
    Ensures (getPeerDump pid ctx skb) (fun w => peerAt w pid = some p)
      (fun result w => peerAt w pid = some p ∧ result =
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
    Ensures (do
      let ret ← setPeerCmd (scalarAttrs key psk interval)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun w => w.k.wg = some d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        peerAt w pid = some updated ∧ result =
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
    Returns (wgSetDevice (partialAttrs d key psk interval))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = -EINVAL ∧ w.k.wg = some
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
    Returns (do
      let ret ← wgSetDevice (partialAttrs d key psk interval)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        peerAt w pid = some updated ∧ result =
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
    Returns (setPeerCmd (scalarAttrs key psk interval)) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ w.k.wg = some (scalarDevice d pid p psk interval)) :=
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
    Returns (do
      let ret ← setPeerCmd (scalarAttrs key psk interval)
      let dump ← getPeerDump pid ctx skb
      pure (ret, dump))
      (fun w => w.k.wg = some d)
      (fun result w =>
        let updated := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        peerAt w pid = some updated ∧ result =
          (0, { skb with room := skb.room - peerFixedSpace updated },
           { ctx with nextAllowedip := none, allowedipsSeq := 0 },
           .complete { publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs updated })) :=
  scalars_get_after_set_returns key psk interval pid d p ctx skb found resident live bounded down fresh empty room

/-- Clearing a resident peer zeroes its cached local source addresses and
drops its cached destination; only the cache reset timestamp is unspecified.
Other peer entries and all other device fields are preserved on normal completion. -/
theorem original_endpoint_source_clear (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (clearPeerEndpointSrc pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ d' reset, w.k.wg = some d' ∧
        d' = { d with peers := d'.peers } ∧
        d'.peers[pid]? = some (clearedSource p reset) ∧
        ∀ q, q ≠ pid → d'.peers[q]? = d.peers[q]?) :=
  clearEndpointSource_exact pid d p resident

/-- On normal completion, a fwmark-only outer set writes the mark and increments
the generation, preserving every other device field outside the peer store.
The creating namespace exists and the request selects this device by index. -/
theorem original_fwmark_device_frame (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 })) :=
  setDevice_fwmark_frame d mark net

/-- On normal completion, a fwmark-only outer set clears local endpoint
sources and cached destination slots for every peer in the device list.
It also writes the mark, increments generation and frames other device fields. -/
theorem original_fwmark_clears_listed_peers (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        sourcesClear w.k d.peerList) :=
  setDevice_fwmark_sources d mark net

/-- Socket replacement returns normally, installs both supplied socket
pointers, and takes the incoming port from the supplied IPv4 socket,
preserving it when that socket is absent.
Every other device field is preserved. -/
theorem original_socket_reinit (new4 new6 : Option Nat) (d : Device) :
    Returns (socketReinit new4 new6) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some
        { d with sock4 := new4, sock6 := new6, incomingPort := new4.getD d.incomingPort }) :=
  socketReinit_returns new4 new6 d

/-- With an existing creating namespace and a nonzero requested port,
socket initialization returns normally: a conflict returns EADDRINUSE with
the device unchanged; otherwise both sockets and the incoming port are replaced. -/
theorem original_nonzero_socket_init (port : Nat) (nonzero : port ≠ 0)
    (d : Device) (bound : Bool) (net : d.creatingNet = true) :
    Returns (socketInit port) (fun w => w.k.wg = some d ∧ w.portBound port = bound)
      (fun ret w => if bound || d.sock4 == some port || d.sock6 == some port
        then ret = -EADDRINUSE ∧ w.k.wg = some d
        else ret = 0 ∧ w.k.wg = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) :=
  socketInit_nonzero_returns port nonzero d bound net

/-- On normal completion, a fwmark-only outer set changes each listed peer
only by clearing local source addresses and its cached destination and possibly
updating the cache-reset timestamp. Unlisted peer entries are unchanged.
The mark/generation writes and every other device field are also specified. -/
theorem original_fwmark_peer_store_effects (d : Device) (mark : Nat) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (fwmarkAttrs d mark))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg.map withoutPeers = some
        (withoutPeers { d with fwmark := mark, deviceUpdateGen := d.deviceUpdateGen + 1 }) ∧
        clearedPeers d w.k d.peerList) :=
  setDevice_fwmark_effects d mark net

/-- A nonzero port request equal to the current port preserves the device.
Otherwise every listed peer has its local source/cache cleared, including when
socket initialization returns an error; the non-peer device fields have the
specified stopped/running, namespace and bind-conflict outcome. This contract
concerns normal completion. -/
theorem original_nonzero_port_effects (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (bound : Nat → Bool) :
    Ensures (setPort port) (fun w => w.k.wg = some d ∧ w.portBound = bound)
      (fun ret w => if d.incomingPort = port then ret = 0 ∧ w.k.wg = some d
        else ret = (portOutcome d port bound).1 ∧
          w.k.wg.map withoutPeers = some (withoutPeers (portOutcome d port bound).2) ∧
          clearedPeers d w.k d.peerList) :=
  setPort_nonzero_effects d port nonzero bound

/-- A port-only outer configuration request increments the device generation.
For a nonzero port, it then has exactly the set_port effects, including retained
source/cache clearing on a bind error. The namespace exists; normal completion
is assumed. -/
theorem original_device_nonzero_port (d : Device) (port : Nat) (nonzero : port ≠ 0)
    (net : d.creatingNet = true) (bound : Nat → Bool) :
    Ensures (wgSetDevice (portAttrs d port))
      (fun w => w.k.wg = some d ∧ selectsDevice w d ∧ w.portBound = bound)
      (fun ret w =>
        let updated := { d with deviceUpdateGen := d.deviceUpdateGen + 1 }
        if d.incomingPort = port then ret = 0 ∧ w.k.wg = some updated
        else ret = (portOutcome updated port bound).1 ∧
          w.k.wg.map withoutPeers = some (withoutPeers (portOutcome updated port bound).2) ∧
          clearedPeers d w.k d.peerList) :=
  setDevice_port_nonzero d port nonzero net bound

/-- On normal completion in an existing namespace, port-zero initialization
installs both sockets at the same selected port in the configured local range,
preserving every other device field. -/
theorem original_zero_socket_range (d : Device) (net : d.creatingNet = true) :
    Ensures (socketInit 0) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ ∃ port,
        LOCAL_PORT_LOW ≤ port ∧ port ≤ LOCAL_PORT_HIGH ∧ w.k.wg = some
          { d with sock4 := some port, sock6 := some port, incomingPort := port }) :=
  socketInit_zero d net

/-- With an explicit correctly padded UDP draw at the head of the records,
an existing namespace and a free first candidate, port-zero initialization
returns normally and installs exactly the port computed from the four draw
bytes. Other device fields are preserved. -/
theorem original_zero_socket_record_return (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) :
    Returns (socketInit 0)
      (fun w => w.k.wg = some d ∧
        w.hidden = some (udpDrawRecord a b c e :: rest) ∧ w.portBound (drawnPort a b c e) = false)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e }) :=
  socketInit_zero_record_returns d net a b c e rest free4 free6

/-- In an existing namespace, normal completion of a port-zero request
returns zero. An existing zero port is a no-op; otherwise listed peer sources
and caches are cleared, a stopped device stores zero, and a running device
installs both sockets at a port within the local range. Other fields are framed. -/
theorem original_zero_port_effects (d : Device) (net : d.creatingNet = true) :
    Ensures (setPort 0) (fun w => w.k.wg = some d)
      (fun ret w => ret = 0 ∧ zeroPortEffects d w) :=
  setPort_zero_effects d net

/-- A port-zero outer configuration request in an existing namespace
increments the device generation and has the specified no-op, stopped-device,
or running-allocation effects on normal completion. -/
theorem original_device_zero_port (d : Device) (net : d.creatingNet = true) :
    Ensures (wgSetDevice (portAttrs d 0))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ zeroPortEffects
        { d with deviceUpdateGen := d.deviceUpdateGen + 1 } w) :=
  setDevice_port_zero d net

/-- An explicit free first-candidate draw in an existing namespace guarantees
socket initialization returns normally and installs the computed port. It consumes exactly the head
draw record and preserves the remaining record list through socket replacement. -/
theorem original_zero_socket_record_tail (d : Device) (net : d.creatingNet = true)
    (a b c e : UInt8) (rest : List HiddenRecord)
    (free4 : d.sock4 ≠ some (drawnPort a b c e))
    (free6 : d.sock6 ≠ some (drawnPort a b c e)) :
    Returns (socketInit 0)
      (fun w => w.k.wg = some d ∧
        w.hidden = some (udpDrawRecord a b c e :: rest) ∧ w.portBound (drawnPort a b c e) = false)
      (fun ret w => ret = 0 ∧ w.k.wg = some
        { d with sock4 := some (drawnPort a b c e), sock6 := some (drawnPort a b c e), incomingPort := drawnPort a b c e } ∧
        w.hidden = some rest) :=
  socketInit_zero_record_tail_returns d net a b c e rest free4 free6

/-- With an explicit draw whose first candidate is occupied, socket
initialization stops at the mirror's declared domain boundary with its collision
message. This describes the modeled-domain stop, not a kernel bind error or
a claim about the kernel's collision retry behavior. -/
theorem original_zero_socket_collision_stop (w : World) (d : Device) (a b c e : UInt8)
    (rest : List HiddenRecord) (device : w.k.wg = some d) (net : d.creatingNet = true)
    (records : w.hidden = some (udpDrawRecord a b c e :: rest))
    (collision : (w.portBound (drawnPort a b c e) ||
      d.sock4 == some (drawnPort a b c e) || d.sock6 == some (drawnPort a b c e)) = true) :
    ∃ site, (socketInit 0).run w = .error
      (.outsideDomain site "the random port draw collides with a bound port") :=
  socketInit_zero_collision w d a b c e rest device net records collision

/-- Cookie-key precomputation returns normally. It changes only the device
cookie-encryption and MAC1 keys, to the specified public-key hashes when identity
exists and to zero otherwise. -/
theorem original_cookie_precomputation_return (d : Device) :
    Returns cookiePrecomputeDeviceKeys (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (cookieKeysAfter d)) :=
  cookiePrecompute_returns d

/-- Identity installation returns normally, clamps the private bytes and
sets the public identity as specified, preserving all other device fields. -/
theorem original_identity_install_return (key : Key) (d : Device) :
    Returns (setStaticIdentityPrivateKey key) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some { d with staticIdentity := identityAfter key d.staticIdentity }) :=
  setStaticIdentity_returns key d

/-- A private-key-only request equal byte-for-byte to the stored private key
returns normally and changes only the device generation. Equality is against
the raw request, not a normalized equivalence class of keys. -/
theorem original_unchanged_private_key_return (d : Device) (key : Key)
    (same : d.staticIdentity.staticPrivate = key) :
    Returns (wgSetDevice (privateKeyAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ w.k.wg = some { d with deviceUpdateGen := d.deviceUpdateGen + 1 }) :=
  setDevice_private_unchanged d key same

/-- Static-static precomputation for a resident peer returns normally with
the exact ordered peer-store updates, including the intermediate DH write
before zeroing a null result. All surrounding device fields are preserved. -/
theorem original_static_precomputation_return (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (precomputeStaticStatic pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (precomputeDevice d pid p)) :=
  precomputeStaticStatic_returns pid d p resident

/-- Normal completion of expiry removes the peer's handshake entries, zeros
handshake fields, preserves its slots, and invalidates next/current sending keys.
The exact store transformation preserves all other fields except last-sent time.
Its existential clock parameter does not constrain that time or prove clock-read
provenance. Missing keypair targets can stop; no return guarantee is claimed. -/
theorem original_expiry_store_effects (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (expireCurrentPeerKeypairs pid) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some (expiredDevice d pid p now)) :=
  expireCurrent_exact pid d p resident

/-- On normal completion, expiry changes only sending validity in current
and next keypair entries. Every other keypair field and lookup is preserved.
Aliased slots are covered by the union of the two target identities. -/
theorem original_expiry_keypair_fields (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (q : KeypairId) :
    Ensures (expireCurrentPeerKeypairs pid) (fun w => w.k.wg = some d)
      (fun _ w => (w.k.wg.bind fun dev => dev.keypairs[q]?) = (d.keypairs[q]?).map fun k =>
        if p.keypairNext = some q ∨ p.keypairCurrent = some q then
          { k with sending := { k.sending with isValid := false } } else k) := by
  intro w ret v hp hr
  obtain ⟨now, hv⟩ := expireCurrent_exact pid d p resident w ret v hp hr
  simpa [hv] using expiredDevice_keypair d pid p now q

/-- Every normally completed original expiry run has an actual prefix and
reset-clock read whose returned value determines the final store, including
last-sent time minus six seconds in wrapping Int64 arithmetic. The read is tied
to that run; this is not merely an unconstrained existential timestamp. -/
theorem original_expiry_clock_relation (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (w v : World) (device : w.k.wg = some d)
    (run : (expireCurrentPeerKeypairs pid).run w = .ok ((), v)) :
    ∃ now before after,
      (expiryReadPrefix pid).run w = .ok ((), before) ∧
      (hiddenClock64 .resetLastSent).run before = .ok (now, after) ∧
      v.k.wg = some (expiredDevice d pid p now) :=
  expireCurrent_clock pid d p resident w v device run

/-- Exact source equality exposing identity installation and the peer-list
loop after optional self-peer removal, before later peer attributes. This is
unconditional; the effects below separately require normal completion. -/
theorem original_private_key_factor (a : DeviceAttrs) :
    deviceKeyFactoredSource a = deviceKeySource a :=
  deviceKey_loop_factor a

/-- With staged sending disabled, a completed peer update precomputes its
static-static value and performs the exact expiry store transformation. The
clock here is existential; the stronger per-expiry read relation is separate. -/
theorem original_quiet_key_peer (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (keyPeerSource pid false) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some (peerUpdatedDevice d pid p now)) :=
  keyPeer_quiet_exact pid d p resident

/-- A completed quiet peer-list loop has the ordered relational effects of
each resident peer update. Repeated peers and aliased keypair slots are allowed;
missing peers or hidden inputs may stop, so this is not a return guarantee. -/
theorem original_quiet_key_peer_loop (pids : List PeerId) (d : Device) :
    Ensures (keyPeerLoopSource pids false) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ KeyPeerUpdates d pids final) :=
  keyPeerLoop_quiet pids d

/-- The quiet installation block sets identity and cookie keys, then applies
ordered precomputation/expiry to its snapshotted peer list. The initial device
is after optional collision removal; later peer attributes are outside this
block. Normal completion is assumed, and clock values remain existential. -/
theorem original_quiet_key_install (d : Device) (key : Key)
    (quiet : requestsStagedSend d key = false) :
    Ensures (keyInstallSource key) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        KeyPeerUpdates (installedDevice d key) d.peerList final) :=
  keyInstall_quiet d key quiet

/-- The original non-retry handshake queue call resets attempts, reads the
age-test clock, and has the exact Device effect selected by that actual read:
no queue change, a balanced pending reference pair, or a fresh queued reference.
World bookkeeping and record availability are outside this normal-run claim. -/
theorem original_queued_handshake_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (w v : World) (device : w.k.wg = some d)
    (run : (sendQueuedHandshakeInitiation pid false).run w = .ok ((), v)) :
    ∃ now before after,
      (queuedReadPrefix pid).run w = .ok ({ p with timerHandshakeAttempts := 0 }, before) ∧
      (hiddenClock64 .birthdateExpired).run before = .ok (now, after) ∧
      v.k.wg = some (queuedDevice (withPeer d pid { p with timerHandshakeAttempts := 0 })
        pid { p with timerHandshakeAttempts := 0 } now) :=
  sendQueued_clock pid d p resident w v device run

/-- Original staging with absent or invalid current sending material either
returns unchanged for an empty staged list, or restores packets and has the
specified handshake-queue Device effects. Temporary key references preserve
lookups. Dangling current slots cannot complete with nonempty staging. Clock
values here are existential; World bookkeeping and record consumption are not
characterized, and no return guarantee is claimed. -/
theorem original_staged_invalid_key (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (invalid : ∀ id k, p.keypairCurrent = some id → d.keypairs[id]? = some k → k.sending.isValid = false) :
    Ensures (sendStagedPackets pid) (fun w => w.k.wg = some d)
      (fun _ w => if p.staged = [] then w.k.wg = some d
        else ∃ now, w.k.wg = some (invalidStagedDevice d pid p now)) :=
  staged_invalid pid d p resident invalid

/-- Both branches of the original key-update peer body have the specified
Device effects: precomputation, expiry, and optional staged-packet restoration
and handshake queueing. The clocks are existential and completion is assumed. -/
theorem original_key_peer_effects (pid : PeerId) (d : Device) (p : Peer) (sendStaged : Bool)
    (resident : d.peers[pid]? = some p) :
    Ensures (keyPeerSource pid sendStaged) (fun w => w.k.wg = some d)
      (fun _ w => ∃ expiryNow queueNow,
        w.k.wg = some (keyPeerDevice d pid p expiryNow sendStaged queueNow)) :=
  keyPeer_complete pid d p sendStaged resident

/-- The original peer-list loop realizes the ordered Device relation for
both staged-send settings. Repeated peers and keypair aliases are permitted.
This normal-completion result does not assert aggregate clock provenance. -/
theorem original_key_peer_loop_effects (pids : List PeerId) (d : Device) (sendStaged : Bool) :
    Ensures (keyPeerLoopSource pids sendStaged) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧ KeyPeerRun sendStaged d pids final) :=
  keyPeerLoop_complete pids d sendStaged

/-- The installation block composes identity and cookie keys with the full
snapshotted peer-list relation, using the code's staged-send condition. The
baseline is after optional self-peer removal and before later peer attributes;
this is a Device-state normal-completion contract for that block. -/
theorem original_key_install_effects (d : Device) (key : Key) :
    Ensures (keyInstallSource key) (fun w => w.k.wg = some d)
      (fun _ w => ∃ final, w.k.wg = some final ∧
        KeyPeerRun (requestsStagedSend d key) (installedDevice d key) d.peerList final) :=
  keyInstall_complete d key

/-- A single empty-device getter is accepted from the runner's ordinary
fixture with an empty hidden record list. This establishes reachability of the
cancelled-nest accounting case, not a changed external observation. -/
theorem empty_dump_trace_accepted : DumpCancellation.accepted = true :=
  DumpCancellation.emptyTrace_accepted

/-- The original empty-device dump callback completes with one message,
a cleared cursor and 3720 bytes of tailroom. This retains the cancelled nest's
four bytes; the source correspondence discrepancy is recorded in request 3. -/
theorem original_empty_dump_room : DumpCancellation.callbackResult = some (0, 3720, true, 1) :=
  DumpCancellation.emptyDump_room

/-- The C-derived accounting of the retained header and attributes leaves
3724 bytes, exactly one cancelled nest header more than the mirror witness.
This is arithmetic supporting the source review, not a formal C simulation. -/
theorem empty_dump_cancellation_accounting :
    DumpCancellation.cancelledNestRoom = 3724 ∧ 3720 + nlaTotal 0 = DumpCancellation.cancelledNestRoom :=
  DumpCancellation.cancellation_accounting

/-- A changed private-key-only outer request with no generated-public-key
peer-table match returns zero on normal completion, increments generation, and
performs the full installation relation including optional staged sending.
The raw request differs from the stored key; no peer-removal arm is taken.
This does not guarantee input records or establish aggregate clock provenance. -/
theorem original_private_key_request_no_collision (d : Device) (key : Key)
    (changed : d.staticIdentity.staticPrivate ≠ key) (absent : noKeyCollision d key) :
    Ensures (wgSetDevice (privateKeyAttrs d key))
      (fun w => w.k.wg = some d ∧ selectsDevice w d)
      (fun ret w => ret = 0 ∧ ∃ final, w.k.wg = some final ∧
        KeyPeerRun (requestsStagedSend d key) (installedDevice (requestGeneration d) key) d.peerList final) :=
  setDevice_private_changed_no_collision d key changed absent

/-- A fresh original callback for one resident peer without allowed IPs
returns all fixed device and peer attributes, completes its cursor and preserves
the device. The bound reserves room for the transport's final DONE message. -/
theorem original_single_peer_dump_callback (pid : PeerId) (d : Device) (p : Peer)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump { hasWg := true } 0 {}) (fun w => w.k.wg = some d)
      (fun result w => result = singlePeerDump d p ∧ w.k.wg = some d) :=
  wgGetDeviceDump_single pid d p peers resident empty room

/-- The original public getter for one resident peer without allowed IPs
returns exact canonical JSON, including the empty allowed-IP array, preserves
the device and leaves socket 7 drained and finished. The socket starts idle
with an empty queue; its bound flag is unrestricted. This is a total-return
contract for one complete chunk, not a multipart snapshot theorem. -/
theorem original_single_peer_getter (pid : PeerId) (d : Device) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (wgGetDevice (byIndex d))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock ∧ selectsDevice w d)
      (fun result w => result = .ok (singlePeerJson d p) ∧ w.k.wg = some d ∧
        w.k.nlSock7 = { completedSock sock d p with queue := [] }) :=
  wgGetDevice_single pid d p sock peers resident noIps room idle empty

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
    Returns (do
      let ret ← wgSetDevice (scalarDeviceAttrs d key psk interval bad)
      let dump ← wgGetDevice (byIndex d)
      pure (ret, dump))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock ∧ selectsDevice w d)
      (fun result w =>
        let updated := scalarRequestDevice d pid p psk interval
        let configured := { p with presharedKey := psk, persistentKeepaliveInterval := interval }
        result = ((if bad then -EINVAL else 0), .ok (singlePeerJson updated configured)) ∧
          w.k.wg = some updated ∧
          w.k.nlSock7 = { completedSock sock updated configured with queue := [] }) :=
  scalar_outer_get_after_set d key psk interval bad pid p sock peers found resident live bounded
    down noIps room idle empty

end Leanux.Proofs.WG.Config
