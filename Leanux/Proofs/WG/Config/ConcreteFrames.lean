import Leanux.Proofs.WG.Config.QuietRemoval
import Leanux.Proofs.WG.Config.PeerDead
import Leanux.Proofs.WG.Config.AllowedOwnerClear
import Leanux.Proofs.WG.Config.AllowedGeneralReplacement
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


/-! Concrete source-level contracts. Public WG projections live in Statements. -/
namespace Leanux.Proofs.WG.Config.SourceClaims
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


end Leanux.Proofs.WG.Config.SourceClaims
