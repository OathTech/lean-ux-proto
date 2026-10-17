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


/-! Native source contracts lifted over all four former Kernel owners.
These are substantive return-value/WireGuard frames; the other owners are
preserved by the lift's type. Public projected claims remain in Statements. -/
namespace Leanux.Proofs.WG.Config.SourceClaims
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

private theorem lift_owners {α : Type} (action : WG.M α)
    (P : WGWorld → Prop) (Q : α → WGWorld → Prop)
    (R : FSWorld → TaskWorld → SeccompWorld → Prop) (proof : Ensures action P Q) :
    Product.Ensures (liftWG action)
      (fun w => P w.wg ∧ R w.fs w.tasks w.seccomp)
      (fun x w => Q x w.wg ∧ R w.fs w.tasks w.seccomp) := by
  intro entry result final pre run
  change ((action.run entry.wg).run entry.ambient >>= fun ((value, g), ambient) =>
    Except.ok (value, {entry with wg := g, ambient})) = _ at run
  cases actual : (action.run entry.wg).run entry.ambient with
  | error stop => rw [actual] at run; cases run
  | ok pair =>
    obtain ⟨⟨value, g⟩, ambient⟩ := pair
    rw [actual] at run
    cases run
    exact ⟨proof entry.wg entry.ambient result g ambient pre.1 actual, pre.2⟩

/-- Invalid allowed-IP family, length, prefix or missing attributes return
EINVAL and leave every former Kernel owner unchanged; records of the tests are still emitted. -/
theorem original_invalid_allowedip (pid : PeerId) (ip : AllowedIpAttrs)
    (invalid : ¬ validAllowedIp ip) (initial : WGWorld) (fs : FSWorld) (tasks : TaskWorld) (seccomp : SeccompWorld) :
    Product.Ensures (liftWG (setAllowedip pid ip)) (fun w => w.wg = initial ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp)
      (fun ret w => (ret = -EINVAL ∧ w.wg = initial) ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp) :=
  lift_owners _ _ _ (fun f t s => f = fs ∧ t = tasks ∧ s = seccomp) (setAllowedip_rejected pid ip invalid initial)


/-- With sufficient tailroom, the original allowed-IP dump emits exactly
its family/address/prefix fields, preserves every former Kernel owner and consumes their space. -/
theorem original_allowedip_dump (skb : NlSkb) (family masked cidr : Nat)
    (room : allowedIpSpace family ≤ skb.room) (initial : WGWorld) (fs : FSWorld) (tasks : TaskWorld) (seccomp : SeccompWorld) :
    Product.Ensures (liftWG (getAllowedips skb family masked cidr)) (fun w => w.wg = initial ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp)
      (fun result w => (w.wg = initial ∧ result =
        ({ skb with room := skb.room - allowedIpSpace family },
          some (Lean.Json.mkObj [("family", Lean.toJson family),
            ("addr", Lean.toJson (hexBE masked (if family = 6 then 16 else 4))),
            ("cidr", Lean.toJson cidr)]))) ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp) :=
  lift_owners _ _ _ (fun f t s => f = fs ∧ t = tasks ∧ s = seccomp) (getAllowedips_exact skb family masked cidr room initial)


/-- For a missing public key, valid remove or update-only requests return zero
and preserve every former Kernel owner on normal completion. -/
theorem original_absent_remove_update (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : WGWorld) (fs : FSWorld) (tasks : TaskWorld) (seccomp : SeccompWorld) (d : Device)
    (device : initial.dev = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (noCreate : flags &&& (WGPEER_F_REMOVE_ME ||| WGPEER_F_UPDATE_ONLY) ≠ 0) :
    Product.Ensures (liftWG (setPeerCmd a)) (fun w => w.wg = initial ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp)
      (fun ret w => (ret = 0 ∧ w.wg = initial) ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp) :=
  lift_owners _ _ _ (fun f t s => f = fs ∧ t = tasks ∧ s = seccomp) (setPeer_absent_remove_update a key flags initial d device missing pubkey flagattr valid protocol noCreate)


/-- An unknown peer flag with a supplied public key returns EOPNOTSUPP
and preserves every former Kernel owner on normal completion. -/
theorem original_invalid_peer_flags (a : PeerAttrs) (key : Key) (flags : UInt32)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (invalid : flags &&& ~~~WGPEER_F_ALL ≠ 0) (initial : WGWorld) (fs : FSWorld) (tasks : TaskWorld) (seccomp : SeccompWorld) :
    Product.Ensures (liftWG (setPeerCmd a)) (fun w => w.wg = initial ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp)
      (fun ret w => (ret = -EOPNOTSUPP ∧ w.wg = initial) ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp) :=
  lift_owners _ _ _ (fun f t s => f = fs ∧ t = tasks ∧ s = seccomp) (setPeer_invalid_flags a key flags pubkey flagattr invalid initial)


/-- A supplied unsupported protocol version, after valid flags, returns
EPFNOSUPPORT and preserves every former Kernel owner on normal completion. -/
theorem original_invalid_peer_protocol (a : PeerAttrs) (key : Key) (flags : UInt32)
    (version : Nat) (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = some version) (invalid : version ≠ 1)
    (initial : WGWorld) (fs : FSWorld) (tasks : TaskWorld) (seccomp : SeccompWorld) :
    Product.Ensures (liftWG (setPeerCmd a)) (fun w => w.wg = initial ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp)
      (fun ret w => (ret = -EPFNOSUPPORT ∧ w.wg = initial) ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp) :=
  lift_owners _ _ _ (fun f t s => f = fs ∧ t = tasks ∧ s = seccomp) (setPeer_invalid_protocol a key flags version pubkey flagattr valid protocol invalid initial)


/-- A valid request for the device identity, absent from the public-key table,
returns zero without changing any former Kernel owner on normal completion. -/
theorem original_absent_self_peer (a : PeerAttrs) (key : Key) (flags : UInt32)
    (initial : WGWorld) (fs : FSWorld) (tasks : TaskWorld) (seccomp : SeccompWorld) (d : Device)
    (device : initial.dev = some d)
    (missing : d.peerHashtable.find? (·.1 == key) = none)
    (pubkey : a.publicKey = some key) (flagattr : a.flags = some flags)
    (valid : flags &&& ~~~WGPEER_F_ALL = 0)
    (protocol : a.protocolVersion = none ∨ a.protocolVersion = some 1)
    (identity : d.staticIdentity.hasIdentity = true) (self : key = d.staticIdentity.staticPublic) :
    Product.Ensures (liftWG (setPeerCmd a)) (fun w => w.wg = initial ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp)
      (fun ret w => (ret = 0 ∧ w.wg = initial) ∧ w.fs = fs ∧ w.tasks = tasks ∧ w.seccomp = seccomp) :=
  lift_owners _ _ _ (fun f t s => f = fs ∧ t = tasks ∧ s = seccomp) (setPeer_absent_self a key flags initial d device missing pubkey flagattr valid protocol identity self)


end Leanux.Proofs.WG.Config.SourceClaims
