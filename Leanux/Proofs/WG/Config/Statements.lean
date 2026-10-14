import Leanux.Proofs.WG.Config.Identity
import Leanux.Proofs.WG.Config.Port

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

end Leanux.Proofs.WG.Config
