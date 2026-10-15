import Layouts
import Memory

namespace Binary.EndpointHeap
open Leanux.WG

def little (memory : Mem 64) (address : BitVec 64) (width : Nat) : Option Nat :=
  (memory.loadBytes address width).map (fun bytes => bytes.foldr (fun b n => n * 256 + b.toNat) 0)

def big (memory : Mem 64) (address : BitVec 64) (width : Nat) : Option Nat :=
  (memory.loadBytes address width).map (fun bytes => bytes.foldl (fun n b => n * 256 + b.toNat) 0)

/-- Outer none rejects unmapped active fields or an unsupported family;
    some none is exactly AF_UNSPEC. Inactive union bytes are never read.
    IPv4 scope/flow and IPv6 srcIf are abstraction defaults, not zero bytes. -/
def decode (memory : Mem 64) (base : BitVec 64) : Option (Option Endpoint) := do
  let family ← little memory (base + .ofNat 64 (Layouts.endpoint_addr + Layouts.sockaddr_sa_family)) 2
  match family with
  | 0 => return none
  | 2 =>
    let port ← big memory (base + .ofNat 64 (Layouts.endpoint_addr4 + Layouts.sockaddr4_sin_port)) 2
    let addr ← big memory (base + .ofNat 64 (Layouts.endpoint_addr4 + Layouts.sockaddr4_sin_addr)) 4
    let src ← big memory (base + .ofNat 64 Layouts.endpoint_src4) 4
    let srcIf ← little memory (base + .ofNat 64 Layouts.endpoint_src_if4) 4
    return some { family := 2, addr, port, src, srcIf }
  | 10 =>
    let port ← big memory (base + .ofNat 64 (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_port)) 2
    let flowinfo ← big memory (base + .ofNat 64 (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_flowinfo)) 4
    let addr ← big memory (base + .ofNat 64 (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_addr)) 16
    let scope ← little memory (base + .ofNat 64 (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_scope_id)) 4
    let src ← big memory (base + .ofNat 64 Layouts.endpoint_src6) 16
    return some { family := 10, addr, port, src, scope, flowinfo }
  | _ => none

def At (memory : Mem 64) (base : BitVec 64) (value : Option Endpoint) : Prop :=
  decode memory base = some value

def Peer (memory : Mem 64) (base : BitVec 64) (peer : Leanux.WG.Peer) : Prop :=
  At memory (base + .ofNat 64 Layouts.peer_endpoint) peer.endpoint

/-- Conservative union of the active read footprints, including family.
    This is a framing support, not a requirement that inactive bytes exist. -/
def offsets : List (Nat × Nat) := [
  (Layouts.endpoint_addr + Layouts.sockaddr_sa_family, 2),
  (Layouts.endpoint_addr4 + Layouts.sockaddr4_sin_port, 2),
  (Layouts.endpoint_addr4 + Layouts.sockaddr4_sin_addr, 4),
  (Layouts.endpoint_src4, 4), (Layouts.endpoint_src_if4, 4),
  (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_port, 2),
  (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_flowinfo, 4),
  (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_addr, 16),
  (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_scope_id, 4),
  (Layouts.endpoint_src6, 16)]

def Reads (base address : BitVec 64) : Prop :=
  ∃ cell ∈ offsets, InRange (base + .ofNat 64 cell.1) cell.2 address

theorem decode_frame {before after : Mem 64} {writes : BitVec 64 → Prop}
    (same : EqualOutside writes before after) (base : BitVec 64)
    (apart : ∀ address, Reads base address → ¬writes address) :
    decode before base = decode after base := by
  have bytes (offset width : Nat) (member : (offset, width) ∈ offsets) :
      before.loadBytes (base + .ofNat 64 offset) width = after.loadBytes (base + .ofNat 64 offset) width :=
    same.loadBytes _ _ (fun i hi => apart _ ⟨(offset, width), member, i, hi, rfl⟩)
  simp only [decode, little, big]
  rw [bytes _ _ (show (Layouts.endpoint_addr + Layouts.sockaddr_sa_family, 2) ∈ offsets by decide),
    bytes _ _ (show (Layouts.endpoint_addr4 + Layouts.sockaddr4_sin_port, 2) ∈ offsets by decide),
    bytes _ _ (show (Layouts.endpoint_addr4 + Layouts.sockaddr4_sin_addr, 4) ∈ offsets by decide),
    bytes _ _ (show (Layouts.endpoint_src4, 4) ∈ offsets by decide),
    bytes _ _ (show (Layouts.endpoint_src_if4, 4) ∈ offsets by decide),
    bytes _ _ (show (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_port, 2) ∈ offsets by decide),
    bytes _ _ (show (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_flowinfo, 4) ∈ offsets by decide),
    bytes _ _ (show (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_addr, 16) ∈ offsets by decide),
    bytes _ _ (show (Layouts.endpoint_addr6 + Layouts.sockaddr6_sin6_scope_id, 4) ∈ offsets by decide),
    bytes _ _ (show (Layouts.endpoint_src6, 16) ∈ offsets by decide)]

theorem At.functional {memory base a b} (ha : At memory base a) (hb : At memory base b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

theorem At.frame {before after base value writes}
    (same : EqualOutside writes before after)
    (apart : ∀ address, Reads base address → ¬writes address)
    (represented : At before base value) : At after base value :=
  (decode_frame same base apart).symm.trans represented

/-- Exact inactive-union behavior: family zero alone determines none. -/
theorem absent {memory base}
    (family : little memory (base + .ofNat 64 (Layouts.endpoint_addr + Layouts.sockaddr_sa_family)) 2 = some 0) :
    At memory base none := by
  simp [At, decode, family]

#print axioms decode_frame
#print axioms At.functional
#print axioms At.frame
#print axioms absent
end Binary.EndpointHeap
