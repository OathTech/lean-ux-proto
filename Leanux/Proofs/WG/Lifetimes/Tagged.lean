import Leanux.Proofs.Logged.Focus
import Leanux.Proofs.WG.Peers.CreationAccess
import Leanux.Proofs.WG.Packets.Primitives

/-! One ordered stream of correctly paired lifetime event families. Packet
stamps already include the device epoch; no frontier order is imposed here. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged

abbrev KeypairEvent := AccessEvent KeypairId Nat
abbrev PacketStamp := Nat × Nat
abbrev PacketEvent := AccessEvent Packets.Slot PacketStamp

inductive LifetimeEvent where
  | peer : Peers.PeerEvent → LifetimeEvent
  | keypair : KeypairEvent → LifetimeEvent
  | packet : PacketEvent → LifetimeEvent
  deriving Repr, DecidableEq

namespace LifetimeEvent
def peer? : LifetimeEvent → Option Peers.PeerEvent
  | .peer e => some e | _ => none
def keypair? : LifetimeEvent → Option KeypairEvent
  | .keypair e => some e | _ => none
def packet? : LifetimeEvent → Option PacketEvent
  | .packet e => some e | _ => none
def Safe (h : List LifetimeEvent) : Prop :=
  AccessEvent.Safe (h.filterMap peer?) ∧ AccessEvent.Safe (h.filterMap keypair?) ∧
    AccessEvent.Safe (h.filterMap packet?)
end LifetimeEvent

/-- The minimal access condition: history is safe and released identities
have no resident. Uniqueness is an additional release obligation, not needed
to observe getters and identity-preserving setters. -/
def ResidentSafe {ι κ : Type} (h : List (AccessEvent ι κ)) (resident : ι → Option κ) : Prop :=
  AccessEvent.Safe h ∧ ∀ stamp, AccessEvent.Released h stamp → ∀ i, resident i ≠ some stamp

theorem ResidentSafe.read (hi : ResidentSafe h resident) (hl : resident i = some stamp) :
    ResidentSafe (h ++ [.read i stamp]) resident := by
  exact ⟨AccessEvent.safe_append_read hi.1 (fun hr => hi.2 stamp hr i hl),
    fun s hs => hi.2 s (AccessEvent.released_append_read.mp hs)⟩

theorem ResidentSafe.write (hi : ResidentSafe h resident) (hl : resident i = some stamp) :
    ResidentSafe (h ++ [.write i stamp]) resident := by
  exact ⟨AccessEvent.safe_append_write hi.1 (fun hr => hi.2 stamp hr i hl),
    fun s hs => hi.2 s (AccessEvent.released_append_write.mp hs)⟩

def keypairResidents (w : World) : KeypairId → Option Nat :=
  fun i => (w.k.wg.bind fun d => d.keypairs[i]?).map (·.internalId)

def packetResidents (w : World) : Packets.Slot → Option PacketStamp :=
  fun slot => w.k.wg.bind fun d => match slot with
    | .inl i => d.txSkbs[i]?.map (fun _ => (d.ifindex, i + 1))
    | .inr i => d.rxSkbs[i]?.map (fun _ => (d.ifindex, i + 1))

structure MixedInv (h : List LifetimeEvent) (w : World) : Prop where
  peer : Peers.AccessInv (h.filterMap LifetimeEvent.peer?) w
  keypair : ResidentSafe (h.filterMap LifetimeEvent.keypair?) (keypairResidents w)
  packet : ResidentSafe (h.filterMap LifetimeEvent.packet?) (packetResidents w)

theorem MixedInv.safe (hi : MixedInv h w) : LifetimeEvent.Safe h :=
  ⟨hi.peer.1, hi.keypair.1, hi.packet.1⟩

abbrev MixedM := PrefixM LifetimeEvent
def peerFocus (g : PrefixM Peers.PeerEvent α) : MixedM α :=
  focusPrefix LifetimeEvent.peer LifetimeEvent.peer? g

theorem peerFocus_erases (hg : ErasesPrefix g a) : ErasesPrefix (peerFocus g) a :=
  focusPrefix_erases _ _ hg

end Leanux.Proofs.WG.Lifetimes
