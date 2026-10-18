import Leanux.Proofs.WG.Index.RetirementBulkModel
import Leanux.Proofs.WG.Index.RetirementTransferSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.Framing
open Queues.RxCredits Queues.RxCredits.DurableHolders Lifetimes Std.Do

theorem deadHashedReserved_of_all (reserved : Reservations) (d : Device)
    (all : AllHashedReserved reserved d) : DeadHashedReserved reserved d :=
  fun entry member kid key pid p owner keyFound word peerFound _ =>
    all entry member kid key pid p owner keyFound word peerFound

/-- The temporary bulk reserve is derived from existing base funding and
the prior dead-owner obligation; it is not an extra initial invariant. -/
theorem allHashedReserved_of_funded
    (holders : DurableHolders) (cs : Ledger) (loans retired : Reservations)
    (w : WGWorld) (d : Device)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs loans w) (device : w.dev = some d)
    (reserved : DeadHashedReserved retired d) :
    AllHashedReserved (holders.base ++ retired) d := by
  intro entry member kid key pid p owner keyFound word peerFound
  cases dead : p.isDead with
  | false => exact List.mem_append.mpr (Or.inl
      (FundedBase.live_base_reservation configured base funded device peerFound dead))
  | true => exact List.mem_append.mpr (Or.inr
      (reserved entry member kid key pid p owner keyFound word peerFound dead))

/-- Table, nullable owner words and peer allocation stamps suffice. Peer
dead flags, allowed-IP lists and reference counts need not be retained. -/
theorem allHashedReserved_transport (reserved : Reservations) (d final : Device)
    (before : AllHashedReserved reserved d)
    (table : final.indexTable = d.indexTable)
    (words : ∀ (kid : KeypairId), (final.keypairs[kid]?).map Keypair.peer =
      (d.keypairs[kid]?).map Keypair.peer)
    (peers : ∀ (pid : PeerId), (final.peers[pid]?).map Peer.internalId =
      (d.peers[pid]?).map Peer.internalId)
    (epoch : final.ifindex = d.ifindex) :
    AllHashedReserved reserved final := by
  intro entry member kid key pid p owner keyFound word peerFound
  have oldMember : entry ∈ d.indexTable := table ▸ member
  have oldWord : (d.keypairs[kid]?).map Keypair.peer = some (some pid) := by
    rw [←words kid,keyFound]
    exact congrArg some word
  obtain ⟨oldKey,oldKeyFound,oldKeyWord⟩ := Option.map_eq_some_iff.mp oldWord
  have oldPeer : (d.peers[pid]?).map Peer.internalId = some p.internalId := by
    rw [←peers pid,peerFound]
    rfl
  obtain ⟨oldP,oldFound,stamp⟩ := Option.map_eq_some_iff.mp oldPeer
  simpa only [epoch,←stamp] using
    before entry oldMember kid oldKey pid oldP owner oldKeyFound oldKeyWord oldFound

end Leanux.Proofs.WG.Index
