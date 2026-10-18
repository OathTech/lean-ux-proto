import Leanux.Proofs.WG.Index.ExpiryIndexFrames
import Leanux.Proofs.WG.Index.ReachedIndexModel
import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.RetirementRetentionEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Queues.RxCredits

/-- The owner word and all three peer slots survive a validity-only key write. -/
theorem invalidateDevice_hashSlots (d : Device) (key : Option KeypairId)
    (covered : HashSlotCoverage d) :
    HashSlotCoverage (Config.invalidateDevice d key) := by
  have fields := invalidateDevice_indexFields d key
  apply hashSlotCoverage_transport d _ (congrArg (fun s => s.1) fields) _ _ covered
  · intro pid
    rw [show (Config.invalidateDevice d key).peers = d.peers from congrArg (fun s => s.2.1) fields]
  · intro kid
    rw [Config.invalidateDevice_lookup]
    cases found : d.keypairs[kid]? with
    | none => rfl
    | some k =>
      simp only [Option.map_some]
      split <;> rfl

/-- The validity write preserves every existing dead-owner reservation. -/
theorem invalidateDevice_retirement (retired : Reservations) (d : Device)
    (key : Option KeypairId) (reserved : DeadHashedReserved retired d) :
    DeadHashedReserved retired (Config.invalidateDevice d key) := by
  have fields := invalidateDevice_indexFields d key
  apply deadHashedReserved_transport retired d _ (congrArg (fun s => s.2.2.1) fields) _ _ _ reserved
  · intro e member
    simpa only [show (Config.invalidateDevice d key).indexTable=d.indexTable from
      congrArg (fun s => s.1) fields] using member
  · intro e member kid owner
    simp only [owner,ownerWord,Config.invalidateDevice_lookup]
    cases found : d.keypairs[kid]? with
    | none => rfl
    | some k =>
      simp only [Option.map_some]
      split <;> rfl
  · intro pid p found
    rw [show (Config.invalidateDevice d key).peers=d.peers from
      congrArg (fun s => s.2.1) fields] at found
    exact ⟨p,found,rfl,rfl⟩

/-- The original prefix unhashes the handshake, zeroes its fields, and resets
its timestamp. A resident peer keeps its slots, allocation stamp and dead flag. -/
theorem expiryHeadDevice_hashSlots_retirement (retired : Reservations) (d : Device)
    (pid : PeerId) (p : Peer) (now : Int64) (resident : d.peers[pid]?=some p)
    (covered : HashSlotCoverage d) (reserved : DeadHashedReserved retired d) :
    HashSlotCoverage (Config.expiryHeadDevice d pid p now) ∧
      DeadHashedReserved retired (Config.expiryHeadDevice d pid p now) := by
  let removed : Device := {d with indexTable := removeOwner (.handshake pid) d.indexTable}
  let zeroed : Device := {removed with peers := removed.peers.insert pid (Config.zeroedHandshake p)}
  let reset : Peer := {Config.zeroedHandshake p with
    lastSentHandshake := now - (REKEY_TIMEOUT+1 : Nat).toInt64 * NSEC_PER_SEC64}
  have zeroResident : zeroed.peers[pid]? = some (Config.zeroedHandshake p) := by
    simp [zeroed]
  have removedReserved : DeadHashedReserved retired removed := by
    apply deadHashedReserved_transport retired d removed rfl _ _ _ reserved
    · intro e member
      exact (List.mem_filter.mp member).1
    · intro e member kid owner
      simp only [owner,ownerWord,removed]
    · intro target peer found
      exact ⟨peer,found,rfl,rfl⟩
  have zeroCovered := hashSlotCoverage_peerWrite removed pid p
    (Config.zeroedHandshake p) resident rfl (hashSlotCoverage_remove d (.handshake pid) covered)
  have zeroReserved := peerWrite_deadHashedReserved retired removed pid p
    (Config.zeroedHandshake p) resident rfl rfl removedReserved
  exact ⟨hashSlotCoverage_peerWrite zeroed pid (Config.zeroedHandshake p) reset
    zeroResident rfl zeroCovered,
    peerWrite_deadHashedReserved retired zeroed pid (Config.zeroedHandshake p) reset
      zeroResident rfl rfl zeroReserved⟩

/-- The exact full expiry effect retains coverage and reservations, including
when the next/current optional slots alias. -/
theorem expiredDevice_hashSlots_retirement (retired : Reservations) (d : Device)
    (pid : PeerId) (p : Peer) (now : Int64) (resident : d.peers[pid]?=some p)
    (covered : HashSlotCoverage d) (reserved : DeadHashedReserved retired d) :
    HashSlotCoverage (Config.expiredDevice d pid p now) ∧
      DeadHashedReserved retired (Config.expiredDevice d pid p now) := by
  have head := expiryHeadDevice_hashSlots_retirement retired d pid p now resident covered reserved
  exact ⟨invalidateDevice_hashSlots _ _ (invalidateDevice_hashSlots _ _ head.1),
    invalidateDevice_retirement _ _ _ (invalidateDevice_retirement _ _ _ head.2)⟩

/-- Expiry only removes handshake rows and leaves the key allocation cursor. -/
theorem expiredDevice_tables (d : Device) (pid : PeerId) (p : Peer) (now : Int64)
    (safe : DeviceTablesSafe d) : DeviceTablesSafe (Config.expiredDevice d pid p now) := by
  have fields := invalidateDevice_indexFields
    (Config.invalidateDevice (Config.expiryHeadDevice d pid p now) p.keypairNext) p.keypairCurrent
  have first := invalidateDevice_indexFields (Config.expiryHeadDevice d pid p now) p.keypairNext
  have table : (Config.expiredDevice d pid p now).indexTable =
      removeOwner (.handshake pid) d.indexTable :=
    (congrArg (fun s => s.1) fields).trans (congrArg (fun s => s.1) first)
  have cursor : (Config.expiredDevice d pid p now).nextKeypairId = d.nextKeypairId :=
    (congrArg (fun s => s.2.2.2) fields).trans (congrArg (fun s => s.2.2.2) first)
  refine ⟨?_,?_,?_⟩
  · rw [table]
    exact remove_indices _ _ safe.1
  · rw [table]
    exact remove_owners _ _ safe.2.1
  · intro e member kid owner
    rw [table] at member
    rw [cursor]
    exact safe.2.2 e (List.mem_filter.mp member).1 kid owner
end Leanux.Proofs.WG.Index
