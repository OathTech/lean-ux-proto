import Leanux.Proofs.WG.Index.OwnerCoherenceSessionFrames
import Leanux.Proofs.WG.Index.OwnerCoherenceTableEffects
import Leanux.Proofs.WG.Config.ExpiryEffects

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Handshake removal and zeroing retain all remaining hashed owner relations.
The actual resident peer need not itself be hashed or positively referenced. -/
theorem expiryZeroDevice_owner_coherent (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (Config.expiryZeroDevice d pid p) := by
  let removed : Device := {d with indexTable := removeOwner (.handshake pid) d.indexTable}
  exact peerWrite_owner_coherent removed pid p (Config.zeroedHandshake p)
    resident rfl rfl (hashedOwnersCoherent_remove d (.handshake pid) coherent)

/-- The optional validity-only write leaves owner words and both reference
counts intact. The pure missing-key case describes no native success claim. -/
theorem invalidateDevice_owner_coherent (d : Device) (key : Option KeypairId)
    (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (Config.invalidateDevice d key) := by
  cases key with
  | none => exact coherent
  | some id =>
    cases resident : d.keypairs[id]? with
    | none => simpa [Config.invalidateDevice, resident] using coherent
    | some k =>
      intro e member
      have oldMember : e ∈ d.indexTable := by simpa [Config.invalidateDevice, resident] using member
      obtain ⟨pid,p,word,found,positive,owned⟩ := coherent e oldMember
      refine ⟨pid,p,?_,?_,positive,?_⟩
      · cases owner : e.owner with
        | handshake own => simpa [owner, ownerWord, Config.invalidateDevice, resident] using word
        | keypair own =>
          by_cases alias : id = own
          · subst own
            simpa [owner, ownerWord, Config.invalidateDevice, resident] using word
          · simpa [owner, ownerWord, Config.invalidateDevice, resident,
              Std.TreeMap.getElem?_insert, alias] using word
      · simpa [Config.invalidateDevice, resident] using found
      · cases owner : e.owner with
        | handshake own => simpa only [owner] using owned
        | keypair own =>
          obtain ⟨original,stored,live⟩ :=
            (show ∃original, d.keypairs[own]? = some original ∧ 0 < original.refcount by
              simpa only [owner] using owned)
          by_cases alias : id = own
          · subst own
            have same : original = k := Option.some.inj (stored.symm.trans resident)
            subst original
            exact ⟨{k with sending := {k.sending with isValid := false}},
              by simp [Config.invalidateDevice, resident], live⟩
          · exact ⟨original,by simpa [Config.invalidateDevice, resident,
              Std.TreeMap.getElem?_insert, alias] using stored,live⟩

/-- The exact expiry effect resets handshake fields and time, then invalidates
next and current in source order. Repeated key identities are allowed. -/
theorem expiredDevice_owner_coherent (d : Device) (pid : PeerId) (p : Peer) (now : Int64)
    (resident : d.peers[pid]? = some p) (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (Config.expiredDevice d pid p now) := by
  have cleared := expiryZeroDevice_owner_coherent d pid p resident coherent
  have zeroResident : (Config.expiryZeroDevice d pid p).peers[pid]? = some (Config.zeroedHandshake p) := by
    simp [Config.expiryZeroDevice, Config.withPeer]
  have head : HashedOwnersCoherent (Config.expiryHeadDevice d pid p now) :=
    peerWrite_owner_coherent (Config.expiryZeroDevice d pid p) pid (Config.zeroedHandshake p)
      {Config.zeroedHandshake p with
        lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64}
      zeroResident rfl rfl cleared
  exact invalidateDevice_owner_coherent _ p.keypairCurrent
    (invalidateDevice_owner_coherent _ p.keypairNext head)

end Leanux.Proofs.WG.Index
