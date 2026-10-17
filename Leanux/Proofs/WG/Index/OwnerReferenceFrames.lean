import Leanux.Proofs.WG.Index.OwnerReferenceModel
import Leanux.Proofs.WG.Config.KeyReferences

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

theorem ownerReferences_coherent (d next : Device)
    (same : ownerReferences next = ownerReferences d)
    (coherent : HashedOwnersCoherent d) : HashedOwnersCoherent next := by
  have table : next.indexTable = d.indexTable := congrArg Prod.fst same
  have keys : next.keypairs = d.keypairs := congrArg (fun x => x.2.1) same
  have peers (pid : PeerId) :
      next.peers[pid]?.map (fun p => (p.handshakeEntryPeer, p.refcount)) =
      d.peers[pid]?.map (fun p => (p.handshakeEntryPeer, p.refcount)) :=
    congrFun (congrArg (fun x => x.2.2) same) pid
  intro e member
  obtain ⟨pid, p, word, found, positive, identity⟩ := coherent e (table ▸ member)
  cases after : next.peers[pid]? with
  | none => have impossible := peers pid; simp [after, found] at impossible
  | some q =>
    have values := peers pid
    simp only [after, found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at values
    refine ⟨pid, q, ?_, after, by omega, ?_⟩
    · cases owner : e.owner with
      | handshake own =>
        have ownpid : pid = own := by simpa [owner] using identity
        subst own
        simpa [ownerWord, owner, after, found, values.1] using word
      | keypair id => simpa [ownerWord, owner, keys] using word
    · cases owner : e.owner with
      | handshake own => simpa only [owner] using identity
      | keypair id => simpa only [owner, keys] using identity

theorem keypairAcquire_owner_coherent (d : Device) (id : KeypairId) (k : Keypair)
    (resident : d.keypairs[id]? = some k) (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (Config.withKeypair d id {k with refcount := k.refcount + 1}) := by
  intro e member
  obtain ⟨pid, p, word, found, positive, identity⟩ := coherent e member
  refine ⟨pid, p, ?_, found, positive, ?_⟩
  · cases owner : e.owner with
    | handshake own => simpa only [owner, ownerWord, Config.withKeypair] using word
    | keypair own =>
      by_cases alias : id = own
      · subst own
        simpa [ownerWord, owner, Config.withKeypair, resident] using word
      · simpa [ownerWord, owner, Config.withKeypair, Std.TreeMap.getElem?_insert, alias] using word
  · cases owner : e.owner with
    | handshake own => simpa only [owner] using identity
    | keypair own =>
      obtain ⟨old, stored, live⟩ := (show ∃ old, d.keypairs[own]? = some old ∧ 0 < old.refcount by simpa only [owner] using identity)
      by_cases alias : id = own
      · subst own
        have equal : old = k := Option.some.inj (stored.symm.trans resident)
        subst old
        exact ⟨{k with refcount := k.refcount + 1}, by simp [Config.withKeypair], by simp⟩
      · exact ⟨old, by simpa [Config.withKeypair, Std.TreeMap.getElem?_insert, alias] using stored, live⟩


end Leanux.Proofs.WG.Index
