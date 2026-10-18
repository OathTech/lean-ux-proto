import Leanux.Proofs.WG.Index.PollCoreModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.PollCore
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem absent_retained {pid : PeerId} {w v : WGWorld}
    (retained : TagsRetained (responseTagMap w.dev) (responseTagMap v.dev))
    (absent : Absent pid w) : Absent pid v := by
  cases found : responseTagMap v.dev pid with
  | none=>exact found
  | some tag=>
    have before := retained pid tag found
    rw [absent] at before
    cases before

theorem key_fields_core (d f : Device)
    (table : f.indexTable=d.indexTable) (cursor : f.nextKeypairId=d.nextKeypairId)
    (epoch : f.ifindex=d.ifindex) (peers : f.peers=d.peers)
    (keys : ∀kid : KeypairId,
      f.keypairs[kid]?.map (fun k=>(k.peer,k.refcount)) =
        d.keypairs[kid]?.map (fun k=>(k.peer,k.refcount)))
    (pre : DeviceIndexCore d) : DeviceIndexCore f := by
  have words (kid : KeypairId) :
      f.keypairs[kid]?.map Keypair.peer=d.keypairs[kid]?.map Keypair.peer := by
    simpa only [Option.map_map,Function.comp_def] using congrArg (Option.map Prod.fst) (keys kid)
  have ownerWords (owner : IndexOwner) : ownerWord f owner=ownerWord d owner := by
    cases owner with
    | handshake pid=>simp only [ownerWord,peers]
    | keypair kid=>exact words kid
  refine ⟨⟨table ▸ pre.1.1,table ▸ pre.1.2.1,
    fun e member kid owner=>cursor ▸ pre.1.2.2 e (table ▸ member) kid owner⟩,
    hashSlotCoverage_transport d f table (fun _=>by rw [peers]) words pre.2.1,?_,?_⟩
  · intro e member
    obtain ⟨pid,p,word,stored,positive,key⟩ := pre.2.2.1 e (table ▸ member)
    refine ⟨pid,p,(ownerWords e.owner).trans word,peers ▸ stored,positive,?_⟩
    cases owner:e.owner with
    | handshake own=>simpa only [owner] using key
    | keypair kid=>
      obtain ⟨k,found,live⟩ : ∃k,d.keypairs[kid]?=some k ∧ 0<k.refcount := by simpa only [owner] using key
      have same : f.keypairs[kid]?.map (fun k=>(k.peer,k.refcount))=some (k.peer,k.refcount) := by
        rw [keys kid,found]; rfl
      obtain ⟨q,after,fields⟩ := Option.map_eq_some_iff.mp same
      exact ⟨q,after,by have count : q.refcount=k.refcount := congrArg Prod.snd fields; simpa only [count] using live⟩
  · exact deadHashedReserved_transport [] d f epoch (fun _ member=>table ▸ member)
      (fun e _ _ _=>ownerWords e.owner)
      (fun _ p found=>⟨p,peers ▸ found,rfl,rfl⟩) pre.2.2.2

theorem key_write_core (d : Device) (kid : KeypairId) (k q : Keypair)
    (resident : d.keypairs[kid]?=some k)
    (same : (q.peer,q.refcount)=(k.peer,k.refcount))
    (pre : DeviceIndexCore d) :
    DeviceIndexCore {d with keypairs:=d.keypairs.insert kid q} := by
  apply key_fields_core d {d with keypairs:=d.keypairs.insert kid q} rfl rfl rfl rfl _ pre
  intro other
  by_cases alias:kid=other
  · subst other; simp [resident,same]
  · simp [Std.TreeMap.getElem?_insert,alias]

end Leanux.Proofs.WG.Index.PollCore
