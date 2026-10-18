import Leanux.Proofs.WG.Index.StagingRichEffects
import Leanux.Proofs.WG.Index.ReachedIndexBridge
import Leanux.Proofs.WG.Queues.RxConsumeProtection

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

namespace StagingCredit
open Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits DurableHolders
theorem handoff_peer {w v : WGWorld} {delta : HandoffDelta}
    (step : Handoff w v [] [] delta) (d : Device) (pid : PeerId) (p : Peer)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p) :
    ∃ final q, v.dev = some final ∧ final.peers[pid]? = some q ∧
      final.ifindex = d.ifindex ∧ q.internalId = p.internalId ∧ p.refcount ≤ q.refcount := by
  have epoch := congrArg Prod.fst step.base
  have cell := congrFun (congrArg Prod.snd step.base) pid
  cases last : v.dev with
  | none => simp [baseView,device,last] at epoch
  | some final =>
    have epochEq : final.ifindex = d.ifindex := by
      simpa [baseView,device,last] using epoch
    cases found : final.peers[pid]? with
    | none => simp [baseView,device,last,peer,found] at cell
    | some q =>
      have fields : (q.internalId,q.rxQueue) = (p.internalId,p.rxQueue) := by
        simpa [baseView,device,last,peer,found] using cell
      have stampEq : q.internalId = p.internalId := congrArg Prod.fst fields
      have count := step.count ⟨d.ifindex,pid,p.internalId⟩
      simp only [List.count_nil,Nat.add_zero] at count
      have initialBalance : balance w ⟨d.ifindex,pid,p.internalId⟩ = p.refcount := by
        simp [balance,resident,device,peer]
      have finalBalance : balance v ⟨d.ifindex,pid,p.internalId⟩ = q.refcount := by
        simp [balance,resident,last,found,epochEq,stampEq]
      rw [initialBalance,finalBalance] at count
      exact ⟨final,q,rfl,found,epochEq,stampEq,by omega⟩

end StagingCredit

namespace StagingRich
open Queues Queues.RxCredits
theorem peer_fields {entry current : WGWorld} (frame : Frame entry current)
    {d f : Device} {pid : PeerId} {p q : Peer}
    (before : entry.dev = some d) (after : current.dev = some f)
    (old : d.peers[pid]? = some p) (new : f.peers[pid]? = some q) :
    PeerCell q = PeerCell p := by
  have observed : peerMap current pid = some (PeerCell q) := by simp [peerMap,after,new]
  have found := frame.peers pid _ observed
  simpa [peerMap,before,old] using found.symm

theorem key_fields {entry current : WGWorld} (frame : Frame entry current)
    {d f : Device} {kid : KeypairId} {p q : Keypair}
    (before : entry.dev = some d) (after : current.dev = some f)
    (old : d.keypairs[kid]? = some p) (new : f.keypairs[kid]? = some q) :
    KeyCell q = KeyCell p := by
  have observed : keyMap current kid = some (KeyCell q) := by simp [keyMap,after,new]
  have found := frame.keys kid _ observed
  simpa [keyMap,before,old] using found.symm

theorem coherent_live {g : WGWorld}
    (coherent : ∀ d, g.dev = some d → HashedOwnersCoherent d) : HashedLive g := by
  intro d hd e member kid owner
  obtain ⟨pid,p,word,peer,positive,key⟩ := coherent d hd e member
  simpa only [owner] using key

theorem core_handoff {g f : WGWorld} {delta : HandoffDelta}
    (frame : Frame g f) (step : Handoff g f [] [] delta) (core : Reached.Core g) :
    Reached.Core f := by
  intro final after
  have oldPresent : ∃d, g.dev = some d := by
    have epoch := congrArg Prod.fst step.base
    cases hd : g.dev with
    | none => simp [baseView,after,hd] at epoch
    | some d => exact ⟨d,rfl⟩
  obtain ⟨d,before⟩ := oldPresent
  have original := core d before
  have subset : ∀ e ∈ final.indexTable, e ∈ d.indexTable := by
    intro e member
    simpa [table,before] using frame.tables e (by simpa [table,after] using member)
  have live : HashedLive f :=
    frame.live (coherent_live (fun d hd => (core d hd).2.2.1))
  have survives (pid : PeerId) (p : Peer) (stored : d.peers[pid]? = some p) :
      ∃ q, final.peers[pid]? = some q ∧ PeerCell q = PeerCell p ∧ p.refcount ≤ q.refcount := by
    obtain ⟨df,q,present,found,_,_,count⟩ := StagingCredit.handoff_peer step d pid p before stored
    have eq : df = final := Option.some.inj (present.symm.trans after)
    subst df
    exact ⟨q,found,peer_fields frame before after stored found,count⟩
  refine ⟨frame.legacy.1 (fun d hd => (core d hd).1) final after,?_,?_,?_⟩
  · intro e member kid owner
    obtain ⟨pid,p,key,stored,keyStored,word,slot⟩ := original.2.1 e (subset e member) kid owner
    obtain ⟨q,found,fields,_⟩ := survives pid p stored
    obtain ⟨k,foundKey,_⟩ := live final after e member kid owner
    have keyFields := key_fields frame before after keyStored foundKey
    have keyWord : k.peer = key.peer := congrArg Prod.fst keyFields
    have slots : clearKeys q = clearKeys p := by
      simp only [PeerCell,Prod.mk.injEq] at fields
      simp [clearKeys,fields.2.1,fields.2.2.1,fields.2.2.2.1]
    exact ⟨pid,q,k,found,foundKey,keyWord.trans word,slots.symm ▸ slot⟩
  · intro e member
    obtain ⟨pid,p,word,stored,pos,ownerFields⟩ := original.2.2.1 e (subset e member)
    obtain ⟨q,found,fields,count⟩ := survives pid p stored
    refine ⟨pid,q,?_,found,by omega,?_⟩
    · cases owner : e.owner with
      | handshake own =>
        have self : pid = own := by simpa only [owner] using ownerFields
        subst own
        have keyWord : q.handshakeEntryPeer = p.handshakeEntryPeer := by
          exact congrArg (fun c => c.2.2.2.2.1) fields
        have oldWord : p.handshakeEntryPeer = some pid := by
          simpa [owner,ownerWord,stored] using word
        simpa [owner,ownerWord,found,keyWord] using oldWord
      | keypair kid =>
        obtain ⟨k,foundKey,_⟩ := live final after e member kid owner
        obtain ⟨oldKey,storedKey,_⟩ : ∃k,d.keypairs[kid]?=some k ∧ 0<k.refcount := by
          simpa only [owner] using ownerFields
        have keyWord : k.peer = oldKey.peer := congrArg Prod.fst (key_fields frame before after storedKey foundKey)
        have oldWord : oldKey.peer = some pid := by
          simpa [owner,ownerWord,storedKey] using word
        simpa [owner,ownerWord,foundKey,keyWord] using oldWord
    · cases owner : e.owner with
      | handshake own => simpa only [owner] using ownerFields
      | keypair kid => exact live final after e member kid owner
  · intro e member kid k pid q owner keyStored keyWord stored dead
    obtain ⟨own,p,oldKey,peerOld,keyOld,oldWord,_⟩ := original.2.1 e (subset e member) kid owner
    have words := congrArg Prod.fst (key_fields frame before after keyOld keyStored)
    have same : own = pid := Option.some.inj (oldWord.symm.trans (words.symm.trans keyWord))
    subst own
    have fields := peer_fields frame before after peerOld stored
    have oldDead : p.isDead = true :=
      (congrArg (fun c => c.2.2.2.2.2.2) fields).symm.trans dead
    exact (List.not_mem_nil (original.2.2.2 e (subset e member) kid oldKey pid p
      owner keyOld oldWord peerOld oldDead)).elim

end StagingRich

end Leanux.Proofs.WG.Index
