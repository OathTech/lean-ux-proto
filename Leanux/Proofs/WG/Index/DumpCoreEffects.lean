import Leanux.Proofs.WG.Index.DumpCoreModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DumpCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits Queues.RxCredits.DurableHolders

theorem deviceFrame_of_rich {w v : WGWorld} (frame : StagingRich.Frame w v) :
    DeviceFrame w.dev v.dev :=
  ⟨⟨frame.legacy.1,frame.legacy.2.1,rfl⟩,frame.tables,frame.peers,frame.keys,frame.live⟩

theorem handshake_of_core (d : Device) (pre : DeviceIndexCore d) : HandshakeCoherent d := by
  intro e member pid owner
  obtain ⟨target,p,word,resident,pos,identity⟩ := pre.2.2.1 e member
  have same : target=pid := by simpa only [owner] using identity
  subst target
  exact ⟨p,resident,by simpa [owner,ownerWord,resident] using word,pos⟩

theorem handshake_acquire (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]?=some p) (pre : HandshakeCoherent d) :
    HandshakeCoherent (acquirePeer d pid p) := by
  intro e member target owner
  obtain ⟨q,stored,word,pos⟩ := pre e member target owner
  by_cases same : pid=target
  · subst target
    have eq : q=p := Option.some.inj (stored.symm.trans resident)
    subst q
    exact ⟨{p with refcount:=p.refcount+1},by simp [acquirePeer],word,by simp⟩
  · exact ⟨q,by simpa [acquirePeer,Std.TreeMap.getElem?_insert,same] using stored,word,pos⟩

theorem handshake_release (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]?=some p) (positive : 0<p.refcount) (pre : HandshakeCoherent d) :
    HandshakeCoherent (releasedPeerDevice d pid p) := by
  intro e member target owner
  by_cases last : p.refcount=1
  · have member' : e∈d.indexTable ∧ e.owner≠.handshake pid := by
      simpa [releasedPeerDevice,last,removeOwner] using member
    have other : pid≠target := by
      intro same
      exact member'.2 (owner.trans (congrArg IndexOwner.handshake same.symm))
    obtain ⟨q,stored,word,pos⟩ := pre e member'.1 target owner
    exact ⟨q,by simpa [releasedPeerDevice,last,Std.TreeMap.getElem?_insert,
      Std.TreeMap.getElem?_erase,other] using stored,word,pos⟩
  · have old : e∈d.indexTable := by simpa [releasedPeerDevice,last] using member
    obtain ⟨q,stored,word,pos⟩ := pre e old target owner
    by_cases same : pid=target
    · subst target
      have eq : q=p := Option.some.inj (stored.symm.trans resident)
      subst q
      exact ⟨{p with refcount:=p.refcount-1},by simp [releasedPeerDevice,last],word,by change 0<p.refcount-1;omega⟩
    · exact ⟨q,by simpa [releasedPeerDevice,last,Std.TreeMap.getElem?_insert,same] using stored,word,pos⟩

theorem base_member_positive
    {holders : DurableHolders} {cs : Ledger} {loans : Reservations}
    {w : WGWorld} {o : Owner}
    (funded : holders.Funded cs loans w) (member : o∈holders.base) :
    ∃p,resident w o=some p ∧ 0<p.refcount := by
  have owned : o∈holders.owners := by
    simp only [DurableHolders.owners,List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl member))))
  have positive : 0<holders.owners.count o := List.count_pos_iff.mpr owned
  have demanded : 0<demand cs (holders.owners++loans) o := by
    simp only [demand,List.count_append]
    omega
  obtain ⟨p,found,budget⟩ := protected_resident funded.carriers.funded demanded
  exact ⟨p,found,by omega⟩

theorem core_of_funded
    (w v : WGWorld) (holders afterHolders : DurableHolders)
    (cs : Ledger) (loans : Reservations)
    (configured : ConfiguredIdentity.Inv w) (base : BaseCoherence.Inv w)
    (funded : holders.Funded cs loans w) (fundedAfter : afterHolders.Funded cs loans v)
    (sameBase : afterHolders.base=holders.base)
    (frame : DeviceFrame w.dev v.dev) (shape : Shape w.dev.isSome v)
    (core : Reached.Core w) : Reached.Core v := by
  apply StagingRich.core_survivors frame ?_ ?_ core
  · intro final after
    change v.dev=some final at after
    cases before:w.dev with
    | none => simp [Shape,after,before] at shape
    | some d => exact ⟨d,rfl⟩
  · intro d final e pid p before after member word stored positive
    change w.dev=some d at before
    change v.dev=some final at after
    have subset : e∈d.indexTable := by
      have old := frame.tables e (by simpa [StagingRich.table,after] using member)
      simpa [StagingRich.table,before] using old
    cases owner:e.owner with
    | handshake target =>
      obtain ⟨old,q,ow,oq,_,identity⟩ := (core d before).2.2.1 e subset
      have oldEq : old=pid := Option.some.inj (Option.some.inj (ow.symm.trans word))
      have targetEq : pid=target := oldEq.symm.trans (by simpa [owner] using identity)
      obtain ⟨q,found,_,pos⟩ := shape.2 final after e member target owner
      exact ⟨q,by simpa only [targetEq] using found,pos⟩
    | keypair kid =>
      cases keyFound:d.keypairs[kid]? with
      | none => simp [ownerWord,owner,keyFound] at word
      | some key =>
        have keyWord : key.peer=some pid := by simpa [ownerWord,owner,keyFound] using word
        have live : p.isDead=false := by
          cases dead:p.isDead with
          | false => rfl
          | true =>
            exact (List.not_mem_nil ((core d before).2.2.2 e subset kid key pid p
              owner keyFound keyWord stored dead)).elim
        have memberBase := FundedBase.live_base_reservation configured base funded before stored live
        have keptBase : (⟨d.ifindex,pid,p.internalId⟩ : Owner)∈afterHolders.base :=
          sameBase.symm ▸ memberBase
        obtain ⟨q,residentQ,pos⟩ := base_member_positive fundedAfter keptBase
        obtain ⟨last,present,_,found,_⟩ := resident_fields residentQ
        have equal : last=final := Option.some.inj (present.symm.trans after)
        subst last
        exact ⟨q,found,pos⟩

end Leanux.Proofs.WG.Index.DumpCore
