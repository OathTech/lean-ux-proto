import Leanux.Proofs.WG.Index.StagedSource
import Leanux.Proofs.WG.Index.StagingIndexEffects
import Leanux.Proofs.WG.Index.StagingIndexModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.StagingRich
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem staged_core (pid : PeerId) :
    Ensures (sendStagedPackets pid)
      (fun g => CurrentSlots.Inv g ∧ Reached.Core g) (fun _ => Reached.Core) := by
  intro g a r f b pre run
  cases r
  obtain ⟨delta,step⟩ := staged_send_handoff pid ((CurrentSlots.current pre.1).compatible pid) a b run
  exact core_handoff (sendStagedPackets_rich pid g g a () f b (refl g) run) step pre.2

theorem keepalive_core (pid : PeerId) :
    Ensures (sendKeepalive pid)
      (fun g => CurrentSlots.Inv g ∧ Reached.Core g) (fun _ => Reached.Core) := by
  apply keepalive_rule pid _ _ (fun _ h => h.2) (staged_core pid)
  intro g d p mtu hd hp pre
  have affiliation : Affiliation.view {g with dev := some {d with peers := d.peers.insert pid ({p with staged := p.staged ++ [{mtu := mtu}]})}} = Affiliation.view g := by
    simp only [Affiliation.view,hd,Option.map_some]
    congr 1
    unfold Affiliation.state
    congr 1
    funext target
    by_cases same : pid = target
    · subst target; simp [hp,Affiliation.peerCell]
    · simp [Std.TreeMap.getElem?_insert,same]
  refine ⟨?_,?_⟩
  · intro s present
    exact pre.1 s (affiliation ▸ present)
  · intro final present
    cases present
    have unchanged : PeerCell {p with staged := p.staged ++ [{mtu := mtu}]} = PeerCell p := rfl
    have peers := peerMap_write d pid p _ hp unchanged
    have original := pre.2 d hd
    refine ⟨original.1,?_,?_,?_⟩
    · intro e member kid owner
      obtain ⟨target,old,key,stored,keyStored,word,slot⟩ := original.2.1 e member kid owner
      by_cases same : pid = target
      · subst target
        have eq : old = p := Option.some.inj (stored.symm.trans hp)
        subst old
        exact ⟨pid,{p with staged := p.staged ++ [{mtu := mtu}]},key,by simp,keyStored,word,slot⟩
      · exact ⟨target,old,key,by simpa [Std.TreeMap.getElem?_insert,same] using stored,keyStored,word,slot⟩
    · intro e member
      obtain ⟨target,old,word,stored,pos,rest⟩ := original.2.2.1 e member
      have ownerSame : ownerWord {d with peers := d.peers.insert pid ({p with staged := p.staged ++ [{mtu := mtu}]})} e.owner = ownerWord d e.owner := by
        cases e.owner with
        | handshake own =>
          by_cases same : pid = own
          · subst own; simp [ownerWord,hp]
          · simp [ownerWord,Std.TreeMap.getElem?_insert,same]
        | keypair _ => rfl
      by_cases same : pid = target
      · subst target
        have eq : old = p := Option.some.inj (stored.symm.trans hp)
        subst old
        exact ⟨pid,{p with staged := p.staged ++ [{mtu := mtu}]},ownerSame.trans word,by simp,pos,rest⟩
      · exact ⟨target,old,ownerSame.trans word,by simpa [Std.TreeMap.getElem?_insert,same] using stored,pos,rest⟩
    · intro e member kid key target q owner keyStored word stored dead
      by_cases same : pid = target
      · subst target
        simp only [Std.TreeMap.getElem?_insert_self,Option.some.injEq] at stored
        subst q
        exact original.2.2.2 e member kid key pid p owner keyStored word hp dead
      · exact original.2.2.2 e member kid key target q owner keyStored word
          (by simpa [Std.TreeMap.getElem?_insert,same] using stored) dead

theorem ready_native (g : WGWorld) (a : Ambient) :
    View.StagedIndexReady (Campaign2.snapshot g a) ↔ CurrentSlots.Inv g ∧ Reached.Core g := by
  constructor
  · intro pre
    refine ⟨?_,fun d hd => (pre d hd).2⟩
    intro s present
    cases hd : g.dev with
    | none => simp [Affiliation.view,hd] at present
    | some d =>
      simp only [Affiliation.view,hd,Option.map_some,Option.some.injEq] at present
      subst s
      exact (pre d hd).1
  · intro pre d hd
    change g.dev = some d at hd
    exact ⟨pre.1 (Affiliation.state d) (by simp [Affiliation.view,hd]),pre.2 d hd⟩

end Leanux.Proofs.WG.Index.StagingRich
