import Leanux.Proofs.WG.RetirementSecurity.ZeroTimerDispatch

/-! Native key clearing removes every original slot's index publication,
including aliased slots. Final store release is separate and may wait for
outstanding RX/TX references. -/
namespace Leanux.Proofs.WG.RetirementSecurity.Unpublication
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes

/-- No existing key-index absence is lost by the action. -/
def Retains (w v : WGWorld) : Prop := ∀id,Unpublished id w→Unpublished id v

theorem Retains.trans (first : Retains w u) (second : Retains u v) : Retains w v :=
  fun id before=>second id (first id before)

theorem Retains.same (same : indexAt v=indexAt w) : Retains w v := by
  intro id before entries found entry member
  exact before entries (same ▸ found) entry member

theorem effect {id : KeypairId} (put : PutEffect id now k w v) : Retains w v := by
  intro selected before entries found entry member
  rw [put.index] at found
  cases old:indexAt w with
  | none=>simp [old] at found
  | some prior=>
    simp only [old,Option.map_some,Option.some.injEq] at found
    split at found
    · subst entries
      exact before prior old entry (List.mem_filter.mp member).1
    · subst entries
      exact before prior old entry member

theorem put_some (id : KeypairId) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some id) now).run w).run a=.ok (((),v),b)) :
    ∃k, keyAt w id=some k ∧ PutEffect id now k w v := by
  cases device:w.dev with
  | none=>
    simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d=>
    cases found:d.keypairs[id]? with
    | none=>
      simp [keypairPut,branch,AmbientM.branch,getKeypair,getDev,device,found,invariant,AmbientM.invariant] at run
      cases run
    | some k=>exact ⟨k,by simp [keyAt,device,found],put_effect id now w v a b d k device found run⟩

theorem put (word : Option KeypairId) (now : Bool) (a b : Ambient)
    (run : ((keypairPut word now).run w).run a=.ok (((),v),b)) :
    Retains w v ∧ (now=true → ∀id∈word.toList,Unpublished id v) := by
  cases word with
  | none=>
    simp [keypairPut,branch,AmbientM.branch] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨fun _ before=>before,by simp⟩
  | some id=>
    obtain ⟨k,_,put⟩ := put_some id now a b run
    refine ⟨effect put,?_⟩
    intro yes other member
    have same : other=id := by simpa using member
    subst other
    exact put.unpublished (.inl yes)

theorem update (pid : PeerId) (slot : KeySlot) (p : Peer) (found : peerAt w pid=some p) (a b : Ambient)
    (run : ((updateSlot pid slot).run w).run a=.ok (((),v),b)) :
    peerAt v pid=some (slot.clear p) ∧ indexAt v=indexAt w := by
  simp only [updateSlot,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨read,u,c,getter,setter⟩ := run
  obtain ⟨worldSame,ambientSame,d,device,stored⟩ := Origins.getPeer_return pid w u read a c getter
  subst u
  subst c
  have same : read=p := Option.some.inj ((show peerAt w pid=some read by simp [peerAt,device,stored]).symm.trans found)
  subst read
  cases setter
  simp [peerAt,indexAt,device]

theorem clear_slot (pid : PeerId) (slot : KeySlot) (p : Peer) (found : peerAt w pid=some p)
    (a b : Ambient) (run : ((clearSlot pid slot).run w).run a=.ok (((),v),b)) :
    peerAt v pid=some (slot.clear p) ∧ Retains w v ∧
      ∀id∈(slot.get p).toList,Unpublished id v := by
  simp only [clearSlot,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨read,u,c,getter,ignored,t,e,updated,paid⟩ := run
  cases ignored
  obtain ⟨worldSame,ambientSame,d,device,stored⟩ := Origins.getPeer_return pid w u read a c getter
  subst u
  subst c
  have same : read=p := Option.some.inj ((show peerAt w pid=some read by simp [peerAt,device,stored]).symm.trans found)
  subst read
  obtain ⟨resident,index⟩ := update pid slot p found a e updated
  obtain ⟨kept,removed⟩ := put (slot.get p) true e b paid
  have peers := congrArg (fun maps=>maps.bind fun table=>table[pid]?) (put_peers (slot.get p) true t v e b paid)
  have pfinal : peerAt v pid=peerAt t pid := by
    simpa only [peersAt,peerAt,Option.bind_map,Function.comp_def] using peers
  exact ⟨pfinal.trans resident,(Retains.same index).trans kept,removed rfl⟩

def SlotEntries (p : Peer) : List KeypairId :=
  p.keypairNext.toList++p.keypairPrevious.toList++p.keypairCurrent.toList

/-- Each old slot is unpublished by its own native put; subsequent puts
only remove index entries, so aliases require no distinctness premise. -/
theorem clear (pid : PeerId) (p : Peer) (found : peerAt w pid=some p) (a b : Ambient)
    (run : ((keypairsClear pid).run w).run a=.ok (((),v),b)) :
    SlotsCleared pid v ∧ Retains w v ∧ ∀id∈SlotEntries p,Unpublished id v := by
  have slots := (hoare_iff_run_ambient _ _ _).mp (clear_slots pid) w a () v b True.intro run
  rw [clear_source] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨first,u,c,nextRun,second,t,e,previousRun,currentRun⟩ := run
  cases first
  cases second
  obtain ⟨pu,keepU,next⟩ := clear_slot pid .next p found a c nextRun
  obtain ⟨pt,keepT,previous⟩ := clear_slot pid .previous (KeySlot.next.clear p) pu c e previousRun
  obtain ⟨_,keepV,current⟩ := clear_slot pid .current (KeySlot.previous.clear (KeySlot.next.clear p)) pt e b currentRun
  refine ⟨slots,keepU.trans (keepT.trans keepV),?_⟩
  intro id member
  rcases List.mem_append.mp member with earlier | last
  · rcases List.mem_append.mp earlier with first | second
    · exact keepV id (keepT id (next id first))
    · exact keepV id (previous id second)
  · exact current id last

end Leanux.Proofs.WG.RetirementSecurity.Unpublication
