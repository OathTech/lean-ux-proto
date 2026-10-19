import Leanux.Proofs.WG.RetirementSecurity.TxWorkEncrypt

/-! Pending TX actors are read from the actual suspended Activation records.
Yield, resume and cryptAhead's iteration increment transfer those actor
obligations without manufacturing an independent scheduler. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def actor (act : Activation) : Option PeerId :=
  match act.worker with
  | .txWorker=>act.pid
  | _=>none

def actors (suspended : List Activation) : List PeerId := suspended.filterMap actor

theorem actor_increment (act : Activation) : actor {act with iterations:=act.iterations+1}=actor act := rfl

theorem actor_beq (left right : Activation) (same : (left == right)=true) : actor left=actor right := by
  obtain ⟨kind,pid,iterations⟩:=left
  obtain ⟨other,q,steps⟩:=right
  change (kind.ctorIdx == other.ctorIdx && (pid == q && iterations == steps))=true at same
  cases kind <;> cases other <;> simp_all [actor,Worker.ctorIdx]

theorem actors_resume (act : Activation) (pending : pid∈actors suspended) :
    pid∈(actor act).toList++actors (suspended.filter (· != act)) := by
  obtain ⟨saved,member,named⟩:=List.mem_filterMap.mp pending
  by_cases same:(saved == act)=true
  · have selected:actor act=some pid := (actor_beq saved act same).symm.trans named
    simp [selected]
  · apply List.mem_append_right
    apply List.mem_filterMap.mpr
    exact ⟨saved,List.mem_filter.mpr ⟨member,by
      change (!(saved == act))=true
      cases value:(saved == act) <;> simp_all⟩,named⟩

theorem suspend (before : Obligations crypt ((actor act).toList++actors w.ambient.suspended) w.wg)
    (run : (modifyAmbient fun s=>{s with suspended:=s.suspended++[{act with iterations:=act.iterations+1}]} :
      Leanux.M Unit).run w=.ok ((),v)) :
    Obligations crypt (actors v.ambient.suspended) v.wg := by
  cases run
  apply before.actor_cover
  intro pid pending
  simp only [actors,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,actor_increment] at pending ⊢
  cases selected:actor act with
  | none=>simpa only [selected,Option.toList_none,List.nil_append,List.append_nil] using pending
  | some q=>
    simp only [selected,Option.toList_some,List.singleton_append,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at pending ⊢
    rcases pending with queued | selected | suspended
    · exact .inl queued
    · exact .inr (.inr selected)
    · exact .inr (.inl suspended)

theorem resume (before : Obligations crypt (actors w.ambient.suspended) w.wg)
    (act : Activation)
    (run : (modifyAmbient fun s=>{s with suspended:=s.suspended.filter (· != act)} : Leanux.M Unit).run w=
      .ok ((),v)) :
    Obligations crypt ((actor act).toList++actors v.ambient.suspended) v.wg := by
  cases run
  apply before.actor_cover
  intro pid pending
  rcases List.mem_append.mp pending with queued | waiting
  · exact List.mem_append_left _ queued
  · exact List.mem_append_right _ (actors_resume act waiting)

theorem actors_increment (suspended : List Activation) (selected : Activation) :
    actors (suspended.map fun act=>if act == selected then {act with iterations:=act.iterations+1} else act)=
      actors suspended := by
  induction suspended with
  | nil=>rfl
  | cons head rest ih=>
    have same:actor (if head == selected then {head with iterations:=head.iterations+1} else head)=actor head := by
      split <;> rfl
    simp only [List.map_cons,actors,List.filterMap_cons] at ih ⊢
    rw [same,ih]

theorem crypt_increment (before : Obligations crypt (active++actors w.ambient.suspended) w.wg)
    (selected : Activation)
    (run : (modifyAmbient fun s=>{s with suspended:=s.suspended.map fun act=>
      if act == selected then {act with iterations:=act.iterations+1} else act} : Leanux.M Unit).run w=
      .ok ((),v)) :
    Obligations crypt (active++actors v.ambient.suspended) v.wg := by
  cases run
  simpa only [actors_increment] using before

end Leanux.Proofs.WG.RetirementSecurity.TxWork
