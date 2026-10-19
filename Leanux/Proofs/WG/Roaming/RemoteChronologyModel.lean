import Leanux.Proofs.WG.Roaming.RemoteOriginModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteChronology
open Leanux Leanux.WG

abbrev Remote := Nat × Nat × Nat × Nat
abbrev Effect (E : Type) := E → PeerId → Option (Option Remote)

def Untouched {E : Type} (effect : Effect E) (events : List E) (pid : PeerId) : Prop :=
  ∀ event ∈ events, effect event pid = none

def Last {E : Type} (effect : Effect E) (entry : RemoteMap)
    (events : List E) (final : RemoteMap) : Prop :=
  ∀ pid remote, final pid = some remote →
    (entry pid = some remote ∧ Untouched effect events pid) ∨
    ∃ before event after, events = before ++ event :: after ∧
      effect event pid = some (some remote) ∧ Untouched effect after pid

def applyEffect {E : Type} (effect : Effect E) (event : E) (entry : RemoteMap) : RemoteMap :=
  fun pid => match effect event pid with
    | none => entry pid
    | some endpoint => endpoint

theorem untouched_append {E : Type} (effect : Effect E) (left right : List E) (pid : PeerId) :
    Untouched effect (left ++ right) pid ↔
      Untouched effect left pid ∧ Untouched effect right pid := by
  constructor
  · intro h
    exact ⟨fun e member => h e (List.mem_append_left _ member),
      fun e member => h e (List.mem_append_right _ member)⟩
  · rintro ⟨hl,hr⟩ e member
    rcases List.mem_append.mp member with member | member
    · exact hl e member
    · exact hr e member

theorem nil_of_retained {E : Type} (effect : Effect E) {entry final : RemoteMap}
    (kept : RemoteRetained entry final) : Last effect entry [] final := by
  intro pid remote present
  exact Or.inl ⟨kept pid remote present,by intro e member; cases member⟩

theorem retained {E : Type} {effect : Effect E} {entry middle final : RemoteMap}
    {events : List E} (prior : Last effect entry events middle)
    (kept : RemoteRetained middle final) : Last effect entry events final :=
  fun pid remote present => prior pid remote (kept pid remote present)

theorem append {E : Type} {effect : Effect E} {entry middle final : RemoteMap}
    {left right : List E} (first : Last effect entry left middle)
    (second : Last effect middle right final) : Last effect entry (left ++ right) final := by
  intro pid remote present
  rcases second pid remote present with ⟨old,quiet⟩ | ⟨before,event,after,shape,set,last⟩
  · rcases first pid remote old with ⟨initial,allQuiet⟩ | ⟨before,event,after,shape,set,last⟩
    · exact Or.inl ⟨initial,(untouched_append effect left right pid).mpr ⟨allQuiet,quiet⟩⟩
    · refine Or.inr ⟨before,event,after ++ right,?_,set,?_⟩
      · rw [shape,List.append_assoc,List.cons_append]
      · exact (untouched_append effect after right pid).mpr ⟨last,quiet⟩
  · refine Or.inr ⟨left ++ before,event,after,?_,set,last⟩
    rw [shape,List.append_assoc]

theorem singleton {E : Type} (effect : Effect E) (event : E) (entry : RemoteMap) :
    Last effect entry [event] (applyEffect effect event entry) := by
  intro pid remote present
  cases applied : effect event pid with
  | none =>
    exact Or.inl ⟨by simpa [applyEffect,applied] using present,
      by
        intro e member
        have same : e = event := by simpa using member
        subst e
        exact applied⟩
  | some endpoint =>
    have endpointEq : endpoint = some remote := by simpa [applyEffect,applied] using present
    exact Or.inr ⟨[],event,[],rfl,by rw [applied,endpointEq],by intro e member; cases member⟩

theorem receipt {E : Type} {effect : Effect E} {entry middle final : RemoteMap}
    {events : List E} (prior : Last effect entry events middle) (event : E)
    (kept : RemoteRetained (applyEffect effect event middle) final) :
    Last effect entry (events ++ [event]) final :=
  append prior (retained (singleton effect event middle) kept)

theorem empty_origin {E : Type} {effect : Effect E} {events : List E} {final : RemoteMap}
    (covered : Last effect (fun _ => none) events final) (pid : PeerId) (remote : Remote)
    (present : final pid = some remote) :
    ∃ before event after, events = before ++ event :: after ∧
      effect event pid = some (some remote) ∧ Untouched effect after pid := by
  rcases covered pid remote present with ⟨absent,_⟩ | actual
  · cases absent
  · exact actual

def replay {E : Type} (effect : Effect E) (entry : RemoteMap) : List E → RemoteMap
  | [] => entry
  | event :: rest => replay effect (applyEffect effect event entry) rest

theorem replay_append {E : Type} (effect : Effect E) (entry : RemoteMap) (left right : List E) :
    replay effect entry (left ++ right) = replay effect (replay effect entry left) right := by
  induction left generalizing entry with
  | nil => rfl
  | cons event rest ih => exact ih (applyEffect effect event entry)

theorem replay_untouched {E : Type} (effect : Effect E) (entry : RemoteMap)
    (events : List E) (pid : PeerId) (quiet : Untouched effect events pid) :
    replay effect entry events pid = entry pid := by
  induction events generalizing entry with
  | nil => rfl
  | cons event rest ih =>
    have head := quiet event (by simp)
    have tail : Untouched effect rest pid := fun e member => quiet e (List.mem_cons_of_mem _ member)
    rw [replay,ih _ tail]
    simp only [applyEffect,head]

theorem replay_last {E : Type} (effect : Effect E) (entry : RemoteMap) (events : List E) :
    Last effect entry events (replay effect entry events) := by
  induction events generalizing entry with
  | nil => exact nil_of_retained effect (.refl entry)
  | cons event rest ih =>
    exact append (singleton effect event entry) (ih (applyEffect effect event entry))

theorem last_to_replay {E : Type} {effect : Effect E} {entry final : RemoteMap}
    {events : List E} (covered : Last effect entry events final) :
    RemoteRetained (replay effect entry events) final := by
  intro pid remote present
  rcases covered pid remote present with ⟨old,quiet⟩ | ⟨before,event,after,shape,set,last⟩
  · rw [replay_untouched effect entry events pid quiet]
    exact old
  · rw [shape,replay_append]
    change replay effect (applyEffect effect event (replay effect entry before)) after pid = some remote
    rw [replay_untouched effect _ after pid last]
    simp only [applyEffect,set]

theorem last_iff_replay {E : Type} {effect : Effect E} {entry final : RemoteMap}
    {events : List E} :
    Last effect entry events final ↔ RemoteRetained (replay effect entry events) final :=
  ⟨last_to_replay,fun kept => retained (replay_last effect entry events) kept⟩

theorem reset_last {E : Type} {effect : Effect E} {entry final : RemoteMap}
    {events : List E} (event : E) (pid : PeerId)
    (reset : effect event pid = some none)
    (covered : Last effect entry (events ++ [event]) final) :
    final pid = none := by
  cases present : final pid with
  | none => rfl
  | some remote =>
    have impossible := last_to_replay covered pid remote present
    rw [replay_append] at impossible
    simp only [replay,applyEffect,reset] at impossible
    cases impossible

theorem set_last {E : Type} {effect : Effect E} {entry final : RemoteMap}
    {events : List E} (event : E) (pid : PeerId) (remote : Remote)
    (set : effect event pid = some (some remote))
    (covered : Last effect entry (events ++ [event]) final) :
    ∀ value, final pid = some value → value = remote := by
  intro value present
  have same := last_to_replay covered pid value present
  rw [replay_append] at same
  simpa only [replay,applyEffect,set,Option.some.injEq] using same.symm

theorem quiet_append {E : Type} {effect : Effect E} {entry middle final : RemoteMap}
    {left right : List E} (prior : Last effect entry left middle)
    (quiet : ∀ pid, Untouched effect right pid) (kept : RemoteRetained middle final) :
    Last effect entry (left ++ right) final := by
  apply append prior
  intro pid remote present
  exact Or.inl ⟨kept pid remote present,quiet pid⟩

/-- A projected boundary certificate for one actual completed setter, reset,
or silent action. Source validity is a separate requirement. -/
def CutRetained {E : Type} (effect : Effect E) (event : E)
    (before after : Campaign2.Snapshot) : Prop :=
  RemoteRetained (applyEffect effect event (remoteMap before)) (remoteMap after)

theorem cut {E : Type} {effect : Effect E} {entry : RemoteMap} {events : List E}
    {before after : Campaign2.Snapshot} (prior : Last effect entry events (remoteMap before))
    (event : E) (effectAtCut : CutRetained effect event before after) :
    Last effect entry (events ++ [event]) (remoteMap after) :=
  receipt prior event effectAtCut

theorem exact_cut {E : Type} {effect : Effect E} {entry : RemoteMap} {events : List E}
    {before after : Campaign2.Snapshot} (prior : Last effect entry events (remoteMap before))
    (event : E) (effectAtCut : remoteMap after = applyEffect effect event (remoteMap before)) :
    Last effect entry (events ++ [event]) (remoteMap after) :=
  receipt prior event (RemoteRetained.of_eq effectAtCut)

theorem forget {E : Type} {effect : Effect E} {entry final : RemoteMap}
    {events : List E} (cause : E → PeerId → Remote → Prop)
    (origin : ∀ e pid remote, effect e pid = some (some remote) → cause e pid remote)
    (covered : Last effect entry events final) : RemoteCovered entry cause events final := by
  intro pid remote present
  rcases covered pid remote present with ⟨old,_⟩ | ⟨before,event,after,shape,set,_⟩
  · exact Or.inl old
  · refine Or.inr ⟨event,?_,origin event pid remote set⟩
    rw [shape]
    exact List.mem_append_right _ (by simp)

end Leanux.Proofs.WG.Roaming.RemoteChronology
