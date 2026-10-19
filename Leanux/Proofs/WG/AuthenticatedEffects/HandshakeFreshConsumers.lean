import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFreshHistory

/-! Successful native consumers install a fresh last admission before any
protected callback. A later failed continuation retains its actual admission
without synthesizing a successful consumer return. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing HandshakeCausal

theorem initiation_run (mac : HandshakeMac) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (HandshakeCausal.initiation mac) w a h =
      match ((initiationAcceptedCheck mac.input).run w).run a with
      | .error error => (.error error,h)
      | .ok ((accepted,u),b) =>
        (((initiationAcceptedContinue mac.input accepted).run u).run b,
          if accepted.isSome then h ++ [.admission (.initiation mac ⟨accepted,w,u,a,b⟩)] else h) := by
  change ((runWGPrefix (admitInitiation mac) w a (h.filterMap admission)).1,
    h ++ ((runWGPrefix (admitInitiation mac) w a (h.filterMap admission)).2.drop
      (h.filterMap admission).length).map Event.admission) = _
  rw [admitInitiation_run]
  cases ((initiationAcceptedCheck mac.input).run w).run a with
  | error error => simp only [List.drop_length,List.map_nil,List.append_nil]
  | ok output =>
    rcases output with ⟨⟨accepted,u⟩,b⟩
    cases accepted <;> simp only [Option.isSome_none,Option.isSome_some,Bool.false_eq_true,↓reduceIte,
      List.drop_length,List.drop_left,List.map_nil,List.map_cons,List.append_nil]

theorem initiation_post (mac : HandshakeMac) (valid : mac.Valid) :
    StatePrefixEnsures Inv Safe (HandshakeCausal.initiation mac)
      (fun result h _ _ => Safe h ∧ ∀ pid, result = some pid → Available h pid) := by
  intro w a h safe
  have observed := initiation_run mac w a h
  change runPrefix ((HandshakeCausal.initiation mac).run w) a h = _ at observed
  rw [observed]
  cases checked : ((initiationAcceptedCheck mac.input).run w).run a with
  | error error => exact ⟨[],by simp,safe,True.intro⟩
  | ok output =>
    rcases output with ⟨⟨accepted,u⟩,b⟩
    cases accepted with
    | none =>
      change ∃ suffix, h = h ++ suffix ∧ Safe h ∧ Safe h ∧
        ∀ pid, (none : Option PeerId) = some pid → Available h pid
      exact ⟨[],by simp,safe,safe,by intro pid impossible; cases impossible⟩
    | some accepted =>
      simp only [Option.isSome_some,↓reduceIte,initiationAcceptedContinue]
      let receipt : HandshakeAdmission := .initiation mac ⟨some accepted,w,u,a,b⟩
      have good : Safe (h ++ [.admission receipt]) := safe.quiet rfl
      refine ⟨[.admission receipt],rfl,good,?_⟩
      cases finished : ((initiationAcceptedFinish mac.input accepted).run u).run b with
      | error error => trivial
      | ok result =>
        rcases result with ⟨⟨result,v⟩,c⟩
        refine ⟨good,?_⟩
        intro pid same
        have returned := (hoare_iff_run_ambient _ _ _).mp (initiation_finish_result mac.input accepted)
          u b result v c True.intro finished
        have peer : accepted.peer = pid := Option.some.inj (returned.symm.trans same)
        exact ⟨h,receipt,[],rfl,rfl,⟨valid,checked,rfl⟩,accepted,rfl,peer⟩

theorem response_run (mac : HandshakeMac) (w : WGWorld) (a : Ambient) (h : List Event) :
    runWGPrefix (HandshakeCausal.response mac) w a h =
      match ((responseAcceptedCheck mac.input).run w).run a with
      | .error error => (.error error,h)
      | .ok ((accepted,u),b) =>
        (((responseAcceptedContinue mac.input accepted).run u).run b,
          if accepted.isSome then h ++ [.admission (.response mac ⟨accepted,w,u,a,b⟩)] else h) := by
  change ((runWGPrefix (admitResponse mac) w a (h.filterMap admission)).1,
    h ++ ((runWGPrefix (admitResponse mac) w a (h.filterMap admission)).2.drop
      (h.filterMap admission).length).map Event.admission) = _
  rw [admitResponse_run]
  cases ((responseAcceptedCheck mac.input).run w).run a with
  | error error => simp only [List.drop_length,List.map_nil,List.append_nil]
  | ok output =>
    rcases output with ⟨⟨accepted,u⟩,b⟩
    cases accepted <;> simp only [Option.isSome_none,Option.isSome_some,Bool.false_eq_true,↓reduceIte,
      List.drop_length,List.drop_left,List.map_nil,List.map_cons,List.append_nil]

theorem response_post (mac : HandshakeMac) (valid : mac.Valid) :
    StatePrefixEnsures Inv Safe (HandshakeCausal.response mac)
      (fun result h _ _ => Safe h ∧ ∀ pid, result = some pid → Available h pid) := by
  intro w a h safe
  have observed := response_run mac w a h
  change runPrefix ((HandshakeCausal.response mac).run w) a h = _ at observed
  rw [observed]
  cases checked : ((responseAcceptedCheck mac.input).run w).run a with
  | error error => exact ⟨[],by simp,safe,True.intro⟩
  | ok output =>
    rcases output with ⟨⟨accepted,u⟩,b⟩
    cases accepted with
    | none =>
      change ∃ suffix, h = h ++ suffix ∧ Safe h ∧ Safe h ∧
        ∀ pid, (none : Option PeerId) = some pid → Available h pid
      exact ⟨[],by simp,safe,safe,by intro pid impossible; cases impossible⟩
    | some accepted =>
      simp only [Option.isSome_some,↓reduceIte,responseAcceptedContinue]
      let receipt : HandshakeAdmission := .response mac ⟨some accepted,w,u,a,b⟩
      have good : Safe (h ++ [.admission receipt]) := safe.quiet rfl
      refine ⟨[.admission receipt],rfl,good,?_⟩
      cases finished : ((responseAcceptedFinish mac.input accepted).run u).run b with
      | error error => trivial
      | ok result =>
        rcases result with ⟨⟨result,v⟩,c⟩
        refine ⟨good,?_⟩
        intro pid same
        have returned := (hoare_iff_run_ambient _ _ _).mp (response_finish_result mac.input accepted)
          u b result v c True.intro finished
        have peer : accepted.peer = pid := Option.some.inj (returned.symm.trans same)
        exact ⟨h,receipt,[],rfl,rfl,⟨valid,checked,rfl⟩,accepted,rfl,peer⟩

end Leanux.Proofs.WG.AuthenticatedEffects.HandshakeFresh
