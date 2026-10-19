import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixQuiet

/-! Reuse native endpoint companions only beside an independently proved
prefix certificate for the same body. A quiet adapter requires literal journal
preservation; absence of births alone is insufficient. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
open Leanux Leanux.Proofs.Logged

theorem Ensures.join
    (prefixes : Ensures P Safe body Q)
    (endpoint : PrefixEnsures P' Safe body Q')
    (pre : ∀ h w, P' h w→P h w) : Ensures P' Safe body Q' := by
  intro w h before
  obtain ⟨suffix,extended,_,kept⟩ := endpoint w h before.1
  have all := prefixes.output (pre h w before.1) before.2
  refine ⟨suffix,extended,all,?_⟩
  cases result : (runPrefix body w h).1 with
  | error reason => trivial
  | ok out =>
    rw [result] at kept
    exact ⟨kept,all⟩

theorem StateEnsures.join
    (prefixes : StateEnsures P Safe body Q)
    (endpoint : StatePrefixEnsures P' Safe body Q')
    (pre : ∀ h w a, P' h w a→P h w a) : StateEnsures P' Safe body Q' := by
  intro w a h before
  obtain ⟨suffix,extended,_,kept⟩ := endpoint w a h before.1
  obtain ⟨_,_,all,_⟩ := prefixes w a h ⟨pre h w a before.1,before.2⟩
  refine ⟨suffix,extended,all,?_⟩
  cases result : (runPrefix (body.run w) a h).1 with
  | error reason => trivial
  | ok out =>
    rw [result] at kept
    exact ⟨kept,all⟩

theorem Ensures.quiet (endpoint : PrefixEnsures P Safe body Q)
    (quiet : ∀ w h, (runPrefix body w h).2=h) : Ensures P Safe body Q := by
  intro w h before
  obtain ⟨suffix,extended,_,kept⟩ := endpoint w h before.1
  have all : All Safe (runPrefix body w h).2 := (quiet w h).symm ▸ before.2
  refine ⟨suffix,extended,all,?_⟩
  cases result : (runPrefix body w h).1 with
  | error reason => trivial
  | ok out =>
    rw [result] at kept
    exact ⟨kept,all⟩

theorem StateEnsures.quiet (endpoint : StatePrefixEnsures P Safe body Q)
    (quiet : ∀ w a h, (runStatePrefix body w a h).2=h) : StateEnsures P Safe body Q := by
  intro w a h before
  obtain ⟨suffix,extended,_,kept⟩ := endpoint w a h before.1
  have all : All Safe (runStatePrefix body w a h).2 := (quiet w a h).symm ▸ before.2
  refine ⟨suffix,extended,all,?_⟩
  cases result : (runPrefix (body.run w) a h).1 with
  | error reason => trivial
  | ok out =>
    rw [result] at kept
    exact ⟨kept,all⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
