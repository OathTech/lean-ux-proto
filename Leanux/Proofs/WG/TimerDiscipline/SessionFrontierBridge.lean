import Leanux.Proofs.WG.TimerDiscipline.SessionCounterFrames
import Leanux.Proofs.WG.TimerDiscipline.SessionFrontierSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
theorem observer_frontier {α : Type} (observer : PrefixM Event α) (action : Leanux.M α)
    (append : Appends observer) (erase : ErasesPrefix observer action)
    (silent : HistoryFrame Event.sessionId observer) (grow : ProductCounterMono action) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered observer := by
  intro w h prior
  obtain ⟨suffix,appended⟩:=append w h
  have ids:=silent w h
  have ordered : Ordered (runPrefix observer w h).2 := by
    change ((runPrefix observer w h).2.filterMap Event.sessionId).Pairwise (·<·)
    rw [ids]
    exact prior.1
  refine ⟨suffix,appended,ordered,?_⟩
  cases outcome : (runPrefix observer w h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,final⟩:=out
    change Frontier (runPrefix observer w h).2 final.wg.keypairCounter
    refine ⟨ordered,?_⟩
    intro serial member
    change serial∈(runPrefix observer w h).2.filterMap Event.sessionId at member
    rw [ids] at member
    exact Nat.le_trans (prior.2 serial member)
      (grow w value final ((erase w h).symm.trans outcome))

theorem focus_frontier {α : Type} (observer : PrefixM HookJournal.Receipt α) (action : Leanux.M α)
    (erase : ErasesPrefix observer action) (grow : ProductCounterMono action) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (focusPrefix Event.hook decodeHook observer) :=
  observer_frontier _ _ (Appends.focus _ _ _) (focusPrefix_erases _ _ erase)
    (focusPrefix_other _ _ _ (fun _=>rfl) _) grow

theorem quiet_frontier {α : Type} (action : Leanux.M α) (grow : ProductCounterMono action) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (liftPrefix action) :=
  observer_frontier _ _ (Appends.lift _) (erasesPrefix_lift _) (fun _ _=>rfl) grow

theorem native_observer_frontier {α : Type} (observer : WGPrefix Event α) (action : WG.M α)
    (append : StateAppends observer) (erase : ErasesStatePrefix observer action)
    (silent : StateHistoryFrame Event.sessionId observer) (grow : CounterMono action) :
    StatePrefixPreserves (fun h g _=>Frontier h g.keypairCounter) Ordered observer := by
  intro g a h prior
  obtain ⟨suffix,appended⟩:=append g a h
  have ids:=silent g a h
  have ordered : Ordered (runPrefix (observer.run g) a h).2 := by
    change ((runPrefix (observer.run g) a h).2.filterMap Event.sessionId).Pairwise (·<·)
    rw [ids]
    exact prior.1
  refine ⟨suffix,appended,ordered,?_⟩
  cases outcome : (runPrefix (observer.run g) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,final⟩,after⟩:=out
    change Frontier (runPrefix (observer.run g) a h).2 final.keypairCounter
    refine ⟨ordered,?_⟩
    intro serial member
    change serial∈(runPrefix (observer.run g) a h).2.filterMap Event.sessionId at member
    rw [ids] at member
    exact Nat.le_trans (prior.2 serial member)
      (grow g a value final after ((erase g a h).symm.trans outcome))
end Leanux.Proofs.WG.TimerDiscipline.HandshakeJournal
