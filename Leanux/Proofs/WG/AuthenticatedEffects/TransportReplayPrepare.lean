import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayNative

/-! Native preparation establishes packet authentication at its exact
publication journal, while every previously checked replay keeps its position. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
variable {E : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay}

theorem prepare_checked (record : TransportDriver.OriginEvent → E)
    (origin : E → Option TransportDriver.OriginEvent) (replay : E → Option TransportDriver.Replay)
    (inverse : ∀ event, origin (record event) = some event) (quiet : ∀ event, replay (record event) = none) :
    Preserves (origin := origin) (replay := replay) (TransportDriver.prepare record origin) := by
  intro w h hi
  obtain ⟨suffix,appended,_,post⟩ := TransportPublication.prepare_preserves record origin inverse w h hi.1
  have history := focusPrefix_other record origin replay quiet (liftWGObserver RxOrigin.prepare) w h
  change (runPrefix (TransportDriver.prepare record origin) w h).2.filterMap replay = h.filterMap replay at history
  rw [appended,List.filterMap_append] at history
  have empty : suffix.filterMap replay = [] := by simpa using history
  have safe : Safe origin replay (runPrefix (TransportDriver.prepare record origin) w h).2 :=
    appended.symm ▸ hi.2.quiet empty
  refine ⟨suffix,appended,safe,?_⟩
  cases run : (runPrefix (TransportDriver.prepare record origin) w h).1 with
  | error err => trivial
  | ok out => exact ⟨by simpa only [run] using post,safe⟩

/-- A quiet observer may change arbitrary non-RX state and append other
observations. The exact normal native run supplies the state frame; the same
observer's append and replay projection supply its retained history. -/
theorem quiet_observed (g : PrefixM E α) (action : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g action) (quiet : HistoryFrame replay g)
    (frames : ∀ h, Leanux.Proofs.Framing.Preserves
      (fun w : World => TransportPublication.Inv h w.wg) action) :
    Preserves (origin := origin) (replay := replay) g := by
  intro w h hi
  obtain ⟨suffix,appended⟩ := appends w h
  have history := quiet w h
  rw [appended,List.filterMap_append] at history
  have empty : suffix.filterMap replay = [] := by simpa using history
  have safe : Safe origin replay (runPrefix g w h).2 := appended.symm ▸ hi.2.quiet empty
  refine ⟨suffix,appended,safe,?_⟩
  cases run : (runPrefix g w h).1 with
  | error err => trivial
  | ok out =>
    rcases out with ⟨value,v⟩
    have carrier := (hoare_iff_run _ _ _).mp (frames (h.filterMap origin))
      w value v hi.1 ((erases w h).symm.trans run)
    refine ⟨?_,safe⟩
    rw [appended,List.filterMap_append]
    exact carrier.append _

end Leanux.Proofs.WG.AuthenticatedEffects.TransportReplay
