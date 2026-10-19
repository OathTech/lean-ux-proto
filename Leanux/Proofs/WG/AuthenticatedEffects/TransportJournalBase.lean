import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierOuter
import Leanux.Proofs.WG.TransmitSecurity.JournalHandshakeProjection

/-! Native endpoint frames and quiet history belong to the same observer.
No chronology is inferred by comparing two erased executions. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity TransportCarrier
variable {E F : Type} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay}

theorem state_erases {g : WGPrefix E α} {action : WG.M α}
    (ρ : E → Option F) (projection : StateProjectsPrefix ρ id g (liftWGPrefix action)) :
    ErasesStatePrefix g action := by
  intro w a h
  have result := congrArg Prod.fst (projection w a h)
  change (action.run w).run a = Except.map id _ at result
  simpa only [Except.map_id,id_eq] using result.symm

theorem product_erases {g : PrefixM E α} {action : Leanux.M α}
    (ρ : E → Option F) (projection : ProjectsPrefix ρ id g (liftPrefix action)) :
    ErasesPrefix g action := by
  intro w h
  have result := congrArg Prod.fst (projection w h)
  change action.run w = Except.map id _ at result
  simpa only [Except.map_id,id_eq] using result.symm

theorem state_history {g : WGPrefix E α} (app : StateAppends g)
    (quiet : StateHistoryFrame replay g) :
    StatePrefixPreserves (fun h _ _ => TransportReplay.Safe origin replay h ∧ True)
      (fun h => TransportReplay.Safe origin replay h ∧ True) g := by
  intro w a h hi
  obtain ⟨suffix,appended⟩ := app w a h
  have frame := quiet w a h
  rw [appended,List.filterMap_append] at frame
  have empty : suffix.filterMap replay = [] := by simpa using frame
  have safe := appended.symm ▸ hi.1.quiet empty
  refine ⟨suffix,appended,⟨safe,True.intro⟩,?_⟩
  split <;> trivial

theorem state_quiet {g : WGPrefix E α} {action : WG.M α}
    (app : StateAppends g) (quiet : StateHistoryFrame replay g)
    (erases : ErasesStatePrefix g action)
    (frame : SameView RxDisposition.nativeRxStore action) :
    StateSafe (fun _ => True) origin replay g :=
  state_observed g action erases (state_history app quiet)
    (TransportPublication.preserves_of_rx action frame)

theorem product_quiet {g : PrefixM E α} {action : Leanux.M α}
    (app : Appends g) (quiet : HistoryFrame replay g) (erases : ErasesPrefix g action)
    (frame : SameView RxDisposition.rxStore action) :
    ProductSafe (fun _ => True) origin replay g :=
  product_combine g (TransportReplay.quiet_observed g action app erases quiet
    (TransportPublication.product_preserves_of_rx action frame))
    (fun w h _ => by
      obtain ⟨suffix,eq⟩ := app w h
      exact ⟨suffix,eq,True.intro,by split <;> trivial⟩)

end Leanux.Proofs.WG.AuthenticatedEffects.TransportJournal
