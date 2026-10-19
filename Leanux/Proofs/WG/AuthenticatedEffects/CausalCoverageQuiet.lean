import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageScopes

/-! Unscoped observers are admitted only when their actual appended event range
contains no delayed effect or allocation. This cannot authorize arbitrary old
callbacks: allocation's event projection is explicitly excluded. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def allocation? : Journal.Event → Option Unit
  | .allocated _ _ => some ()
  | _ => none

theorem old_quiet (event : Journal.Event) (absent : allocation? event = none) : ¬ Protected (.old event) := by
  cases event <;> simp_all [allocation?,Protected]

private theorem suffix_quiet (history suffix : List Journal.Event)
    (same : (history ++ suffix).filterMap allocation? = history.filterMap allocation?) :
    ∀ event ∈ suffix, allocation? event = none := by
  have empty : suffix.filterMap allocation? = [] := by
    have sizes := congrArg List.length same
    simp only [List.filterMap_append,List.length_append] at sizes
    exact List.eq_nil_of_length_eq_zero (by omega)
  intro event member
  cases value : allocation? event with
  | none => rfl
  | some marker =>
    have included : marker ∈ suffix.filterMap allocation? := List.mem_filterMap.mpr ⟨event,member,value⟩
    rw [empty] at included
    cases included

theorem old_product_quiet {State : Type} (body : PrefixT Journal.Event State α) (appends : Appends body)
    (quiet : HistoryFrame allocation? body) :
    PrefixEnsures (fun h (_ : State) => Inv frames h) Safe (focusPrefix Event.old old? body)
      (fun _ h (_ : State) => Inv frames h) := by
  intro w h ready
  obtain ⟨suffix,grown⟩ := appends w (h.filterMap old?)
  have frame := quiet w (h.filterMap old?)
  rw [grown] at frame
  have absent := suffix_quiet _ suffix frame
  have good := ready.quiet (suffix.map Event.old) (by
    intro event member
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp member
    rfl) (by
    intro event member
    obtain ⟨original,found,rfl⟩ := List.mem_map.mp member
    intro relevant
    exact (old_quiet original (absent original found) relevant).elim)
  have run := focusPrefix_suffix Event.old old? body w h _ suffix (Prod.ext rfl grown)
  rw [run]
  refine ⟨suffix.map Event.old,rfl,good.1,?_⟩
  cases (runPrefix body w (h.filterMap old?)).1 <;> trivial

theorem old_state_quiet (body : WGPrefix Journal.Event α) (appends : StateAppends body)
    (quiet : StateHistoryFrame allocation? body) : StateAt frames (state body) := by
  intro w a h ready
  exact old_product_quiet (frames := frames) (body.run w) (appends w) (quiet w) a h ready

theorem counter (skb : SkbId) (packet : RxPacket) : ProductAt frames (hooks.counterCheck skb packet) := by
  apply old_product_quiet
  · exact Appends.receiptObserved (Appends.lift _)
  · exact HistoryFrame.receiptObserved (HistoryFrame.lift allocation? _) (fun _ => rfl)

theorem prepare : ProductAt frames hooks.prepare := by
  apply old_product_quiet
  · exact Appends.focus _ _ _
  · exact focusPrefix_other Journal.Event.rxOrigin Journal.origin? allocation? (fun _ => rfl) _

theorem poll : ProductAt frames hooks.poll := by
  apply old_product_quiet
  · exact Appends.receiptObserved (Appends.focus _ _ _)
  · exact HistoryFrame.receiptObserved
      (focusPrefix_other Journal.Event.ring Journal.ring? allocation? (fun _ => rfl) _) (fun _ => rfl)

theorem encrypt (item : Option (List SkbId)) : ProductAt frames (hooks.encrypt item) := by
  apply old_product_quiet
  · exact Appends.receiptObserved (Appends.focus _ _ _)
  · exact HistoryFrame.receiptObserved
      (focusPrefix_other Journal.Event.encrypted Journal.encryption? allocation? (fun _ => rfl) _) (fun _ => rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
