import Leanux.Proofs.WG.TransmitSecurity.StagedAvailabilityProduct

/-! Native product-state frames for staged provenance. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects AuthenticatedEffects.CausalJournal

theorem product_wg_store (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (before : Carrier h w.wg) : Carrier h v.wg := by
  have device := congrArg WGStoreView.dev same
  change v.wg.dev = w.wg.dev at device
  refine ⟨before.1.retains ?_ ?_,before.2⟩
  · simp only [Packets.epoch,device]
  · intro pid cell found
    simpa only [stagedAt,device] using found

theorem product_stable (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (before : Carrier h w.wg) : Carrier h v.wg := by
  have device := congrArg (fun s : ProductStore43 => s.2.2.2.dev) same
  change v.wg.dev = w.wg.dev at device
  refine ⟨before.1.retains ?_ ?_,before.2⟩
  · simp only [Packets.epoch,device]
  · intro pid cell found
    simpa only [stagedAt,device] using found

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductSafe (liftPrefix action) := by
  change PrefixEnsures (fun h w => Carrier h w.wg) Safe (liftPrefix action) (fun _ h w => Carrier h w.wg)
  apply PrefixEnsures.lift action (fun _ _ before => before.2)
  intro h w value v before run
  exact product_stable h w v ((ProjectedAction.iff_run _ _ _).mp same w value v run) before

theorem product_suffix_quiet {action : PrefixM Event α}
    (quiet : HistoryFrame allocation? action)
    (position : (runPrefix action w h).2 = h ++ suffix) :
    ∀ event ∈ suffix, allocation? event = none := by
  have same := quiet w h
  rw [position,List.filterMap_append] at same
  have empty : suffix.filterMap allocation? = [] := by
    have sizes := congrArg List.length same
    cases found : suffix.filterMap allocation? with
    | nil => rfl
    | cons x xs => simp only [List.length_append,found,List.length_cons] at sizes; omega
  intro event member
  cases found : allocation? event with
  | none => rfl
  | some value =>
    have present := List.mem_filterMap.mpr ⟨event,member,found⟩
    rw [empty] at present
    cases present

theorem product_quiet {action : PrefixM Event α} {native : Leanux.M α}
    (appends : Appends action) (quiet : HistoryFrame allocation? action)
    (erase : ErasesPrefix action native)
    (kept : ∀ h, Preserves (fun w : World => Inv h w.wg) native) : ProductSafe action := by
  intro w h before
  obtain ⟨suffix,position⟩ := appends w h
  have excluded := product_suffix_quiet quiet position
  have safe : Safe (runPrefix action w h).2 := by
    rw [position]
    exact before.2.quiet excluded
  refine ⟨suffix,position,safe,?_⟩
  cases outcome : (runPrefix action w h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    have run : native w = .ok (value,v) := (erase w h).symm.trans outcome
    have inv := (hoare_iff_run _ _ _).mp (kept h) w value v before.1 run
    refine ⟨?_,safe⟩
    rw [position]
    exact inv.append (fun _ event member => no_use (excluded event member))

theorem product_lift (action : Leanux.M α)
    (native : ∀ h, Preserves (fun w : World => Inv h w.wg) action) : ProductSafe (liftPrefix action) :=
  product_quiet (Appends.lift _) (HistoryFrame.lift _ _) (erasesPrefix_lift _) native

theorem product_history {action : PrefixM Event α} {native : Leanux.M α}
    (history : Driver.ProductHistorySafe Safe action) (erase : ErasesPrefix action native)
    (kept : ∀ h, Preserves (fun w : World => Inv h w.wg) native)
    (quiet : HistoryFrame allocation? action) : ProductSafe action := by
  intro w h before
  obtain ⟨suffix,position,safe,_⟩ := history w h before.2
  have excluded := product_suffix_quiet quiet position
  refine ⟨suffix,position,safe,?_⟩
  cases outcome : (runPrefix action w h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨value,v⟩ := out
    have run : native w = .ok (value,v) := (erase w h).symm.trans outcome
    have inv := (hoare_iff_run _ _ _).mp (kept h) w value v before.1 run
    refine ⟨?_,safe⟩
    rw [position]
    exact inv.append (fun _ event member => no_use (excluded event member))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Availability
