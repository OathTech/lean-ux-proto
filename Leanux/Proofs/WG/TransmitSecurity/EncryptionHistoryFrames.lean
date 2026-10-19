import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryQuiet

/-! Exact journal erasure and native frames for the joint encryption-history
carrier. These frames transport the projected state, including on empty polls. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

theorem product_checked {g : PrefixM Journal.Event α}
    (history : ∀ past, Driver.ProductHistorySafe (Quiet.Stable past) g)
    (native : ∀ past w h result v, Native past active w.wg →
      (runPrefix g w h).1 = .ok (result,v) → Native past active v.wg) :
    PrefixPreserves (Inv active) Safe g := by
  intro w h before
  obtain ⟨suffix,extension,same,_⟩ := history (used h) w h rfl
  have equal : used (runPrefix g w h).2 = used h := same
  refine ⟨suffix,extension,by simpa only [Safe,equal] using safe before,?_⟩
  cases result : (runPrefix g w h).1 with
  | error stop => trivial
  | ok out => simpa only [Inv,StateInv,equal] using native (used h) w h out.1 out.2 before result

theorem native_join {action : WG.M α}
    (pastFrame : Preserves (EncryptionPast.Ready past active) action)
    (physical : Preserves (OccurrenceStack.Ready [] active) action) :
    Preserves (Native past active) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp pastFrame w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp physical w a result v b before.2 run⟩

theorem state_checked {g : WGPrefix Journal.Event α}
    (history : ∀ past, Driver.StateHistorySafe (Quiet.Stable past) g)
    (native : ∀ past w a h result v b, Native past active w →
      (runWGPrefix g w a h).1 = .ok ((result,v),b) → Native past active v) :
    StatePrefixPreserves (fun h w _ => StateInv active h w) Safe g := by
  intro w a h before
  obtain ⟨suffix,extension,same,_⟩ := history (used h) w a h rfl
  have equal : used (runPrefix (g.run w) a h).2 = used h := same
  refine ⟨suffix,extension,by simpa only [Safe,equal] using state_safe before,?_⟩
  cases result : (runPrefix (g.run w) a h).1 with
  | error stop => trivial
  | ok out =>
    have after := native (used h) w a h out.1.1 out.1.2 out.2 before result
    simpa only [StateInv,equal] using after

theorem product_join {action : Leanux.M α}
    (pastFrame : Preserves (fun w : World => EncryptionPast.Ready past active w.wg) action)
    (physical : Preserves (fun w : World => OccurrenceStack.Ready [] active w.wg) action) :
    Preserves (fun w : World => Native past active w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact ⟨(hoare_iff_run _ _ _).mp pastFrame w result v before.1 run,
    (hoare_iff_run _ _ _).mp physical w result v before.2 run⟩

theorem projected_erases {E F α : Type} {ρ : E → Option F}
    {g : PrefixM E α} {reference : PrefixM F α} {action : Leanux.M α}
    (projects : ProjectsPrefix ρ id g reference) (erases : ErasesPrefix reference action) :
    ErasesPrefix g action := by
  intro w h
  have projected := congrArg Prod.fst (projects w h)
  have result := projected.symm.trans (erases w (h.filterMap ρ))
  cases outcome : (runPrefix g w h).1 <;> simpa only [outcome,Except.map,id_eq] using result

theorem native_product_store {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World => Native past active w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  have frame := (ProjectedAction.iff_run _ _ _).mp same w result v run
  exact ⟨EncryptionPast.product_transport frame before.1,
    OccurrenceStack.ready_store (congrArg (fun s : ProductStore43 => s.2.2.2) frame) before.2⟩

theorem softirq : PrefixPreserves (Inv active) Safe (Driver.softirqObserved Journal.hooks) := by
  apply product_quiet (fun _ => Quiet.softirq_history)
  · have projected := Driver.softirq_projects Journal.hooks_projects
    rw [Driver.nonce_softirqObserved_eq] at projected
    exact projected_erases projected Nonce.softirqObserved_erases
  · intro past
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    exact ⟨(hoare_iff_run _ _ _).mp EncryptionPast.Napi.softirq w result v before.1 run,
      (hoare_iff_run _ _ _).mp (OccurrenceNapi.softirq [] active) w result v before.2 run⟩

end Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
