import Leanux.Proofs.WG.Origins.CurrentChecks

/-! Current identity at the actual decrypt/probe prefixes of the existing
persistent journal. The native decrypt normal-state obligation remains explicit
until its concrete source preservation contract is supplied. -/
namespace Leanux.Proofs.WG.CurrentChecks
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
open Origins.HistorySupport (sessions sessionEvent lifeEncode)

/-- This check concerns the captured entry and strict earlier session history;
it is retained even if the observed decrypt or a later action Stops. -/
theorem decrypt_checks (id : SkbId) (w : World) (h : List RxHistory.Event)
    (current : CurrentSessionPrefix.StateInv h w) (checks : Checks h) :
    Checks (runPrefix (Origins.HistoryAdapters.decrypt id) w h).2 := by
  rw [Origins.HistorySupport.decrypt_run]
  cases run : runWGPrefix (RxOrigin.readDecryptPrefix id) w.wg w.ambient (RxHistory.prior h) with
  | mk result history =>
    have quiet : Checks (h ++ (history.drop (RxHistory.prior h).length).map lifeEncode) :=
      checks.quiet (filterMap_disjoint _ _ (fun _ => rfl) _)
    cases result with
    | error e => exact quiet
    | ok out =>
      apply quiet.snoc
      change CurrentLifecycle.Inv (sessions (h ++ _)) w.wg
      rw [Origins.HistorySupport.life_sessions]
      exact current

theorem decrypt_sessions (id : SkbId) (w : World) (h : List RxHistory.Event) :
    sessions (runPrefix (Origins.HistoryAdapters.decrypt id) w h).2 = sessions h := by
  rw [Origins.HistorySupport.decrypt_run]
  cases run : runWGPrefix (RxOrigin.readDecryptPrefix id) w.wg w.ambient (RxHistory.prior h) with
  | mk result history =>
    cases result <;>
      simp only [sessions,List.filterMap_append,List.filterMap_cons,List.filterMap_nil,
        sessionEvent,List.append_nil]
    all_goals
      rw [filterMap_disjoint lifeEncode sessionEvent (fun _ => rfl)]
      exact List.append_nil _

theorem decrypt (id : SkbId)
    (native : ∀ history, Framing.Preserves (CurrentLifecycle.Inv history) (RxOrigin.readDecrypt id)) :
    Preserves (Origins.HistoryAdapters.decrypt id) := by
  apply combine _ (Origins.HistorySupport.decrypt id)
  · exact CurrentHistory.erased _ _ (Appends.focus _ _ _)
      (Origins.HistoryAdapters.decrypt_erases id) (decrypt_sessions id)
      (CurrentHistory.native_product _ native)
  · intro w h hi
    exact decrypt_checks id w h hi.2.1 hi.2.2

theorem filter_run (w : World) (h : List RxHistory.Event) :
    runPrefix (RxHistory.audit consistentFilterAudit) w h =
      ((w.ambient.suspended.filterM Env.Activation.consistent).run w,
        h ++ [.audit (.probe ⟨w,RxHistory.prior h⟩)]) := by
  change ((runPrefix consistentFilterAudit w (h.filterMap RxHistory.auditEvent)).1,
    h ++ ((runPrefix consistentFilterAudit w (h.filterMap RxHistory.auditEvent)).2.drop
      (h.filterMap RxHistory.auditEvent).length).map RxHistory.Event.audit) = _
  rw [consistentFilterAudit_run]
  simp only [List.drop_left,List.map_cons,List.map_nil]
  rfl

/-- The probe captures the real product World before the filter's copied
consistency trials; their normal return preserves its WG device view. -/
theorem filter_probe : Preserves (RxHistory.audit consistentFilterAudit) := by
  intro w h hi
  have checked := hi.2.2.snoc (e := .audit (.probe ⟨w,RxHistory.prior h⟩)) hi.2.1
  obtain ⟨suffix,hs,safe,post⟩ := Origins.HistorySupport.filter_probe w h hi.1
  simp only [filter_run] at hs safe post ⊢
  refine ⟨[.audit (.probe ⟨w,RxHistory.prior h⟩)],rfl,⟨safe,checked⟩,?_⟩
  cases hr : (w.ambient.suspended.filterM Env.Activation.consistent).run w with
  | error e => trivial
  | ok out =>
    rw [hr] at post
    refine ⟨post,?_,checked⟩
    have frame := (ProjectedAction.iff_run _ _ _).mp
      (filterM_sameKernel productStoreView _ activationConsistent_sameKernel _)
      w out.1 out.2 hr
    have dev : out.2.wg.dev = w.wg.dev :=
      congrArg (fun s : ProductStore43 => s.2.2.2.dev) frame
    have cfg : ConfiguredIdentity.Inv out.2.wg := by
      intro state hs
      exact hi.2.1.1 state (by simpa only [ConfiguredIdentity.view,dev] using hs)
    have current : CurrentIdentity.Inv (sessions h) out.2.wg :=
      fun d hd id key hk valid => hi.2.1.2 d (dev.symm.trans hd) id key hk valid
    simpa only [CurrentSessionPrefix.StateInv,sessions,List.filterMap_append,
      List.filterMap_cons,List.filterMap_nil,sessionEvent,List.append_nil]
      using And.intro cfg current

end Leanux.Proofs.WG.CurrentChecks

