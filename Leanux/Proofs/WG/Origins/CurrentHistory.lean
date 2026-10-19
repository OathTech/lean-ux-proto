import Leanux.Proofs.WG.Origins.CurrentSessionPrefix

/-! Composition rules for current configured identity on the existing RX
journal. A lifetime-only observer changes no session receipts; its normal
native or product action supplies state preservation. The rules preserve the
actual reached prefix on Stop and require no validity of incoming receipts. -/
namespace Leanux.Proofs.WG.CurrentHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues
open Origins.HistorySupport (sessions)
abbrev StateInv := CurrentSessionPrefix.StateInv
abbrev Preserves (g : RxHistory.Obs α) := PrefixPreserves StateInv (fun _ => True) g

theorem erased (g : RxHistory.Obs α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (sameSessions : ∀ w h, sessions (runPrefix g w h).2 = sessions h)
    (state : ∀ history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg) a) : Preserves g := by
  intro w h hi
  obtain ⟨s,hs⟩ := appends w h
  refine ⟨s,hs,True.intro,?_⟩
  cases hr : (runPrefix g w h).1 with
  | error e => trivial
  | ok out =>
    change CurrentLifecycle.Inv (sessions (runPrefix g w h).2) out.2.wg
    rw [sameSessions]
    exact (hoare_iff_run _ _ _).mp (state (sessions h)) w out.1 out.2 hi
      ((erases w h).symm.trans hr)

theorem lift (a : Leanux.M α)
    (state : ∀ history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg) a) : Preserves (liftPrefix a) :=
  erased _ a (Appends.lift a) (erasesPrefix_lift a) (fun _ _ => rfl) state

/-- The concrete two-stage focus keeps incoming probes, receipts, and session
events. Only its actual lifetime suffix is added. -/
theorem mixed (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (erases : ErasesPrefix g a)
    (state : ∀ history, Framing.Preserves
      (fun w : World => CurrentLifecycle.Inv history w.wg) a) :
    Preserves (RxHistory.mixed g) := by
  apply erased _ a (Appends.focus _ _ _) (focusPrefix_erases _ _
    (focusPrefix_erases _ _ erases)) _ state
  intro w h
  unfold sessions
  rw [Origins.HistorySupport.focus_compose]
  exact focusPrefix_other _ _ Origins.HistorySupport.sessionEvent (fun _ => rfl) _ w h

theorem native_product (a : WG.M α)
    (state : ∀ history, Framing.Preserves (CurrentLifecycle.Inv history) a)
    (history : List SessionOrigin.Receipt) :
    Framing.Preserves (fun w : World => CurrentLifecycle.Inv history w.wg) (liftWG a) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi hr
  rw [liftWG_run] at hr
  cases native : (a.run w.wg).run w.ambient with
  | error e => simp [native,Except.map] at hr
  | ok out =>
    rcases out with ⟨⟨value,g⟩,ambient⟩
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at hr
    obtain ⟨rfl,rfl⟩ := hr
    exact (hoare_iff_run_ambient _ _ _).mp (state history)
      w.wg w.ambient value g ambient hi native

theorem native_mixed (g : WGPrefix LifetimeEvent α) (a : WG.M α)
    (erases : ErasesStatePrefix g a)
    (state : ∀ history, Framing.Preserves (CurrentLifecycle.Inv history) a) :
    Preserves (RxHistory.mixed (liftWGObserver g)) :=
  mixed _ _ (liftWGObserver_erases erases) (native_product a state)

end Leanux.Proofs.WG.CurrentHistory

