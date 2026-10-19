import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkServicePointFrames

/-! Fixed-ledger facts for service metadata mutations and the queue receipt.
The counted repayment is deliberately excluded from these passive frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity CausalJournal

theorem native_accounted (action : WG.M α) (frame : SameView StagedEntry.view action)
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg)
    (performed : runPrefix (wg action) w h = (.ok (value,v),last)) :
    CompleteCarrier.Accounted last ledger debts locals v.wg := by
  rw [Wheel.Points.native_run] at performed
  cases actual : ((action.run w.wg).run w.ambient) with
  | error reason => simp only [actual] at performed; cases performed
  | ok output =>
    obtain ⟨⟨x,u⟩,ambient⟩ := output
    simp only [actual,Prod.mk.injEq,Except.ok.injEq] at performed
    rcases performed with ⟨⟨rfl,rfl⟩,rfl⟩
    exact before.same_view ((ProjectedAction.iff_run_ambient _ _ _).mp frame w.wg w.ambient x u ambient actual)

theorem Native.accounted (token : Native) {value : token.Result}
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg)
    (performed : runPrefix token.action w h = (.ok (value,v),last)) :
    CompleteCarrier.Accounted last ledger debts locals v.wg := by
  cases token with
  | ambient body =>
    change ((Leanux.liftAmbient body).run w,h) = (.ok (value,v),last) at performed
    have actual := (Prod.mk.inj performed).1
    have lastEq := (Prod.mk.inj performed).2
    subst last
    have same : v.wg = w.wg := (ProjectedAction.iff_run _ _ _).mp
      (show SameView World.wg (Leanux.liftAmbient body) from fun initial =>
        productAmbient_spec body _ (fun _ _ hi => hi)) w value v actual
    simpa only [same] using before
  | change f same =>
    apply native_accounted _ _ before performed
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a value v b run
    cases run
    exact same w
  | acquire pid => exact native_accounted _ (Queued.acquire pid) before performed
  | expired site birth limit test =>
    exact native_accounted _ ((branchExpired_sameWGWorld site birth limit test).factor StagedEntry.view) before performed
  | queued receipt =>
    change ((Except.ok ((),w) : Except Stop (Unit × World)),h ++ [.queued receipt]) = (.ok (value,v),last) at performed
    rcases Prod.mk.inj performed with ⟨same,rfl⟩
    cases same
    exact before.append_quiet _ (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)
      (by intro event member; simp only [List.mem_singleton] at member; subst event; exact fun _ => rfl)

theorem metadata_accounted (pid : PeerId) (f : Peer → Peer)
    (fields : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged ∧ (f p).txQueue = p.txQueue)
    (before : CompleteCarrier.Accounted h ledger debts locals w.wg)
    (performed : runPrefix (wg (do setPeer pid (f (← getPeer pid)))) w h = (.ok ((),v),last)) :
    CompleteCarrier.Accounted last ledger debts locals v.wg :=
  native_accounted _ (Queued.update pid f fields) before performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.WorkService.Points
