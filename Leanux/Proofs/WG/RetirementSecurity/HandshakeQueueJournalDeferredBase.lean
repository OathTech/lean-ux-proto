import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueJournalWorkers
import Leanux.Proofs.WG.Queues.SendEnvironment
import Leanux.Proofs.WG.Queues.EnvClearDispatch

/-! Recorded work selection and timer scope markers retain the actual
handshake queue; histories remain those of the shared source execution. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits TransmitSecurity
variable {E : Type} {Valid : List UInt8 → Prop} {Safe : List E → Prop}
  {hooks : Driver.Hooks E} {ρ : E → Option TransmitSecurity.Journal.Event}

theorem stable (h : List E) (w v : World) (same : productStoreView v=productStoreView w)
    (before : ProductInv Valid Safe h w) : ProductInv Valid Safe h v := by
  refine ⟨transport ?_ before.1,before.2⟩
  exact congrArg (fun s : ProductStore43=>s.2.2.2.dev.map fun d=>d.handshakeQueue) same

theorem product_store (action : Leanux.M α) (same : SameProductStore action) :
    ProductSafe Valid Safe (liftPrefix action) :=
  viewLiftPrefix_preserves productStoreView (fun _ _ before=>before.2) stable same

theorem send_one_cell : SameView HandshakeLengths.productView Env.runOneSendWorker := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩:=SendEnvironment.runOneSendWorker_selected w v run
  exact (ProjectedAction.iff_run_ambient _ _ _).mp (flushed_send_cell pid)
    w.wg beforeWorker () v.wg v.ambient worker

theorem clear_one_cell : SameView HandshakeLengths.productView Env.runOneClearWorker := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases result
  obtain ⟨_,_,_,_,pid,beforeWorker,_,_,_,_,_,worker⟩:=ClearWork.runOneClearWorker_selected w v run
  exact (ProjectedAction.iff_run_ambient _ _ _).mp (flushed_clear_cell pid)
    w.wg beforeWorker () v.wg v.ambient worker

theorem send_one (c : Contracts Valid Safe hooks ρ) :
    ProductSafe Valid Safe (Driver.sendWorkerObserved hooks) := by
  have projected:=Projection.product (Driver.sendWorker_projects c.projects) (Driver.sendWorker_projects TransmitSecurity.Journal.hooks_projects)
  rw [Driver.sendWorker_lift Driver.nonceHooks rfl] at projected
  exact product_native c.quiet.sendWorker projected (erasesPrefix_lift _) (product_frame send_one_cell)

theorem clear_one : ProductSafe Valid Safe (liftPrefix Env.runOneClearWorker) :=
  product_lift Valid Safe _ (product_frame clear_one_cell)

theorem deliver (c : Contracts Valid Safe hooks ρ) : ProductSafe Valid Safe hooks.deliver :=
  product_native c.quiet.deliver c.projects.deliver (erasesPrefix_lift _)
    (product_frame (deliverSent_sameKernel.of_factor
      (fun s : ProductStore43=>s.2.2.2.dev.map fun d=>d.handshakeQueue)
      HandshakeLengths.productView (fun _=>rfl)))

theorem product_neutral {F : Type} {ρ : E→Option F} {g : PrefixM E α} {f : α → β} {value : β}
    (history : Driver.ProductHistorySafe Safe g)
    (projects : ProjectsPrefix ρ f g (pure value)) : ProductSafe Valid Safe g := by
  apply checked_product history
  intro w h result v before run
  have same:=congrArg Prod.fst (projects w h)
  simp only [runPrefix_pure,run,Except.map,Except.ok.injEq,Prod.mk.injEq] at same
  exact same.2 ▸ before

theorem timer_selected (c : Contracts Valid Safe hooks ρ)
    (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (we : WheelEntry) :
    ProductSafe Valid Safe (hooks.timerSelected d j pid t we) := by
  obtain ⟨scopeMap,selected,_⟩:=c.projects.timer
  obtain ⟨nextMap,nextSelected,_⟩:=TransmitSecurity.Journal.hooks_projects.timer
  exact product_neutral (c.quiet.timerSelected d j pid t we)
    (Projection.product (selected d j pid t we) (nextSelected d j pid t we))

theorem timer_finished (c : Contracts Valid Safe hooks ρ) (token : Nat) :
    ProductSafe Valid Safe (hooks.timerFinished token) := by
  obtain ⟨scopeMap,_,finished⟩:=c.projects.timer
  exact product_neutral (c.quiet.timerFinished token) (finished token)

theorem wg_read : ProductSafe Valid Safe (liftPrefix getWG) :=
  product_store _ (fun initial=>productGetWG_spec (·=initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀w,wgStoreView (f w)=wgStoreView w) :
    ProductSafe Valid Safe (liftPrefix (modifyWG f)) :=
  product_store _ (fun initial=>productModifyWG_spec (·=initial) f same)

theorem env_read : ProductSafe Valid Safe (liftPrefix getEnv) := by
  apply product_lift
  apply (hoare_iff_run _ _ _).mpr
  intro w x v before run
  cases run
  exact before

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Journal
