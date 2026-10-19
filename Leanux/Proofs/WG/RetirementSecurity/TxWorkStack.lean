import Leanux.Proofs.WG.RetirementSecurity.TxWorkTransmit

/-! Native IP-stack replies retain the joint TX coverage/service carrier.
The actual routed transmit call may allocate; every other source cut preserves
its relevant WG store. No actor-suspension frame is inferred from this fact. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open StackOwnership Queues.RxCredits

theorem serving_store_transport (same : wgStoreView v=wgStoreView w)
    (before : Serving locals crypt tx w) : Serving locals crypt tx v := by
  have dev:v.dev=w.dev := congrArg WGStoreView.dev same
  refine ⟨before.1.frame ?_ ?_ ?_ ?_,TxCovered.ready_store same before.2⟩
  · funext pid; simp only [handoffTxView,dev]
  · funext id; simp only [TxDisposition.txPackets,dev]
  · simp only [txCryptItems,dev]
  · simp only [queued,dev]

theorem ready_kernel : KernelStable (fun w : World => Serving locals crypt tx w.wg) := by
  intro w v same before
  exact serving_store_transport (congrArg (fun s : ProductStore43 => s.2.2.2) same) before

theorem reply4_stack (dst : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜Serving locals crypt tx w.wg⌝⦄ Leanux.Env.Stack.reply4 dst bytes
    ⦃⇓? _ w => ⌜Serving locals crypt tx w.wg⌝⦄ := by
  let P := fun w : World => Serving locals crypt tx w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α) :=
    kernel_predicate ready_kernel
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have device : Preserves P (liftWG getDev) :=
    kernel_predicate ready_kernel (liftWG_sameProductStore _ getDev_sameWGStore)
  change Hoare _ P (fun _ => P)
  unfold Leanux.Env.Stack.reply4 skipCut
  material_lower
  repeat' first
    | (rx_stack_lift_source wgXmit; exact serving_transmit _ _ _ _)
    | (rx_stack_lift_source getDev; exact device)
    | (first | rx_stack_lift_source Net.routeOutput4 | rx_stack_lift_source Net.neighbourClassify
       exact routing _)
    | (rx_stack_lift_head; exact ambient _)
    | rx_stack_basic P

theorem receive4_stack (bytes : List UInt8) :
    ⦃fun w => ⌜Serving locals crypt tx w.wg⌝⦄ Leanux.Env.Stack.receive4 bytes
    ⦃⇓? _ w => ⌜Serving locals crypt tx w.wg⌝⦄ := by
  let P := fun w : World => Serving locals crypt tx w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α) :=
    kernel_predicate ready_kernel
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have read : Preserves P (getWG : Leanux.M WGWorld) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  have write (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi hr
    cases hr
    exact hi
  change Hoare _ P (fun _ => P)
  unfold Leanux.Env.Stack.receive4 Leanux.Env.Stack.excluded
  material_lower
  repeat' first
    | (index_material_head Leanux.Env.Stack.reply4; exact reply4_stack _ _)
    | (index_material_head getWG; exact read)
    | (index_material_head modifyEnv; exact write _)
    | (rx_stack_lift_source Net.routeInput4; exact routing _)
    | (rx_stack_lift_head; exact ambient _)
    | rx_stack_basic P

theorem stackReceive_stack (bytes : List UInt8) :
    ⦃fun w => ⌜Serving locals crypt tx w.wg⌝⦄ Leanux.Env.Stack.receive bytes
    ⦃⇓? _ w => ⌜Serving locals crypt tx w.wg⌝⦄ := by
  let P := fun w : World => Serving locals crypt tx w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  change Hoare _ P (fun _ => P)
  unfold Leanux.Env.Stack.receive
  material_lower
  repeat' first
    | (index_material_head Leanux.Env.Stack.receive4; exact receive4_stack _)
    | (index_material_head Leanux.Env.Stack.receive6
       exact kernel_predicate ready_kernel (stackReceive6_sameKernel _))
    | (rx_stack_lift_head; exact ambient _)
    | rx_stack_basic P

theorem deliverInner_stack (bytes : List UInt8) :
    ⦃fun w => ⌜Serving locals crypt tx w.wg⌝⦄ Leanux.Env.deliverInner bytes
    ⦃⇓? _ w => ⌜Serving locals crypt tx w.wg⌝⦄ := by
  change Hoare _ (fun w : World => Serving locals crypt tx w.wg) (fun _ w => Serving locals crypt tx w.wg)
  unfold Leanux.Env.deliverInner
  exact stackReceive_stack bytes

theorem stackForM_stack (packets : List (List UInt8)) :
    ⦃fun w => ⌜Serving locals crypt tx w.wg⌝⦄ packets.forM Leanux.Env.deliverInner
    ⦃⇓? _ w => ⌜Serving locals crypt tx w.wg⌝⦄ := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes xs ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_stack bytes) (fun _ => ih)


end Leanux.Proofs.WG.RetirementSecurity.TxWork
