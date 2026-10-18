import Leanux.Proofs.WG.RetirementSecurity.ReceiveOccurrences

/-! The actual IP-stack callback preserves physical TX ownership without
assuming key-holder alignment. Allocation freshness is transported by the
independent campaign-1 invariant at each original transmit call. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceStack
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open StackOwnership Queues.RxCredits

def Ready (locals : List TxLocalBatch) (active : List (List SkbId)) (w : WGWorld) : Prop :=
  Allocated w ∧ TxOccurrences locals active w

theorem ready_store (same : wgStoreView v = wgStoreView w)
    (before : Ready locals active w) : Ready locals active v := by
  have dev : v.dev = w.dev := congrArg WGStoreView.dev same
  have wire : txCryptWire v = txCryptWire w := by
    simp only [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,dev]
  have queues : handoffTxView v = handoffTxView w := by funext pid; simp only [handoffTxView,dev]
  exact ⟨before.1.store same,before.2.1.wire_queues wire queues,
    before.2.2.frame_packets (congrArg Prod.fst wire)
      (fun _ owned => owned.queues queues) (congrArg Prod.snd wire)⟩

theorem ready_kernel : KernelStable (fun w : World => Ready locals active w.wg) := by
  intro w v same before
  exact ready_store (congrArg (fun s : ProductStore43 => s.2.2.2) same) before

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (fun w : World => Ready locals active w.wg) (liftWG (wgXmit family addr packets mtu)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  rw [liftWG_run] at run
  cases native : ((wgXmit family addr packets mtu).run w.wg).run w.ambient with
  | error e => simp [native,Except.map] at run
  | ok output =>
    obtain ⟨⟨ret,g⟩,a⟩ := output
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨before.1.transmit family addr packets mtu w.ambient a native,
      TransmitOccurrences.transmit ⟨before.1.bounded,before.2⟩ family addr packets mtu w.ambient a native⟩

theorem reply4_stack (dst : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜Ready locals active w.wg⌝⦄ Leanux.Env.Stack.reply4 dst bytes
    ⦃⇓? _ w => ⌜Ready locals active w.wg⌝⦄ := by
  let P := fun w : World => Ready locals active w.wg
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
    | (rx_stack_lift_source wgXmit; exact transmit _ _ _ _)
    | (rx_stack_lift_source getDev; exact device)
    | (first | rx_stack_lift_source Net.routeOutput4 | rx_stack_lift_source Net.neighbourClassify
       exact routing _)
    | (rx_stack_lift_head; exact ambient _)
    | rx_stack_basic P

theorem receive4_stack (bytes : List UInt8) :
    ⦃fun w => ⌜Ready locals active w.wg⌝⦄ Leanux.Env.Stack.receive4 bytes
    ⦃⇓? _ w => ⌜Ready locals active w.wg⌝⦄ := by
  let P := fun w : World => Ready locals active w.wg
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
    ⦃fun w => ⌜Ready locals active w.wg⌝⦄ Leanux.Env.Stack.receive bytes
    ⦃⇓? _ w => ⌜Ready locals active w.wg⌝⦄ := by
  let P := fun w : World => Ready locals active w.wg
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
    ⦃fun w => ⌜Ready locals active w.wg⌝⦄ Leanux.Env.deliverInner bytes
    ⦃⇓? _ w => ⌜Ready locals active w.wg⌝⦄ := by
  change Hoare _ (fun w : World => Ready locals active w.wg) (fun _ w => Ready locals active w.wg)
  unfold Leanux.Env.deliverInner
  exact stackReceive_stack bytes

theorem stackForM_stack (packets : List (List UInt8)) :
    ⦃fun w => ⌜Ready locals active w.wg⌝⦄ packets.forM Leanux.Env.deliverInner
    ⦃⇓? _ w => ⌜Ready locals active w.wg⌝⦄ := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes xs ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_stack bytes) (fun _ => ih)


end Leanux.Proofs.WG.RetirementSecurity.OccurrenceStack
