import Leanux.Proofs.WG.RetirementSecurity.KeySlotDataCompletion
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceStack

/-! Native transmit and IP-stack callback transport for published-slot liveness.
The callback is the actual fixture stack, including its outgoing reply path. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open Queues.RxCredits StackOwnership

theorem lookup_destination (family addr : Nat) :
    Preserves (InvExcept pending) (lookupDst family addr) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none=>exact device before (congrArg WGStoreView.dev borrowed)
  | some pid=>
    obtain ⟨d,p,hd,hp,_,out⟩ := borrowed
    exact device (replace before hd hp (q:={p with refcount:=p.refcount+1}) (fun h=>h) (fun h=>h))
      (congrArg WGStoreView.dev out)

theorem xmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (InvExcept pending) (wgXmit family addr packets mtu) := by
  have routing {α : Type} (action : Net.M α) : Preserves (InvExcept pending) (monadLift action : WG.M α) :=
    store (liftRouting_sameWGStore action)
  unfold wgXmit WG.andM
  simp (config := {zeta:=false}) only [branch,invariant,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (rx_retention_head lookupDst; exact lookup_destination _ _)
    | (rx_retention_head sendStagedPackets; exact staged _)
    | (rx_retention_head loopbackSend; exact store (loopbackSend_kernel _ _))
    | (rx_retention_head skipCutSites; unfold skipCutSites)
    | (rx_retention_head envOk; unfold envOk)
    | (allocation_release_lift_from Net.M; exact routing _)
    | key_slot_rx_step

theorem store_transport (same : wgStoreView v=wgStoreView w) (before : InvExcept pending w) :
    InvExcept pending v := device before (congrArg WGStoreView.dev same)

theorem kernel_stable : KernelStable (fun w : World=>InvExcept pending w.wg) := by
  intro w v same before
  exact store_transport (congrArg (fun s : ProductStore43=>s.2.2.2) same) before

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (fun w : World=>InvExcept pending w.wg) (liftWG (wgXmit family addr packets mtu)) :=
  PublicationPoll.native_product _ _ (xmit family addr packets mtu)

theorem reply4_stack (dst : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜InvExcept pending w.wg⌝⦄ Leanux.Env.Stack.reply4 dst bytes
    ⦃⇓? _ w => ⌜InvExcept pending w.wg⌝⦄ := by
  let P := fun w : World => InvExcept pending w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α) :=
    kernel_predicate kernel_stable
      (liftWG_sameProductStore _ (liftRouting_sameWGStore a))
  have device : Preserves P (liftWG getDev) :=
    kernel_predicate kernel_stable (liftWG_sameProductStore _ getDev_sameWGStore)
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
    ⦃fun w => ⌜InvExcept pending w.wg⌝⦄ Leanux.Env.Stack.receive4 bytes
    ⦃⇓? _ w => ⌜InvExcept pending w.wg⌝⦄ := by
  let P := fun w : World => InvExcept pending w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have routing {α : Type} (a : Net.M α) :
      Preserves P (MonadLift.monadLift (MonadLift.monadLift a : WG.M α) : Leanux.M α) :=
    kernel_predicate kernel_stable
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
    ⦃fun w => ⌜InvExcept pending w.wg⌝⦄ Leanux.Env.Stack.receive bytes
    ⦃⇓? _ w => ⌜InvExcept pending w.wg⌝⦄ := by
  let P := fun w : World => InvExcept pending w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (MonadLift.monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  change Hoare _ P (fun _ => P)
  unfold Leanux.Env.Stack.receive
  material_lower
  repeat' first
    | (index_material_head Leanux.Env.Stack.receive4; exact receive4_stack _)
    | (index_material_head Leanux.Env.Stack.receive6
       exact kernel_predicate kernel_stable (stackReceive6_sameKernel _))
    | (rx_stack_lift_head; exact ambient _)
    | rx_stack_basic P

theorem deliverInner_stack (bytes : List UInt8) :
    ⦃fun w => ⌜InvExcept pending w.wg⌝⦄ Leanux.Env.deliverInner bytes
    ⦃⇓? _ w => ⌜InvExcept pending w.wg⌝⦄ := by
  change Hoare _ (fun w : World => InvExcept pending w.wg) (fun _ w => InvExcept pending w.wg)
  unfold Leanux.Env.deliverInner
  exact stackReceive_stack bytes

theorem stackForM_stack (packets : List (List UInt8)) :
    ⦃fun w => ⌜InvExcept pending w.wg⌝⦄ packets.forM Leanux.Env.deliverInner
    ⦃⇓? _ w => ⌜InvExcept pending w.wg⌝⦄ := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes xs ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_stack bytes) (fun _ => ih)


end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
