import Leanux.Proofs.WG.RetirementSecurity.DriverOwnership
import Leanux.Proofs.WG.Lifetimes.AllocationInitial
import Leanux.Proofs.WG.TransmitSecurity.DriverReceiveProjection

/-! Native Stack callbacks transport concrete ownership alongside campaign
1's independently proved allocation invariant. Its history is existential:
only native endpoint facts are used, never event chronology. -/
namespace Leanux.Proofs.WG.RetirementSecurity.StackOwnership
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open Queues.RxCredits

def Allocated (w : WGWorld) : Prop := ∃ history, AllocationInv history w

theorem Allocated.bounded (before : Allocated w) : Packets.Inv w := by
  obtain ⟨history,account⟩ := before
  cases device : w.dev with
  | none => simp [Packets.Inv,Packets.snapshot,device,Bounded]
  | some d => simpa only [Packets.Inv,Packets.snapshot,device] using account.packetBounded d device

theorem Allocated.store (before : Allocated w) (same : wgStoreView v = wgStoreView w) : Allocated v :=
  ⟨before.choose,before.choose_spec.store same⟩

theorem Allocated.transmit (before : Allocated w) (family addr : Nat)
    (packets : List WG.Packet) (mtu : Nat) (a b : Ambient)
    (run : ((wgXmit family addr packets mtu).run w).run a = .ok ((result,v),b)) : Allocated v := by
  obtain ⟨history,account⟩ := before
  have checked := wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit
    family addr packets mtu w a history account
  obtain ⟨_,_,_,post⟩ := checked
  have observed := (wgXmitPrefix_erases family addr packets mtu) w a history
  rw [run] at observed
  rw [observed] at post
  exact ⟨_,post⟩

def Ready (temporary : Credits.Ledger) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (w : WGWorld) : Prop :=
  DriverOwnership.Boundary temporary locals active w ∧ Allocated w ∧ CurrentsCompatible w

theorem initial (net bare : Bool) : Ready [] [] [] (Runner.initialWG net bare) := by
  refine ⟨DriverOwnership.initial net bare,⟨[],allocation_initial net bare _ rfl⟩,?_⟩
  intro pid d p kid device resident
  by_cases enabled : (net && !bare) = true
  · simp only [Runner.initialWG,enabled,ite_true,Option.some.injEq] at device
    subst d
    simp at resident
  · simp only [Runner.initialWG,enabled,ite_false,reduceCtorEq] at device

theorem ready_store (same : wgStoreView v = wgStoreView w)
    (before : Ready temporary locals active w) : Ready temporary locals active v := by
  have dev : v.dev = w.dev := congrArg WGStoreView.dev same
  have own : ownershipPointView v = ownershipPointView w := by
    unfold ownershipPointView ownershipAt peerAt keyReferenceView keyAt packetKeyWords
    rw [dev]
  have wire : txCryptWire v = txCryptWire w := by
    simp only [txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,dev]
  have queues : handoffTxView v = handoffTxView w := by funext pid; simp only [handoffTxView,dev]
  exact ⟨⟨before.1.1.points own,before.1.2.1.wire_queues wire queues,
    before.1.2.2.frame_packets (congrArg Prod.fst wire)
      (fun _ owned => owned.queues queues) (congrArg Prod.snd wire)⟩,
    before.2.1.store same,by simpa only [CurrentsCompatible,CurrentCompatible,KeyCompatible,dev] using before.2.2⟩

theorem ready_kernel : KernelStable (fun w : World => Ready temporary locals active w.wg) := by
  intro w v same before
  exact ready_store (congrArg (fun s : ProductStore43 => s.2.2.2) same) before

theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (fun w : World => Ready temporary locals active w.wg) (liftWG (wgXmit family addr packets mtu)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  rw [liftWG_run] at run
  cases native : ((wgXmit family addr packets mtu).run w.wg).run w.ambient with
  | error e => simp [native,Except.map] at run
  | ok output =>
    obtain ⟨⟨ret,g⟩,a⟩ := output
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨⟨before.1.1.transmit before.2.1.bounded before.2.2 family addr packets mtu w.ambient a native,
      TransmitOccurrences.transmit ⟨before.2.1.bounded,before.1.2⟩ family addr packets mtu w.ambient a native⟩,
      before.2.1.transmit family addr packets mtu w.ambient a native,
      (wgXmit_closed family addr packets mtu before.2.2 native).2⟩

theorem reply4_stack (dst : Nat) (bytes : List UInt8) :
    ⦃fun w => ⌜Ready temporary locals active w.wg⌝⦄ Leanux.Env.Stack.reply4 dst bytes
    ⦃⇓? _ w => ⌜Ready temporary locals active w.wg⌝⦄ := by
  let P := fun w : World => Ready temporary locals active w.wg
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
    ⦃fun w => ⌜Ready temporary locals active w.wg⌝⦄ Leanux.Env.Stack.receive4 bytes
    ⦃⇓? _ w => ⌜Ready temporary locals active w.wg⌝⦄ := by
  let P := fun w : World => Ready temporary locals active w.wg
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
    ⦃fun w => ⌜Ready temporary locals active w.wg⌝⦄ Leanux.Env.Stack.receive bytes
    ⦃⇓? _ w => ⌜Ready temporary locals active w.wg⌝⦄ := by
  let P := fun w : World => Ready temporary locals active w.wg
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
    ⦃fun w => ⌜Ready temporary locals active w.wg⌝⦄ Leanux.Env.deliverInner bytes
    ⦃⇓? _ w => ⌜Ready temporary locals active w.wg⌝⦄ := by
  change Hoare _ (fun w : World => Ready temporary locals active w.wg) (fun _ w => Ready temporary locals active w.wg)
  unfold Leanux.Env.deliverInner
  exact stackReceive_stack bytes

theorem stackForM_stack (packets : List (List UInt8)) :
    ⦃fun w => ⌜Ready temporary locals active w.wg⌝⦄ packets.forM Leanux.Env.deliverInner
    ⦃⇓? _ w => ⌜Ready temporary locals active w.wg⌝⦄ := by
  induction packets with
  | nil => exact preserves_pure _
  | cons bytes xs ih =>
    simp only [List.forM_eq_forM,List.forM_cons]
    exact preserves_bind (deliverInner_stack bytes) (fun _ => ih)


theorem shared_stack {E : Type}
    {ρ : E → Option TransmitSecurity.Nonce.Allocation}
    {hooks : TransmitSecurity.Driver.Hooks E}
    (projects : TransmitSecurity.Driver.HooksProjects ρ hooks TransmitSecurity.Driver.nonceHooks)
    (before : Ready temporary locals active w.wg) (bytes : List UInt8) (h : List E)
    (run : (runPrefix (TransmitSecurity.Driver.stackObserved hooks bytes) w h).1 = .ok (result,v)) :
    Ready temporary locals active v.wg := by
  have projected := TransmitSecurity.Driver.stack_projects projects bytes
  rw [TransmitSecurity.Driver.nonce_stackObserved_eq] at projected
  exact (hoare_iff_run _ _ _).mp (deliverInner_stack bytes) w result v before
    (DriverOwnership.product_native projected (TransmitSecurity.Nonce.stackObserved_erases bytes) w v h run)

end Leanux.Proofs.WG.RetirementSecurity.StackOwnership
