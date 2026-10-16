import Leanux.Proofs.WG.Lifetimes.DeviceControls
import Leanux.Proofs.WG.Lifetimes.DeviceCreation

/-! Whole device creation, destruction and deletion. Destruction preserves the
actual peer-removal and socket-access prefixes, including every original Stop,
then records retirement of the actual residual stores at the final device drop.
The drop is logical store accounting, not a proof of per-object kernel frees. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def wgDestructPrefix : MixedM Unit := do
  liftWGPrefix (modifyDev fun d => {d with creatingNet := false, incomingPort := 0})
  liftWGPrefix (socketReinit none none)
  peerRemoveAllPrefix
  let d ← liftWGPrefix getDev
  if !d.sendWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.empty || !d.clearWorkQueue.isEmpty then
    liftWGPrefix (unsupported "wg_destruct with queued work (destroy_workqueue runs it)")
  if !d.handshakeQueue.empty then
    liftWGPrefix (invariant "wg_destruct with handshake messages queued (wg_stop drains the ring)")
  liftWGPrefix mayHaveSlept
  liftWGPrefix (modifyDev fun d => {d with handshakeQueueLen := 0})
  liftWGPrefix mayHaveSlept
  liftWGPrefix ratelimiterUninit
  dropDevicePrefix
  liftWGPrefix retireDeviceUnits

def wgDeletePrefix : MixedM Int := do
  if (← liftWGPrefix (get : WG.M WGWorld)).dev.isNone then return -ENODEV
  if (← liftWGPrefix getDev).running then wgDownPrefix
  liftWGPrefix (skipCut allocCuts)
  liftWGPrefix mayHaveSlept
  wgDestructPrefix
  return 0

theorem wgDestructPrefix_erases : ErasesStatePrefix wgDestructPrefix wgDestruct := by
  unfold wgDestructPrefix wgDestruct
  repeat' first
    | with_reducible exact peerRemoveAllPrefix_erases
    | with_reducible exact dropDevicePrefix_erases
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgDeletePrefix_erases : ErasesStatePrefix wgDeletePrefix wgDelete := by
  unfold wgDeletePrefix wgDelete
  simp only [pure_bind]
  repeat' first
    | exact wgDownPrefix_erases
    | exact wgDestructPrefix_erases
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

structure DeviceLifecycleContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  controls : DeviceControlContracts I
  startDestruct : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev fun d => {d with creatingNet := false, incomingPort := 0}))
  ratelimiter : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix ratelimiterUninit)
  drop : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe dropDevicePrefix
  create : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe wgCreatePrefix

structure ProductDeviceLifecycleContracts (I : List LifetimeEvent → World → Prop) : Prop where
  controls : ProductDeviceControlContracts I
  startDestruct : PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with creatingNet := false, incomingPort := 0})))
  ratelimiter : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix ratelimiterUninit))
  drop : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver dropDevicePrefix)
  create : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver wgCreatePrefix)

theorem allocationDeviceLifecycle : DeviceLifecycleContracts AllocationInv := by
  refine ⟨allocationDeviceControl, ?_, ?_, dropDevicePrefix_allocation, wgCreatePrefix_allocation⟩
  · apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl
  · apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    have he := (ProjectedAction.iff_run_ambient _ _ _).mp
      ratelimiterUninit_sameRatelimiter w ambient x v ambient' hr
    have hl0 := congrArg linkStore he
    have hl : linkView v = linkView w := by
      simpa only [linkView, ratelimiterView, linkStore, ratelimiterStore] using hl0
    have hf := linkView_identity_metadata w v hl
    exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem wgDestructPrefix_preserves (c : AmbientContracts I) (r : DeviceLifecycleContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe wgDestructPrefix := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold wgDestructPrefix
  repeat' first
    | (maintenance_lift_action_head modifyDev; exact r.startDestruct)
    | (maintenance_lift_action_head socketReinit; exact socketControlLift_preserves c r.controls.socket _ ((socketReinit_sameSocket _ _).factor WGOwnedView.toWGStoreView))
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves c r.controls.removal)
    | (maintenance_lift_action_head modifyDev; exact r.controls.clearHandshakeQueue)
    | (maintenance_lift_action_head ratelimiterUninit; exact r.ratelimiter)
    | (maintenance_head dropDevicePrefix; exact r.drop)
    | (maintenance_lift_action_head retireDeviceUnits; exact AmbientContracts.drop (c.store (fun _ => True) _ retireDeviceUnits_sameWGStore))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head mayHaveSlept; exact AmbientContracts.drop (c.store (fun _ => True) _ mayHaveSlept_sameWGStore))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgDeletePrefix_preserves (c : AmbientContracts I) (r : DeviceLifecycleContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe wgDeletePrefix := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P _ (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold wgDeletePrefix
  repeat' first
    | (maintenance_head wgDownPrefix; exact wgDownPrefix_preserves c r.controls)
    | (maintenance_head wgDestructPrefix; exact wgDestructPrefix_preserves c r)
    | (maintenance_lift_action_head skipCut; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.skipCut _)))
    | (maintenance_lift_action_head get; exact AmbientContracts.drop (c.store (fun _ => True) (get : WG.M WGWorld) (by apply (ProjectedAction.iff_run_ambient _ _ _).mpr; intro w ambient x v ambient' hr; cases hr; rfl)))
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head mayHaveSlept; exact AmbientContracts.drop (c.store (fun _ => True) _ mayHaveSlept_sameWGStore))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgDestructPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductDeviceLifecycleContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver wgDestructPrefix) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P _ (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold wgDestructPrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [apply_ite])
    | (maintenance_lift_action_head modifyDev; exact r.startDestruct)
    | (maintenance_lift_action_head socketReinit; exact socketControlNative_preserves_product c r.controls.socket _ ((socketReinit_sameSocket _ _).factor WGOwnedView.toWGStoreView))
    | (maintenance_head peerRemoveAllPrefix; exact peerRemoveAllPrefix_preserves_product c r.controls.removal)
    | (maintenance_lift_action_head modifyDev; exact r.controls.clearHandshakeQueue)
    | (maintenance_lift_action_head ratelimiterUninit; exact r.ratelimiter)
    | (maintenance_head dropDevicePrefix; exact r.drop)
    | (maintenance_lift_action_head retireDeviceUnits; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ retireDeviceUnits_sameWGStore))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head mayHaveSlept; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ mayHaveSlept_sameWGStore))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem wgDeletePrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductDeviceLifecycleContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver wgDeletePrefix) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P _ (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold wgDeletePrefix
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [apply_ite])
    | (maintenance_head wgDownPrefix; exact wgDownPrefix_preserves_product c r.controls)
    | (maintenance_head wgDestructPrefix; exact wgDestructPrefix_preserves_product c r)
    | (maintenance_lift_action_head skipCut; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.skipCut _)))
    | (maintenance_lift_action_head get; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) (get : WG.M WGWorld) (by apply (ProjectedAction.iff_run_ambient _ _ _).mpr; intro w ambient x v ambient' hr; cases hr; rfl)))
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head mayHaveSlept; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ mayHaveSlept_sameWGStore))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

inductive DeviceLifecycleCall where
  | create | destruct | delete

def DeviceLifecycleCall.Result : DeviceLifecycleCall → Type
  | .create | .delete => Int
  | .destruct => Unit

def DeviceLifecycleCall.original (call : DeviceLifecycleCall) : WG.M call.Result :=
  match call with | .create => wgCreate | .destruct => wgDestruct | .delete => wgDelete

def DeviceLifecycleCall.observed (call : DeviceLifecycleCall) : MixedM call.Result :=
  match call with | .create => wgCreatePrefix | .destruct => wgDestructPrefix | .delete => wgDeletePrefix

theorem DeviceLifecycleCall.erases (call : DeviceLifecycleCall) : ErasesStatePrefix call.observed call.original := by
  cases call
  · exact wgCreatePrefix_erases
  · exact wgDestructPrefix_erases
  · exact wgDeletePrefix_erases

theorem DeviceLifecycleCall.preserves_ambient (c : AmbientContracts I)
    (r : DeviceLifecycleContracts I) (call : DeviceLifecycleCall) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call
  · exact r.create
  · exact wgDestructPrefix_preserves c r
  · exact wgDeletePrefix_preserves c r

theorem DeviceLifecycleCall.preserves_ambient_product (c : ProductAmbientContracts I)
    (r : ProductDeviceLifecycleContracts I) (call : DeviceLifecycleCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call
  · exact r.create
  · exact wgDestructPrefix_preserves_product c r
  · exact wgDeletePrefix_preserves_product c r

theorem DeviceLifecycleCall.allocation (call : DeviceLifecycleCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationDeviceLifecycle

end Leanux.Proofs.WG.Lifetimes
