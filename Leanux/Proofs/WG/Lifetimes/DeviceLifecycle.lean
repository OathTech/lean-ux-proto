import Leanux.Proofs.WG.Lifetimes.DeviceControls
import Leanux.Proofs.WG.Lifetimes.DeviceCreation

/-! Whole device creation, destruction and deletion. Destruction preserves the
actual peer-removal and socket-access prefixes, including every original Stop,
then records retirement of the actual residual stores at the final device drop.
The drop is logical store accounting, not a proof of per-object kernel frees. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def wgDestructPrefix : MixedM Unit := do
  liftPrefix (modifyDev fun d => {d with creatingNet := false, incomingPort := 0})
  liftPrefix (socketReinit none none)
  peerRemoveAllPrefix
  let d ← liftPrefix getDev
  if !d.sendWorkQueue.isEmpty || !d.encryptQueue.empty || !d.txWorkQueue.isEmpty
      || !d.decryptQueue.empty || !d.clearWorkQueue.isEmpty then
    liftPrefix (unsupported "wg_destruct with queued work (destroy_workqueue runs it)")
  if !d.handshakeQueue.isEmpty then
    liftPrefix (invariant "wg_destruct with handshake messages queued (wg_stop drains the ring)")
  liftPrefix mayHaveSlept
  liftPrefix (modifyDev fun d => {d with handshakeQueue := [], handshakeQueueLen := 0})
  liftPrefix mayHaveSlept
  liftPrefix ratelimiterUninit
  dropDevicePrefix
  liftPrefix retireDeviceUnits

def wgDeletePrefix : MixedM Int := do
  if (← liftPrefix getK).wg.isNone then return -ENODEV
  if (← liftPrefix getDev).running then wgDownPrefix
  liftPrefix (skipCut allocCuts)
  liftPrefix mayHaveSlept
  wgDestructPrefix
  return 0

theorem wgDestructPrefix_erases : ErasesPrefix wgDestructPrefix wgDestruct := by
  unfold wgDestructPrefix wgDestruct
  repeat' first
    | with_reducible exact peerRemoveAllPrefix_erases
    | with_reducible exact dropDevicePrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgDeletePrefix_erases : ErasesPrefix wgDeletePrefix wgDelete := by
  unfold wgDeletePrefix wgDelete
  repeat' first
    | with_reducible exact wgDownPrefix_erases
    | with_reducible exact wgDestructPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

structure DeviceLifecycleContracts (I : List LifetimeEvent → World → Prop) : Prop where
  controls : DeviceControlContracts I
  startDestruct : PrefixPreserves I LifetimeEvent.Safe
    (liftPrefix (modifyDev fun d => {d with creatingNet := false, incomingPort := 0}))
  ratelimiter : PrefixPreserves I LifetimeEvent.Safe (liftPrefix ratelimiterUninit)
  drop : PrefixPreserves I LifetimeEvent.Safe dropDevicePrefix
  create : PrefixPreserves I LifetimeEvent.Safe wgCreatePrefix

theorem allocationDeviceLifecycle : DeviceLifecycleContracts AllocationInv := by
  refine ⟨allocationDeviceControl, ?_, ?_, dropDevicePrefix_allocation, wgCreatePrefix_allocation⟩
  · apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    apply hi.congr
    · cases hr
      unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · cases hr
      simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl
  · apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    have he := ratelimiterUninit_sameRatelimiterKernel w x v hr
    have hi' := congrArg (fun k => identityView {w with k}) he
    have hm' := congrArg (fun k => allocationMetadata {w with k}) he
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents at hi' ⊢
      simpa [ratelimiterKernelView, ratelimiterKernel] using hi'
    · simpa [ratelimiterKernelView, ratelimiterKernel, allocationMetadata] using hm'

theorem wgDestructPrefix_preserves (c : AmbientContracts I) (r : DeviceLifecycleContracts I) :
    PrefixPreserves I LifetimeEvent.Safe wgDestructPrefix := by
  unfold wgDestructPrefix
  repeat' first
    | with_reducible exact r.startDestruct
    | with_reducible exact socketControlLift_preserves c r.controls.socket _ (socketReinit_sameSocketKernel _ _)
    | with_reducible exact peerRemoveAllPrefix_preserves c r.controls.removal
    | with_reducible exact r.controls.clearHandshakeQueue
    | with_reducible exact r.ratelimiter
    | with_reducible exact r.drop
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ mayHaveSlept_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ retireDeviceUnits_sameKernel)
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr <;> rfl))
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem wgDeletePrefix_preserves (c : AmbientContracts I) (r : DeviceLifecycleContracts I) :
    PrefixPreserves I LifetimeEvent.Safe wgDeletePrefix := by
  unfold wgDeletePrefix
  repeat' first
    | with_reducible exact wgDownPrefix_preserves c r.controls
    | with_reducible exact wgDestructPrefix_preserves c r
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ mayHaveSlept_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (skipCut_sameKernel _))
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr <;> rfl))
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

inductive DeviceLifecycleCall where
  | create | destruct | delete

def DeviceLifecycleCall.Result : DeviceLifecycleCall → Type
  | .create | .delete => Int
  | .destruct => Unit

def DeviceLifecycleCall.original (call : DeviceLifecycleCall) : M call.Result :=
  match call with | .create => wgCreate | .destruct => wgDestruct | .delete => wgDelete

def DeviceLifecycleCall.observed (call : DeviceLifecycleCall) : MixedM call.Result :=
  match call with | .create => wgCreatePrefix | .destruct => wgDestructPrefix | .delete => wgDeletePrefix

theorem DeviceLifecycleCall.erases (call : DeviceLifecycleCall) : ErasesPrefix call.observed call.original := by
  cases call
  · exact wgCreatePrefix_erases
  · exact wgDestructPrefix_erases
  · exact wgDeletePrefix_erases

theorem DeviceLifecycleCall.preserves_ambient (c : AmbientContracts I)
    (r : DeviceLifecycleContracts I) (call : DeviceLifecycleCall) :
    PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call
  · exact r.create
  · exact wgDestructPrefix_preserves c r
  · exact wgDeletePrefix_preserves c r

theorem DeviceLifecycleCall.allocation (call : DeviceLifecycleCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationDeviceLifecycle

end Leanux.Proofs.WG.Lifetimes
