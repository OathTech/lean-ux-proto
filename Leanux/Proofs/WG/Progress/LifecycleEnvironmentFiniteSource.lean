import Leanux.Proofs.WG.Progress.MaintenanceFiniteSource
import Leanux.Proofs.WG.Noise.DriverTagEnvironmentFactors

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.LifecycleFinite
open Leanux Leanux.WG

/-- Original environment down, using the concrete finite native stop/drain
callback. The actual idle checks, routing notifications and all Stops remain. -/
def envDown : Leanux.M Int :=
  Noise.DriverTags.Environment.envDownWith (fun {_} a => a) Env.requireIdleDevice
    (liftWG MaintenanceFinite.down)

theorem envDown_source : Env.wgDown = envDown := by
  rw [Noise.DriverTags.Environment.envDown_factor, MaintenanceFinite.down_source]
  rfl


universe u

/-- Local source variants of Configuration.envDeleteWith/envDelete_factor in
Queues.JointDelete. Its observer import closure is currently lagging. Replace
these two declarations with that shared source when its carry lands. -/
def envDeleteWith_variant {m : Type → Type u} [Monad m]
    (lift : {α : Type} → Leanux.M α → m α) (idle down destruct : m Unit) : m Int := do
  if (← lift getWG).dev.isSome then idle
  let pending (sock : WG.NlSock) : Bool :=
    sock.cbRunning || sock.queue.any fun chunk => chunk.messages.any fun m => match m with | .done .. => true | _ => false
  let k ← lift getWG
  if pending k.nlSock7 || pending k.nlSock8 then
    lift (unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)")
  let onDown : m Unit := do
    lift Net.Fib.rtCacheFlush
    lift (Net.Fib.netdevDown WG0_IFINDEX)
    lift (modifyRouting fun w => { w with defaultRoute6 := false, addrs6 := [], ipv6Gen := w.ipv6Gen + 1 })
  let onUnregister : m Unit := do
    lift Env.inetdevDestroy
    lift (Net.Fib.netdevUnregister WG0_IFINDEX)
    lift (modifyRouting fun w => { w with addrs6 := [], defaultRoute6 := false, ipv6Gen := w.ipv6Gen + 1 })
  if (← lift getWG).dev.isNone then return -ENODEV
  if (← lift (liftWG getDev)).running then
    down
    onDown
  lift (skipCut allocCuts)
  onUnregister
  lift (liftWG mayHaveSlept)
  destruct
  return 0

theorem envDelete_factor_variant : Env.wgDelete = envDeleteWith_variant (fun {_} a => a)
    Env.requireIdleDevice (liftWG wgDown) (liftWG wgDestruct) := by
  simp only [Env.wgDelete,WG.wgDelete,envDeleteWith_variant]
  rfl


/-- Actual environment deletion with finite down and destruction callbacks.
The stepped-dump and idle checks remain the original native guards. -/
def envDelete : Leanux.M Int :=
  envDeleteWith_variant (fun {_} a => a) Env.requireIdleDevice
    (liftWG MaintenanceFinite.down) (liftWG MaintenanceFinite.destruct)

theorem envDelete_source : Env.wgDelete = envDelete := by
  rw [envDelete_factor_variant, MaintenanceFinite.down_source, MaintenanceFinite.destruct_source]
  rfl

end Leanux.Proofs.WG.Progress.LifecycleFinite
