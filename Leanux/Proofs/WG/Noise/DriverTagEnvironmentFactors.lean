import Leanux.Env

/-! The existing native environment-down factor, isolated from observer and
retention dependencies without changing its definition or source theorem. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Environment
open Leanux Leanux.WG
universe u

def envDownWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → Leanux.M α → m α) (idle down : m Unit) : m Int := do
  let some d := (← lift getWG).dev | return -ENODEV
  if !d.running then return 0
  idle
  down
  lift (skipCut allocCuts)
  lift Net.Fib.rtCacheFlush
  lift (Net.Fib.netdevDown WG0_IFINDEX)
  lift (modifyRouting fun w => {w with defaultRoute6 := false, addrs6 := [], ipv6Gen := w.ipv6Gen+1})
  return 0

theorem envDown_factor : Env.wgDown =
    envDownWith (fun {_} a => a) Env.requireIdleDevice (liftWG WG.wgDown) := rfl

end Leanux.Proofs.WG.Noise.DriverTags.Environment
