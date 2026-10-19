import Leanux.Proofs.WG.Progress.KeepaliveFiniteSource
import Leanux.Proofs.WG.Noise.LifecycleFactors

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.LifecycleFinite
open Leanux Leanux.WG
open Leanux.Proofs.WG.Noise.LifecycleSource

/-- The captured peer list and all original guards are retained; only the
guarded keepalive allocation uses its concrete finite counterpart. -/
def openDevice : WG.M Int := openWith HandshakeFinite.keepalive

theorem open_source : WG.wgOpen = openDevice := by
  rw [open_factor]
  have keepalive : WG.sendKeepalive = HandshakeFinite.keepalive :=
    funext HandshakeFinite.keepalive_source
  rw [keepalive]
  rfl

/-- The running flag is set before open and reset on the original negative result. -/
def up : WG.M Int := upWith openDevice

theorem up_source : WG.wgUp = up := by
  rw [up_factor, open_source]
  rfl

/-- The original missing/already-running exits, routing notifications, and
deferred route flag are preserved exactly. -/
def envUp : Leanux.M Int := envUpWith up

theorem envUp_source : Env.wgUp = envUp := by
  rw [envUp_factor, up_source]
  rfl

end Leanux.Proofs.WG.Progress.LifecycleFinite
