import Leanux.Proofs.WG.AuthenticatedEffects.EmissionDeferredFrames
import Leanux.Proofs.WG.TransmitSecurity.EmissionDispatchFrames

/-! Environment control leaves preserve the actual pending send buffer.
Shutdown and deletion themselves remain callback-parametric source proofs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes TransmitSecurity

theorem idle_device : SameView EmissionOuter.Sent Env.requireIdleDevice := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have crypt : Preserves P Env.requireNoCryptWork := no_crypt initial
  have dev : Preserves P (monadLift getDev : Leanux.M Device) := EmissionOuter.wg _ (by sent_frame [] using []) initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  routing_tx_source [Env.requireIdleDevice,unsupported] using [crypt,dev,ambient]

theorem inetdev_destroy : SameView EmissionOuter.Sent Env.inetdevDestroy := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.routing a initial
  routing_tx_source [Env.inetdevDestroy,getRouting,modifyRouting] using [routing]

theorem slept : SameView WGWorld.sent mayHaveSlept := by
  sent_frame [mayHaveSlept] using []

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
