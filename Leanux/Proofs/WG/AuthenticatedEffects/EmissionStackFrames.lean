import Leanux.Proofs.WG.TransmitSecurity.EmissionOuterFrames

/-! The native IPv6 input leaf delivers only to the fixture inbox. Its sent
frame is proved directly, independently of the packet-store projection. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes TransmitSecurity

theorem stack6 (bytes : List UInt8) : SameView EmissionOuter.Sent (Env.Stack.receive6 bytes) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have read : Preserves P (getWG : Leanux.M WGWorld) := EmissionOuter.read_wg initial
  have write (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := EmissionOuter.env f initial
  routing_tx_source [Env.Stack.receive6,Env.Stack.excluded,invariant,unsupported] using [ambient,read,write]

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
