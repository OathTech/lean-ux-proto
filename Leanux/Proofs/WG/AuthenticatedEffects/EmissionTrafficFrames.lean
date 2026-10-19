import Leanux.Proofs.WG.AuthenticatedEffects.EmissionIngressFrames
import Leanux.Proofs.WG.AuthenticatedEffects.EmissionRoutingFrames
import Leanux.Proofs.WG.AuthenticatedEffects.DeliverySource

/-! Fixture traffic preparation and observation bookkeeping preserve sent.
The delivery between observation front/finish is deliberately not framed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes TransmitSecurity
set_option maxHeartbeats 600000

theorem sender (family dest tos : Nat) (ll : Bool) : SameView EmissionOuter.Sent (Env.senderSource family dest tos ll) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.routing a initial
  routing_tx_source [Env.senderSource,getRouting,unsupported] using [ambient,routing]

private theorem xmit_packet (family addr : Nat) (bytes : List UInt8) (mtu tos : Nat) :
    SameView EmissionOuter.Sent (Env.xmitPacket family addr bytes mtu tos) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  routing_tx_source [Env.xmitPacket,invariant,unsupported] using [ambient]

theorem xmit_packets (family addr : Nat) (bytes : List UInt8) (opts : Env.XmitOpts) :
    SameView EmissionOuter.Sent (Env.xmitPackets family addr bytes opts) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have dev : Preserves P (monadLift getDev : Leanux.M Device) := EmissionOuter.wg _ (by sent_frame [] using []) initial
  have fixture : Preserves P getEnv := env_read initial
  have packet (family addr : Nat) (bytes : List UInt8) (mtu tos : Nat) : Preserves P (Env.xmitPacket family addr bytes mtu tos) :=
    xmit_packet family addr bytes mtu tos initial
  routing_tx_source [Env.xmitPackets,unsupported] using [ambient,dev,fixture,packet]

theorem multicast (family addr : Nat) : SameView EmissionOuter.Sent (Env.xmitMulticastLoop family addr) := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have loop : Preserves P (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    EmissionOuter.wg _
      ((pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.EmissionRoutingFrames.«0».Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames.loopback) [] true) initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  routing_tx_source [Env.xmitMulticastLoop,unsupported] using [loop,ambient]

theorem observe_front : SameView EmissionOuter.Sent DeliverySource.observeFront := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have read : Preserves P getWG := EmissionOuter.read_wg initial
  have crypt : Preserves P Env.requireNoCryptWork := no_crypt initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  routing_tx_source [DeliverySource.observeFront,unsupported] using [read,crypt,ambient]

theorem observe_finish : SameView EmissionOuter.Sent DeliverySource.observeFinish := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have read : Preserves P getWG := EmissionOuter.read_wg initial
  have fixture : Preserves P getEnv := env_read initial
  have edit (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := EmissionOuter.env f initial
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.routing a initial
  routing_tx_source [DeliverySource.observeFinish,getRouting] using [read,fixture,edit,routing]

theorem route_into : SameView EmissionOuter.Sent Env.routeIntoWg0 := by
  intro initial
  let P := fun w : World => EmissionOuter.Sent w = initial
  change Preserves P _
  have dev : Preserves P (monadLift getDev : Leanux.M Device) := EmissionOuter.wg _ (by sent_frame [] using []) initial
  have fixture : Preserves P getEnv := env_read initial
  have edit (f : EnvWorld → EnvWorld) : Preserves P (modifyEnv f) := EmissionOuter.env f initial
  have routing {α : Type} (a : Net.M α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.routing a initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  routing_tx_source [Env.routeIntoWg0,Env.outsideWindow,getRouting,modifyRouting,getAmbient,modifyAmbient]
    using [dev,fixture,edit,routing,ambient]

end Leanux.Proofs.WG.AuthenticatedEffects.EmissionFrames
