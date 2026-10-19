import Leanux.Proofs.WG.TransmitSecurity.EmissionOuterFrames
import Leanux.Proofs.WG.TransmitSecurity.EmissionDumpFrames

/-! Native namespace cleanup retains the pending send buffer; actual sends
remain accounted for by their own source receipts. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EmissionCleanup
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues AuthenticatedEffects

theorem socket_reinit (new4 new6 : Option Nat) : SameView WGWorld.sent (socketReinit new4 new6) := by
  sent_frame [socketReinit,sockFree,Leanux.iputReport] using []

theorem clear_endpoint (pid : PeerId) : SameView WGWorld.sent (clearPeerEndpointSrc pid) := by
  sent_frame [clearPeerEndpointSrc,dstCacheResetNow,dstCacheReset,getAmbient,hiddenJiffies]
    using [getPeer_sent_spec,setPeer_sent_spec]

theorem reinit_spec (P : List SentDatagram → Prop) (new4 new6 : Option Nat) :
    Preserves (fun w => P w.sent) (socketReinit new4 new6) := (socket_reinit new4 new6).wp P

theorem endpoint_spec (P : List SentDatagram → Prop) (pid : PeerId) :
    Preserves (fun w => P w.sent) (clearPeerEndpointSrc pid) := (clear_endpoint pid).wp P

theorem pre_exit : SameView WGWorld.sent netnsPreExit := by
  sent_frame [netnsPreExit] using [reinit_spec,endpoint_spec,EmissionDump.list_spec]

theorem env_cleanup : SameView EmissionOuter.Sent Env.netnsCleanup := by
  intro initial
  change Preserves (fun w : World => EmissionOuter.Sent w = initial) _
  have pre : Preserves (fun w : World => EmissionOuter.Sent w = initial)
      (monadLift netnsPreExit : Leanux.M Unit) := EmissionOuter.wg _ pre_exit initial
  have effects {α : Type} (a : AmbientM α) : Preserves (fun w : World => EmissionOuter.Sent w = initial)
      (monadLift a : Leanux.M α) := EmissionOuter.ambient a initial
  have routes {α : Type} (a : Net.M α) : Preserves (fun w : World => EmissionOuter.Sent w = initial)
      (monadLift a : Leanux.M α) := EmissionOuter.routing a initial
  have env (f : EnvWorld → EnvWorld) : Preserves (fun w : World => EmissionOuter.Sent w = initial)
      (modifyEnv f) := EmissionOuter.env f initial
  routing_tx_source [Env.netnsCleanup,Env.runWorker,getRouting,peekUnit,resolveUnit,skipCut,unsupported,modifyAmbient,hidden]
    using [pre,effects,routes,env]

end Leanux.Proofs.WG.TransmitSecurity.EmissionCleanup
