import Leanux.Proofs.WG.Progress.CookieBoundedSource
import Leanux.Proofs.WG.Campaign2.Bridge
/-! Historical list-based continuation support pending the ring carry. The corrected
bounded operational contracts are in CookieBoundedSource; no drain adequacy is claimed. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

def cookieActivationWorld (a : Activation) (w : World) (d : Device)
    (summary : CookieActivationSummary) : World :=
  {w with
    k := {w.k with wg := some {d with
      handshakeQueue := d.handshakeQueue.drop summary.processed
      handshakeQueueLen := d.handshakeQueueLen - summary.processed}}
    hidden := some summary.rest
    suspended := if summary.yielded then
      w.suspended ++ [{a with iterations := a.iterations + summary.processed}]
      else w.suspended
    steps := cookieFinalSteps w.netRxSection summary w.steps}

theorem cookieActivationWorld_continue (a : Activation) (w : World) (d : Device)
    (msg : List UInt8) (src : SkbSource) (rest : List (List UInt8 × SkbSource))
    (records : List HiddenRecord) (summary : CookieActivationSummary)
    (queue : d.handshakeQueue = (msg,src)::rest) :
    cookieActivationWorld {a with iterations := a.iterations+1}
      {cookieMissStepView w d rest with hidden := some records} (cookieTailDevice d) summary =
    cookieActivationWorld a w d {summary with processed := summary.processed+1} := by
  simp [cookieActivationWorld, cookieMissStepView, cookieTailDevice, cookieFinalSteps,
    cookieProcessedSteps, cookiePacketSteps, queue, Nat.sub_sub,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

end Leanux.Proofs.WG.Progress
