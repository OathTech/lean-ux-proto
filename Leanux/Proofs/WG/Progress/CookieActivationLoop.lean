import Leanux.Proofs.WG.Progress.CookieActivationCompositionModel
import Leanux.Proofs.WG.Progress.CookieActivationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

def cookieActivationWorld (a : Activation) (w : World) (d : Device)
    (summary : CookieActivationSummary) : World :=
  {w with
    wg := {w.wg with dev := some {d with
      handshakeQueue := cookieRingAfter summary.processed d.handshakeQueue
      handshakeQueueLen := d.handshakeQueueLen - summary.processed}}
    ambient := {w.ambient with
      hidden := some summary.rest
      suspended := if summary.yielded then
        w.ambient.suspended ++ [{a with iterations := a.iterations + summary.processed}]
        else w.ambient.suspended
      steps := cookieFinalSteps w.ambient.netRxSection summary w.ambient.steps}}

theorem cookieActivationWorld_continue (a : Activation) (w : World) (d : Device)
    (msg : List UInt8) (src : SkbSource) (rest : PtrRing (List UInt8 × SkbSource))
    (records : List HiddenRecord) (summary : CookieActivationSummary)
    (queue : d.handshakeQueue.consume = (some (msg,src), rest)) :
    cookieActivationWorld {a with iterations := a.iterations+1}
      {cookieMissStepView w d rest with ambient := {(cookieMissStepView w d rest).ambient with hidden := some records}}
      (cookieTailDevice d) summary =
    cookieActivationWorld a w d {summary with processed := summary.processed+1} := by
  have tail : d.handshakeQueue.consume.2 = rest := congrArg Prod.snd queue
  simp [cookieActivationWorld, cookieMissStepView, cookieTailDevice,
    cookieRingTailDevice, cookieRingAfter, cookieFinalSteps,
    cookieProcessedSteps, cookiePacketSteps, tail, Nat.sub_sub,
    Nat.add_comm, Nat.add_left_comm]


end Leanux.Proofs.WG.Progress
