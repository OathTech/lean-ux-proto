import Leanux.Proofs.WG.Progress.CookieControlModel
import Leanux.Env.Batch
import Leanux.Proofs.WG.Campaign2.View

/-! Data-only receive activation model on cookie-classified queues with an empty index table. It retains original hidden-control validation, exact errors, record suffixes, queue consumption and yielded activation updates. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux

def cookieActivationSnapshot (a : Activation) (d : WG.Device)
    (entry : Campaign2.Snapshot) (summary : CookieActivationSummary) : Campaign2.Snapshot :=
  {entry with
    wg := {entry.wg with device := some {d with
      handshakeQueue := d.handshakeQueue.drop summary.processed
      handshakeQueueLen := d.handshakeQueueLen - summary.processed}}
    ambient := {entry.ambient with
      hidden := some summary.rest
      suspended := if summary.yielded then
        entry.ambient.suspended ++ [{a with iterations := a.iterations + summary.processed}]
        else entry.ambient.suspended
      steps := cookieFinalSteps entry.ambient.netRxSection summary entry.ambient.steps}}

theorem cookieActivationSnapshot_drained (a : Activation) (d : WG.Device)
    (entry : Campaign2.Snapshot) (summary : CookieActivationSummary)
    (processed : summary.processed = d.handshakeQueue.length) :
    (cookieActivationSnapshot a d entry summary).wg.device =
      some {d with handshakeQueue := [], handshakeQueueLen := d.handshakeQueueLen - summary.processed} := by
  simp [cookieActivationSnapshot, processed]

def cookieTailDevice (d : WG.Device) : WG.Device :=
  {d with
    handshakeQueue := d.handshakeQueue.drop 1
    handshakeQueueLen := d.handshakeQueueLen - 1}

def cookiePacketSnapshot (d : WG.Device) (entry : Campaign2.Snapshot)
    (records : List HiddenRecord) : Campaign2.Snapshot :=
  {entry with
    wg := {entry.wg with device := some (cookieTailDevice d)}
    ambient := {entry.ambient with
      hidden := some records
      steps := cookiePacketSteps entry.ambient.netRxSection entry.ambient.steps}}

theorem cookieActivationSnapshot_continue (a : Activation) (d : WG.Device)
    (entry : Campaign2.Snapshot) (records : List HiddenRecord)
    (summary : CookieActivationSummary) :
    cookieActivationSnapshot {a with iterations := a.iterations + 1}
      (cookieTailDevice d) (cookiePacketSnapshot d entry records) summary =
    cookieActivationSnapshot a d entry {summary with processed := summary.processed + 1} := by
  simp [cookieActivationSnapshot, cookiePacketSnapshot, cookieTailDevice,
    cookieFinalSteps, cookieProcessedSteps, List.drop_drop, Nat.sub_sub,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def CookieOnly (d : WG.Device) : Prop :=
  ∀ msg src, (msg, src) ∈ d.handshakeQueue → WG.messageType msg = WG.MESSAGE_HANDSHAKE_COOKIE

end Leanux.Proofs.WG.Progress
