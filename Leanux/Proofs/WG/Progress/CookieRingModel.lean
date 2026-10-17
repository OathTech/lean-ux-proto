import Leanux.Proofs.WG.Progress.CookieControlModel
import Leanux.Proofs.WG.Campaign2.ProductView
import Leanux.WG.PtrRing

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

/-- Repeated actual poll/discard operations retain every physical ring field.
This is not a claim that arbitrary ring metadata represents a coherent FIFO. -/
def cookieRingAfter : Nat → PtrRing (List UInt8 × SkbSource) → PtrRing (List UInt8 × SkbSource)
  | 0, ring => ring
  | count + 1, ring => cookieRingAfter count ring.consume.2

def cookieRingActivationSnapshot (a : Activation) (d : Device)
    (entry : Campaign2.Product.Snapshot) (summary : CookieActivationSummary) : Campaign2.Product.Snapshot :=
  {entry with
    wg := {entry.wg with device := some {d with
      handshakeQueue := cookieRingAfter summary.processed d.handshakeQueue
      handshakeQueueLen := d.handshakeQueueLen - summary.processed}}
    ambient := {entry.ambient with
      hidden := some summary.rest
      suspended := if summary.yielded then
        entry.ambient.suspended ++ [{a with iterations := a.iterations + summary.processed}]
        else entry.ambient.suspended
      steps := cookieFinalSteps entry.ambient.netRxSection summary entry.ambient.steps}}

def cookieRingTailDevice (d : Device) : Device :=
  {d with handshakeQueue := d.handshakeQueue.consume.2, handshakeQueueLen := d.handshakeQueueLen - 1}

def cookieRingPacketSnapshot (d : Device) (entry : Campaign2.Product.Snapshot)
    (records : List HiddenRecord) : Campaign2.Product.Snapshot :=
  {entry with
    wg := {entry.wg with device := some (cookieRingTailDevice d)}
    ambient := {entry.ambient with hidden := some records, steps := cookiePacketSteps entry.ambient.netRxSection entry.ambient.steps}}

/-- The compositional law keeps physical slots/cursors, including arbitrary
metadata. It does not assert any successful activation or an empty result. -/
theorem cookieRingActivationSnapshot_continue (a : Activation) (d : Device)
    (entry : Campaign2.Product.Snapshot) (records : List HiddenRecord)
    (summary : CookieActivationSummary) :
    cookieRingActivationSnapshot {a with iterations := a.iterations + 1}
      (cookieRingTailDevice d) (cookieRingPacketSnapshot d entry records) summary =
    cookieRingActivationSnapshot a d entry {summary with processed := summary.processed + 1} := by
  simp [cookieRingActivationSnapshot, cookieRingPacketSnapshot, cookieRingTailDevice, cookieRingAfter,
    cookieFinalSteps, cookieProcessedSteps, Nat.sub_sub,
    Nat.add_comm, Nat.add_left_comm]


end Leanux.Proofs.WG.Progress
