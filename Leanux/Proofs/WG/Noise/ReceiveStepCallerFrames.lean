import Leanux.Proofs.WG.Noise.ReceiveStepCallerSource

/-! Native queue updates projected into the campaign view. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ReceiveStepCaller
open Leanux Leanux.WG Leanux.Proofs.WG.Origins
open ReceptionCaller
def pollView (entry : Campaign2.Snapshot) (consumed : Bool) : Campaign2.Snapshot :=
  {entry with ambient := {entry.ambient with steps := (entry.ambient.steps.push
    {decision := .workerConsumed,outcome := consumed,netRx := entry.ambient.netRxSection})}}

def dequeueView (entry : Campaign2.Snapshot)
    (ring : PtrRing (List UInt8 × SkbSource)) : Campaign2.Snapshot :=
  {entry with wg := {entry.wg with device := entry.wg.device.map fun d =>
    {d with handshakeQueue := ring}}}

def decrementView (entry : Campaign2.Snapshot) : Campaign2.Snapshot :=
  {entry with wg := {entry.wg with device := entry.wg.device.map fun d =>
    {d with handshakeQueueLen := d.handshakeQueueLen - 1}}}

theorem snapshot_poll (g : WGWorld) (ambient : Ambient) (consumed : Bool) :
    Campaign2.snapshot g (pollAmbient ambient consumed) =
      pollView (Campaign2.snapshot g ambient) consumed := rfl

theorem snapshot_dequeue (g : WGWorld) (ambient : Ambient)
    (ring : PtrRing (List UInt8 × SkbSource)) :
    Campaign2.snapshot (dequeueWorld g ring) ambient =
      dequeueView (Campaign2.snapshot g ambient) ring := rfl

theorem snapshot_decrement (g : WGWorld) (ambient : Ambient) :
    Campaign2.snapshot (decrementWorld g) ambient =
      decrementView (Campaign2.snapshot g ambient) := rfl


end Leanux.Proofs.WG.Noise.ReceiveStepCaller
