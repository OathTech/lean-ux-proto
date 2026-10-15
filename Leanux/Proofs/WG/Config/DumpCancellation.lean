import Leanux.Runner

set_option synthInstance.maxSize 1024
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.DumpCancellation
open Leanux Leanux.WG Leanux.Runner

def emptyTrace : Trace :=
  { id := "campaign2-empty-dump-cancellation", ops := #[.wgGet {}], hidden := some #[[]] }

def initialWorld : World :=
  { k := initialKernel 32 true, env := harnessEnv, timing := Env.timing,
    portBound := Env.portBound, fixtureNetDevices := Env.fixtureNetDevices,
    hidden := some [] }

def accepted : Bool :=
  match executeTrace emptyTrace with
  | .ok _ => true
  | .error _ => false

def callbackResult : Option (Int × Nat × Bool × Nat) := do
  let .ok (out, _) := (wgGetDeviceDump { hasWg := true } 0 {}).run initialWorld | none
  return (out.ret, out.skb.room, out.ctx.nextPeer.isNone, out.skb.messages.length)

theorem emptyTrace_accepted : accepted = true := by decide +kernel

theorem emptyDump_room : callbackResult = some (0, 3720, true, 1) := by decide +kernel

/-- The header and four retained attributes occupy 52 bytes. The peer-nest
header is cancelled in C; its four bytes must not remain in this accounting. -/
def cancelledNestRoom : Nat :=
  NLMSG_GOODSIZE - (nlmsgTotal 4 + nlaTotal 2 + nlaTotal 4 + nlaTotal 4 + nlaTotal 4)

theorem cancellation_accounting : cancelledNestRoom = 3724 ∧ 3720 + nlaTotal 0 = cancelledNestRoom := by
  decide +kernel

end Leanux.Proofs.WG.Config.DumpCancellation
