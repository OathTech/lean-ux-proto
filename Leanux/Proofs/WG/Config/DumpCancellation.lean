import Leanux.Runner

set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.DumpCancellation
open Leanux Leanux.WG Leanux.Runner

def emptyTrace : Trace :=
  { id := "campaign2-empty-dump-cancellation", ops := #[.wgGet {}], hidden := some #[[]] }

def initialWireGuard : WGWorld :=
  { (initialWG true) with
    portBound := Env.portBound,
    fixtureNetDevices := Env.fixtureNetDevices }

def initialAmbient : Ambient :=
  { env := harnessEnv, timing := Env.timing, hidden := some [] }

def accepted : Bool :=
  match executeTrace emptyTrace with
  | .ok _ => true
  | .error _ => false

def callbackResult : Option (Int × Nat × Bool × Nat) := do
  let .ok ((out, _), _) :=
    ((wgGetDeviceDump { hasWg := true } 0 {}).run initialWireGuard).run initialAmbient | none
  return (out.ret, out.skb.room, out.ctx.nextPeer.isNone, out.skb.messages.length)

theorem emptyTrace_accepted : accepted = true := by decide +kernel

theorem emptyDump_room : callbackResult = some (0, 3724, true, 1) := by decide +kernel

/-- The message header and four retained attributes occupy 52 bytes. The empty
peer nest is cancelled to its pre-reservation snapshot, retaining the message
but restoring the nest header's four bytes. -/
def cancelledNestRoom : Nat :=
  NLMSG_GOODSIZE - (nlmsgTotal 4 + nlaTotal 2 + nlaTotal 4 + nlaTotal 4 + nlaTotal 4)

theorem cancellation_accounting : cancelledNestRoom = 3724 ∧ callbackResult = some (0, cancelledNestRoom, true, 1) := by
  decide +kernel

end Leanux.Proofs.WG.Config.DumpCancellation
