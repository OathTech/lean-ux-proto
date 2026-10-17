import Leanux.Env
import Leanux.Proofs.WG.TimerDiscipline.FireUnitSource

/-! Historical pre-wheel dispatcher definitions remain for pending callers. The checked current-unit factor is in FireUnitSource; these definitions do not implement the current runTimers selection. -/

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Original dispatcher selection, including named identities and all failure arms. -/
def timerSelection (w : Worker) (jHi : UInt64) : M (PeerId × PeerTimer) := do
  let some t := w.timer? | invariant s!"{w.symbol} is not a timer callback"
  let d ← getDev
  let due := d.peerList.filter fun pid =>
    match d.peers.get? pid >>= (·.timer t) with
    | some e => timeBefore e jHi
    | none => false
  let named ← match ← peekUnit w with
    | some u =>
      match (← get).timerUnits.find? (·.1 == u) with
      | some (_, pid, t') =>
        if t' != t then throw (.hidden s!"a section of {w.symbol} for another timer of peer {pid}")
        pure (some pid)
      | none => throw (.hidden s!"a section of {w.symbol} for a timer the mirror never armed ({u})")
    | none => pure none
  match named with
  | some pid =>
    if !due.contains pid then
      throw (.hidden s!"a section of {w.symbol} for peer {pid}, whose timer is not pending with expires before jiffies {jHi}")
    return (pid, t)
  | none =>
    match due with
    | [pid] => return (pid, t)
    | [] => throw (.hidden s!"a section of {w.symbol}, but no peer's timer is pending with expires before jiffies {jHi}")
    | _ => unsupported s!"several peers' timers for {w.symbol} due in one pass (their order)"

def fireSelected (w : Worker) (pid : PeerId) (timer : PeerTimer) : M Unit := do
  delTimer pid timer
  runTimerSection w (timerCallback pid timer)

end Leanux.Proofs.WG.TimerDiscipline
