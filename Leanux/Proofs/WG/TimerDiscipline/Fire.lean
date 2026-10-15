import Leanux.Env
import Leanux.Proofs.WG.TimerDiscipline.Retry

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

theorem throw_bind_timer {α β : Type} (e : Stop) (f : α → M β) :
    ((throw e : M α) >>= f) = throw e := rfl

theorem unsupported_bind_timer {α β : Type} (message : String) (f : α → M β) :
    ((unsupported message : M α) >>= f) = unsupported message := by
  simp only [unsupported, bind_assoc, throw_bind_timer]

theorem fireTimer_source (w : Worker) (jHi : UInt64) :
    fireTimer w jHi = (do
      let selected ← timerSelection w jHi
      fireSelected w selected.1 selected.2) := by
  cases ht : w.timer? with
  | none =>
    simp [fireTimer, timerSelection, ht, invariant]
    rfl
  | some t =>
    simp only [fireTimer, timerSelection, ht, fireSelected, bind_assoc, pure_bind]
    congr 1
    funext d
    generalize hdue : (d.peerList.filter fun pid =>
      match d.peers.get? pid >>= (·.timer t) with
      | some e => timeBefore e jHi
      | none => false) = due
    rcases due with _ | ⟨first, _ | ⟨second, rest⟩⟩
    all_goals try simp only [bind_assoc, pure_bind]
    all_goals congr 1
    all_goals funext unit
    all_goals cases unit <;> simp only [bind_assoc, pure_bind]
    all_goals repeat (first | rfl | (split <;> try simp_all only [bind_assoc, pure_bind, throw_bind_timer, unsupported_bind_timer]) | (congr 1; funext x))
    all_goals try simp_all only [bind_assoc, pure_bind, throw_bind_timer, unsupported_bind_timer, List.contains, List.elem_nil, Bool.not_false]
    all_goals grind only

end Leanux.Proofs.WG.TimerDiscipline
