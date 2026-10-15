import Leanux.Proofs.WG.Config.DumpCoalesce

set_option pp.structureInstances false
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

abbrev DumpAccumulator := Array NlMessage × Bool

def receiveDumpStep (_ : Nat) (acc : DumpAccumulator) : M (ForInStep DumpAccumulator) := do
  let (messages, finished) := acc
  if finished then return .done (messages, finished)
  let some ms ← netlinkRecvmsg 7 | do
    invariant "op 9: nothing queued before the dump finished"
    return .yield (messages, finished)
  let mut messages := messages
  let mut finished := finished
  for m in ms do
    messages := messages.push m
    match m with
    | .done .. | .error _ => finished := true
    | .data .. => pure ()
  return .yield (messages, finished)

def getterDrainSource : M (Except Int Json) := do
  let (messages, finished) ← forIn [:4096] (#[], false) receiveDumpStep
  if !finished then invariant "op 9: the dump did not finish"
  coalesce messages.toList

theorem wgGetDevice_source (ref : DeviceRef) :
    wgGetDevice ref = (do netlinkDumpStart 7 ref; getterDrainSource) := rfl

theorem receiveDump_finished (xs : List Nat) (messages : Array NlMessage) :
    forIn xs (messages, true) receiveDumpStep = pure (messages, true) := by
  cases xs <;> simp [List.forIn_cons, List.forIn_nil, receiveDumpStep]

theorem getterDrain_first :
    getterDrainSource = (do
      let first ← receiveDumpStep 0 (#[], false)
      let (messages, finished) ← match first with
        | .done acc => pure acc
        | .yield acc => forIn (List.range' 1 4095) acc receiveDumpStep
      if !finished then invariant "op 9: the dump did not finish"
      coalesce messages.toList) := by
  unfold getterDrainSource
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size]
  change (do
    let acc ← forIn (List.range' 0 (4095 + 1)) (#[], false) receiveDumpStep
    if !acc.2 then invariant "op 9: the dump did not finish"
    coalesce acc.1.toList) = _
  rw [List.range'_succ, List.forIn_cons]
  simp [bind_assoc]
  congr 1
  funext first
  cases first <;> simp [bind_assoc]

end Leanux.Proofs.WG.Config
