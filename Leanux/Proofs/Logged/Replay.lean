import Leanux.Proofs.Logged.Runner

/-! A small reproduction command for recorded campaign witnesses. It executes
both the original runner and its proved observer, rejects failures or an
observation mismatch, and prints the committed validator history. This is a
reproducer, not a replacement for the result theorems or the proof gate. -/
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged

def main : IO UInt32 := do
  let input ← IO.getStdin
  let line ← input.getLine
  let trace ← match Json.parse line >>= parseTrace with
    | .error message => throw (IO.userError s!"invalid witness: {message}")
    | .ok t => pure t
  if trace.hidden.isNone then
    throw (IO.userError "witness must supply an explicit recorded input stream")
  let original ← match executeTrace trace false with
    | .error (index, stop) => throw (IO.userError s!"operation {index}: {stop.message}")
    | .ok json => pure json
  let (observed, history) ← match (executeTraceLogged trace false).run [] with
    | .error (index, stop) => throw (IO.userError s!"observer operation {index}: {stop.message}")
    | .ok result => pure result
  if original.compress != observed.compress then
    throw (IO.userError "original and observed runner outputs disagree")
  let events := history.map fun e =>
    Json.mkObj [("keypair_lifetime", toJson e.keypair), ("wire_counter", toJson e.nonce)]
  let branches ← match original.getObjValAs? (Array Json) "branches" with
    | .error message => throw (IO.userError message)
    | .ok bs => pure bs
  let mut validators : Array Json := #[]
  for b in branches do
    let label ← match b.getObjValAs? String "label" with
      | .error message => throw (IO.userError message)
      | .ok s => pure s
    if label.startsWith "counter_validate." && !label.startsWith "counter_validate.clear_iter" then
      validators := validators.push b
  let output ← IO.getStdout
  output.putStrLn (Json.mkObj [("id", toJson trace.id), ("accepted", toJson true),
    ("operations", toJson trace.ops.size), ("history", toJson events),
    ("validator_branches", toJson validators)]).compress
  return 0
