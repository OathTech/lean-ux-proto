import Leanux.Proofs.Logged.Runner

/-! Reproduce the receive wire-limit boundary through the original runner and
its proved validator observer. The input is reconstructed from tracked fixtures,
with synthetic wait bounds; it is not a new Linux capture. -/
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged

private def selectedLabels : List String :=
  ["decrypt_packet.key_invalid=0", "decrypt_packet.key_expired=0",
   "decrypt_packet.counter_limit=0", "decrypt_packet.decrypt_failed=0",
   "wg_packet_decrypt_worker.decrypted=1", "counter_validate.counter_at_limit=0",
   "counter_validate.theirs_at_limit=1", "wg_packet_rx_poll.counter_invalid=1"]

def main : IO UInt32 := do
  let input ← IO.getStdin
  let trace ← match Json.parse (← input.getLine) >>= parseTrace with
    | .error message => throw (IO.userError s!"invalid witness: {message}")
    | .ok t => pure t
  if !(trace.id == "r5_rx_wire_limit" || trace.id == "r5_rx_wire_past_limit") ||
      trace.hidden.isNone || trace.ops.size != 5 then
    throw (IO.userError "expected a five-operation wire-limit witness with explicit records")
  let wireCounter := REJECT_AFTER_MESSAGES + if trace.id == "r5_rx_wire_past_limit" then 1 else 0
  let original ← match executeTrace trace false with
    | .error (index, stop) => throw (IO.userError s!"original operation {index}: {stop.message}")
    | .ok json => pure json
  let (observed, history) ← match (executeTraceLogged trace false).run [] with
    | .error (index, stop) => throw (IO.userError s!"observer operation {index}: {stop.message}")
    | .ok result => pure result
  if original.compress != observed.compress then
    throw (IO.userError "original and observed runner outputs disagree")
  if !history.isEmpty then
    throw (IO.userError "the rejected wire-limit packet unexpectedly produced an acceptance")
  let branches ← match original.getObjValAs? (Array Json) "branches" with
    | .error message => throw (IO.userError message)
    | .ok bs => pure bs
  let mut selected : List String := []
  let mut evidence : Array Json := #[]
  for b in branches do
    let index ← match b.getObjValAs? Nat "index" with
      | .error message => throw (IO.userError message)
      | .ok i => pure i
    let label ← match b.getObjValAs? String "label" with
      | .error message => throw (IO.userError message)
      | .ok s => pure s
    if index == 4 && selectedLabels.contains label then
      selected := selected ++ [label]
      evidence := evidence.push b
      if label == "decrypt_packet.counter_limit=0" || label == "counter_validate.theirs_at_limit=1" then
        let operands ← match b.getObjValAs? (List Int) "operands" with
          | .error message => throw (IO.userError message)
          | .ok xs => pure xs
        let expected : List Int := if label == "decrypt_packet.counter_limit=0" then
          [0, REJECT_AFTER_MESSAGES] else [wireCounter, REJECT_AFTER_MESSAGES]
        if operands != expected then
          throw (IO.userError s!"unexpected comparison operands at {label}: {repr operands}")
  if selected != selectedLabels then
    throw (IO.userError s!"unexpected branch order: {repr selected}")
  let output ← IO.getStdout
  output.putStrLn (Json.mkObj [("id", toJson trace.id), ("accepted", toJson true),
    ("original_json_matches", toJson true), ("record_origin", toJson "reconstructed; synthetic wait bounds"),
    ("wire_counter", toJson wireCounter), ("validator_acceptances", toJson history.length),
    ("finding", toJson "wire nonce at or past the limit decrypts successfully, then replay validation rejects it"),
    ("branches", .arr evidence)]).compress
  return 0
