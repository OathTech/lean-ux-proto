import Leanux.Proofs.Logged.Checkpoints

/-! Reproduce the stale dump cursor's effect through the original runner and
its proved checkpoint observer. The generated stream is synthetic, explicit
and replayed without placeholders. Every expected checkpoint is asserted. -/
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged

private structure CursorCheckpoint where
  index : Nat
  cursor : Option Nat
  running : Bool
  frontier : Nat
  ifindex : Option Nat
  peer : Option (Nat × Nat × Bool)
  listed : Bool
  hashed : Bool
  deriving BEq, Repr

private def projectCursor (index : Nat) (w : World) : CursorCheckpoint :=
  { index, cursor := w.k.nlSock8.ctx.nextPeer, running := w.k.nlSock8.cbRunning,
    frontier := w.k.peerCounter, ifindex := w.k.wg.map (·.ifindex),
    peer := (w.k.wg.bind (·.peers[26]?)).map fun p => (p.internalId, p.refcount, p.isDead),
    listed := w.k.wg.any (·.peerList.contains 26),
    hashed := w.k.wg.any fun d => d.peerHashtable.any (·.2 == 26) }

private def expected : List CursorCheckpoint :=
  [⟨2, some 26, true, 28, some 3, some (27, 2, false), true, true⟩,
   ⟨3, some 26, true, 28, none, none, false, false⟩,
   ⟨4, some 26, true, 28, some 4, none, false, false⟩,
   ⟨6, some 26, true, 55, some 4, some (55, 1, false), true, true⟩,
   ⟨7, none, false, 55, some 4, none, true, true⟩]

private def checkpointJson (c : CursorCheckpoint) : Json :=
  Json.mkObj [("operation", toJson c.index), ("cursor_slot", toJson c.cursor),
    ("dump_running", toJson c.running), ("peer_frontier", toJson c.frontier),
    ("device_ifindex", toJson c.ifindex),
    ("slot26", match c.peer with
      | none => .null
      | some (identity, refs, dead) => Json.mkObj
          [("lifetime", toJson identity), ("references", toJson refs), ("dead", toJson dead)]),
    ("configured_list_has26", toJson c.listed), ("public_key_hash_has26", toJson c.hashed)]

def main : IO UInt32 := do
  let input ← IO.getStdin
  let trace ← match Json.parse (← input.getLine) >>= parseTrace with
    | .error message => throw (IO.userError s!"invalid witness: {message}")
    | .ok t => pure t
  if trace.id != "r2_stale_dump_cursor" || trace.hidden.isNone || trace.ops.size != 8 then
    throw (IO.userError "expected the eight-operation r2-stale-dump-cursor witness with explicit records")
  let original ← match executeTrace trace false with
    | .error (index, stop) => throw (IO.userError s!"original operation {index}: {stop.message}")
    | .ok json => pure json
  let (observed, checkpoints) ← match (executeTraceCheckpoints projectCursor trace false).run [] with
    | .error (index, stop) => throw (IO.userError s!"observer operation {index}: {stop.message}")
    | .ok result => pure result
  if original.compress != observed.compress then
    throw (IO.userError "original and checkpoint runner outputs disagree")
  if checkpoints.length != trace.ops.size then
    throw (IO.userError "checkpoint count does not equal operation count")
  for want in expected do
    let some actual := checkpoints[want.index]?
      | throw (IO.userError s!"missing checkpoint {want.index}")
    if actual != want then
      throw (IO.userError s!"checkpoint mismatch: expected {repr want}; observed {repr actual}")
  let output ← IO.getStdout
  output.putStrLn (Json.mkObj [("id", toJson trace.id), ("accepted", toJson true),
    ("original_json_matches", toJson true), ("record_origin", toJson "synthetic"),
    ("finding", toJson "stale cursor retargets replacement lifetime 55; no old-identity resurrection"),
    ("checkpoints", toJson (expected.map checkpointJson))]).compress
  return 0
