import Leanux.Proofs.Logged.Checkpoints

/-! Check the historical stale dump cursor recipe's current rejection.
The original runner and its proved checkpoint observer accept the pre-delete
prefix, then reject deletion with a pending dump at c047e64. Later expected
values below describe the historical accepted run, not current checkpoints.
The input records are synthetic and explicit, with no placeholders. -/
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
  -- Preserve the historical pre-delete boundary, but require the current
  -- original and observer to reject the full recipe at the new runner guard.
  let beforeDelete : Trace := { trace with ops := trace.ops.extract 0 3, hidden := trace.hidden.map (·.extract 0 3) }
  let prefixOriginal ← match executeTrace beforeDelete false with
    | .error (index, stop) => throw (IO.userError s!"prefix original {index}: {stop.message}")
    | .ok json => pure json
  let (prefixObserved, checkpoints) ← match (executeTraceCheckpoints projectCursor beforeDelete false).run [] with
    | .error (index, stop) => throw (IO.userError s!"prefix observer {index}: {stop.message}")
    | .ok result => pure result
  if prefixOriginal.compress != prefixObserved.compress || checkpoints.length != 3 ||
      checkpoints[2]? != expected.head? then
    throw (IO.userError "pre-delete dump-cursor checkpoint or original/observer output differs")
  let reason := "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)"
  let (index, site) ← match executeTrace trace false,
      (executeTraceCheckpoints projectCursor trace false).run [] with
    | .error (i, .outsideDomain s message), .error (j, .outsideDomain t other) =>
      if i != 3 || j != i || s != t || message != reason || other != reason then
        throw (IO.userError "original/observer rejection differs from the exact pending-dump guard")
      pure (i, s)
    | _, _ => throw (IO.userError "historical cursor recipe was not rejected by both current runners")
  let some pre := checkpoints[2]? | throw (IO.userError "missing pre-delete checkpoint")
  let output ← IO.getStdout
  output.putStrLn (Json.mkObj [("id", toJson trace.id), ("accepted", toJson false),
    ("current_rejection_check", toJson true), ("original_observer_stop_matches", toJson true),
    ("operation", toJson index), ("stop_site", toJson site), ("reason", toJson reason),
    ("record_origin", toJson "synthetic historical recipe"),
    ("pre_delete_checkpoint", checkpointJson pre),
    ("historical_checkpoints", toJson (expected.map checkpointJson))]).compress
  return 0
