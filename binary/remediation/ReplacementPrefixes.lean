import ProbeSupport

/-! Diagnostic only: run the original mirror to completed-operation boundaries
around a replacement call. Neither boundary is asserted to be the call's entry.
No captured heap values enter the source execution. -/
open Lean Leanux Leanux.WG

def entryJson (e : IndexEntry) : Json :=
  let (kind, id) := match e.owner with
    | .handshake pid => ("handshake", pid)
    | .keypair kid => ("keypair", kid)
  Json.mkObj [("index", toJson e.index), ("kind", toJson kind), ("id", toJson id)]

def prefixJson (input : ProbeInput) (count : Nat) : Except String Json := do
  let w ← replayRecordedPrefix input.trace count
  let some d := w.wg.dev | throw "source prefix has no device"
  let peers := d.peers.toList.map fun (id, p) => Json.mkObj [
    ("id", toJson id), ("public_key", toJson (p.remoteStatic.map UInt8.toNat)),
    ("refcount", toJson p.refcount), ("handshake_peer", toJson p.handshakeEntryPeer)]
  let keypairs := d.keypairs.toList.map fun (id, k) => Json.mkObj [
    ("id", toJson id), ("internal_id", toJson k.internalId), ("peer", toJson k.peer)]
  return Json.mkObj [("completed_operations", toJson count),
    ("index_table", toJson (d.indexTable.map entryJson)),
    ("peers", toJson peers), ("keypairs", toJson keypairs),
    ("hidden_consumed", toJson (w.ambient.hidden == some []))]

def main (args : List String) : IO UInt32 := do
  let [inputPath, operationText] := args
    | IO.eprintln "usage: ReplacementPrefixes INPUT.json CAPTURED_OPERATION"; return 1
  let some operation := operationText.toNat?
    | IO.eprintln "captured operation must be a natural number"; return 1
  let parsed := Json.parse (← IO.FS.readFile inputPath) >>= fromJson? (α := ProbeInput)
  let result := do
    let input ← parsed
    let before ← prefixJson input operation
    let after ← prefixJson input (operation + 1)
    pure (Json.mkObj [("before", before), ("after", after)])
  match result with
  | .ok report => IO.println report.compress; return 0
  | .error error => IO.eprintln s!"FAIL: {error}"; return 1
