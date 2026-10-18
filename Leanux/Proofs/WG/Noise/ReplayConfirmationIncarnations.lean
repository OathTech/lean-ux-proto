import Leanux.Proofs.WG.Queues.RunnerAccount

/-! Runtime witness for the distinction between a device-local keypair slot and
an allocation lifetime. This module does not prove the finite execution by
kernel reduction. It uses the existing initialized runner observer whose
generic erasure theorem is RxCredits.RunnerAccount.json.
Run with the unmodified d2_respond_then_data corpus JSON on standard input. -/

namespace Leanux.Proofs.WG.Noise.ConfirmationIncarnationWitness
open Lean Leanux Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.WG.Queues

def allocationPair : RxHistory.Event → Option (Nat × Nat)
 | .audit (.lifetime (.keypair (.allocate slot stamp))) => some (slot,stamp)
 | _ => none
def consumeSummary : RxHistory.Event →
    Option (Nat × Nat × Nat × Option Nat × Option Nat × Option Nat)
 | .consumed _ _ _ r => do
    let d ← r.run.before.dev
    let final ← r.run.after.dev
    let key ← d.keypairs[r.packet.keypair]?
    let beforePeer ← d.peers[r.peer]?
    let afterPeer ← final.peers[r.peer]?
    return (d.ifindex,r.packet.keypair,key.internalId,
      beforePeer.keypairNext,afterPeer.keypairNext,afterPeer.keypairCurrent)
 | _ => none

def readOrFail {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok x => pure x
  | .error e => throw (IO.userError e)

def require (condition : Bool) (message : String) : IO Unit :=
  if condition then pure () else throw (IO.userError message)

def decisionPositions (output : Json) (label : String) : IO (Array Nat) := do
  let branches ← readOrFail (output.getObjVal? "branches" >>= Json.getArr?)
  let mut positions := #[]
  for branch in branches do
    let found ← readOrFail (branch.getObjValAs? String "label")
    if found == label then
      positions := positions.push (← readOrFail (branch.getObjValAs? Nat "index"))
  return positions

def operationRet (output : Json) (index : Nat) : IO Int := do
  let observations ← readOrFail (output.getObjVal? "observations" >>= Json.getArr?)
  let some observation := observations[index]? |
    throw (IO.userError s!"missing operation {index}")
  readOrFail (observation.getObjValAs? Int "ret")

def witnessTrace (base : Trace) : Trace :=
  {base with
    id := "confirmation_recreation"
    ops := base.ops ++ #[.wgDelete,.wgCreate] ++ base.ops
    steer := base.steer ++ base.steer}

def checkInput (input : String) : IO Unit := do
  let base ← readOrFail (Json.parse input >>= parseTrace)
  require (base.id == "d2_respond_then_data" && base.ops.size == 6)
    "expected the six-operation d2_respond_then_data corpus trace"
  require base.hidden.isNone "this witness uses declared placeholder mode; supplied records require their own schedule"
  let trace := witnessTrace base
  let observed := runPrefixOuter (RxCredits.RunnerAccount.observed trace true) []
  let original := Runner.executeTrace trace true
  let (json,final) ← match observed.1 with
    | .ok value => pure value
    | .error e => throw (IO.userError s!"observed runner stopped: {repr e}")
  let direct ← match original with
    | .ok value => pure value
    | .error e => throw (IO.userError s!"original runner stopped: {repr e}")
  require (json.compress == direct.compress) "original/observed runner outputs differ"
  let allocations := observed.2.filterMap allocationPair
  match allocations with
  | [(0,1),(0,2)] => pure ()
  | _ => throw (IO.userError s!"unexpected committed allocations: {repr allocations}")
  let consumed := observed.2.filter fun
    | .consumed _ _ _ _ => true
    | _ => false
  require (consumed.length == 2) "expected exactly two committed consume receipts"
  let summaries := observed.2.filterMap consumeSummary
  match summaries with
  | [(3,0,1,some 0,none,some 0),(4,0,2,some 0,none,some 0)] => pure ()
  | _ => throw (IO.userError s!"unexpected committed promotion summaries: {repr summaries}")
  let notNew ← decisionPositions json "wg_noise_received_with_keypair.not_new=0"
  let changed ← decisionPositions json "wg_noise_received_with_keypair.changed=0"
  require (notNew == #[3,11] && changed == #[3,11])
    s!"unexpected confirmation decisions: not_new={repr notNew}, changed={repr changed}"
  let deleted ← operationRet json 6
  let created ← operationRet json 7
  require (deleted == 0 && created == 0)
    s!"device lifecycle did not succeed: delete={deleted}, create={created}"
  require (final.wg.keypairCounter == 2) "wrong final allocation frontier"
  require ((final.wg.dev.map fun d => (d.ifindex,d.nextKeypairId)) == some (4,1))
    "wrong final device incarnation or local slot frontier"
  IO.println "PASS (runtime): original initialized runner and observer agree; device deletion/recreation both return 0."
  IO.println s!"Committed (epoch,slot,stamp,before.next,after.next,after.current): {repr summaries}"
  IO.println "Both original confirmation branches pass at operations 3 and 11. Raw slot 0 repeats; allocation stamps 1 and 2 differ."
  IO.println "Scope: accepted placeholder-mode model execution; no Linux-record replay or finite kernel-normalization theorem claimed."

end Leanux.Proofs.WG.Noise.ConfirmationIncarnationWitness

def main : IO Unit := do
  let input ← (← IO.getStdin).readToEnd
  Leanux.Proofs.WG.Noise.ConfirmationIncarnationWitness.checkInput input
