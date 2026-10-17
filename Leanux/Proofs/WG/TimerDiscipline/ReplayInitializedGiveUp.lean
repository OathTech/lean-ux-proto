import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource

/-! A runtime witness from the actual initialized runner, using generated
records rather than a Linux capture. The imported observer has proved exact
erasure, including indexed errors and final guards. The assertions below are
runtime checks, not a kernel-proved closed execution or a universal timer
count theorem. No concrete execution state is reconstructed from a snapshot.
-/
namespace Leanux.Proofs.WG.TimerDiscipline.InitializedGiveUp
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.WG.Progress
open Leanux.Proofs.WG.Campaign2

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def cut (audit : RunnerBoundaryAudit) (index : Nat) : IO RunnerBoundary :=
  match audit.boundaries[index]? with
  | some boundary => pure boundary
  | none => throw (IO.userError s!"missing operation boundary {index}")

private def device (s : Product.Snapshot) : IO Device :=
  match s.wg.device with
  | some d => pure d
  | none => throw (IO.userError "missing configured device")

private def peer (s : Product.Snapshot) : IO Peer :=
  match s.peerAt 0 with
  | some p => pure p
  | none => throw (IO.userError "missing configured peer 0")

private def keypairAllocationOrSessionDecision : Decision → Bool
  | .keypairCreateNoMem | .sessionNotCreatedResponse | .sessionNotConsumedResponse
  | .sessionNoKeypair | .sessionInitiator | .sessionAlive
  | .respSessionBegun | .hsRespSessionBegun => true
  | _ => false

private def tick (i : Nat) : UInt64 := UInt64.ofNat (2^32 - 75000 + 2500 + 1451 * i)

private def coarse (i : Nat) : Int64 := Int64.ofNat ((2500 + 1451 * i) * 4000000)

private def selectedSteps (s : Product.Snapshot) (decision : Decision) : List Step :=
  s.ambient.steps.toList.filter (fun step => step.decision == decision)

private def oneDecision (s : Product.Snapshot) (decision : Decision)
    (outcome : Bool) (context : String) : IO Step := do
  let [step] := selectedSteps s decision
    | throw (IO.userError s!"{context}: expected exactly one {decision.info.label}")
  require (step.outcome == outcome) s!"{context}: wrong {decision.info.label} outcome"
  return step

private def run : IO UInt32 := do
  let trace ← match Json.parse (← (← IO.getStdin).getLine) >>= parseTrace with
    | .error error => throw (IO.userError error)
    | .ok trace => pure trace
  require (trace.id == "c2_initialized_giveup" && trace.ops.size == 23 &&
    trace.hidden.isSome && trace.armRecords && !trace.dstCacheRecords &&
    trace.net && !trace.bare && !trace.foreign && !trace.stepped &&
    trace.seccompPrefill == 0 && trace.steer.isEmpty)
    "expected the generated 23-operation initialized recorded-arm recipe"
  match trace.ops[0]?, trace.ops[1]?, trace.ops[2]? with
  | some (.wgSet _), some .wgUp, some (.wgXmit ..) => pure ()
  | _, _, _ => throw (IO.userError "expected configure, up, initial transmit")
  let original ← match executeTrace trace false with
    | .error (index, stop) => throw (IO.userError s!"original operation {index}: {stop.message}")
    | .ok output => pure output
  let audit ← match executeTraceWithBoundaries trace false with
    | .error (index, stop) => throw (IO.userError s!"audited operation {index}: {stop.message}")
    | .ok audit => pure audit
  require (original.compress == audit.output.compress && audit.boundaries.length == 23 &&
    audit.boundaries.map (·.index) == List.range 23)
    "original/audited JSON or operation boundaries differ"
  for boundary in audit.boundaries do
    let s := boundary.after
    let d ← device s
    let p ← peer s
    require (s.wg.keypairCounter == 0 && d.keypairs.isEmpty &&
      p.keypairPrevious.isNone && p.keypairCurrent.isNone && p.keypairNext.isNone)
      s!"operation {boundary.index}: counter, key store or slots are nonempty"
    require (!(s.ambient.steps.any (fun step => keypairAllocationOrSessionDecision step.decision)))
      s!"operation {boundary.index}: keypair allocation or session-begin decision occurred"
    require (s.ambient.hidden == some [] && s.ambient.suspended.isEmpty && !s.wg.netRxRaised &&
      s.ambient.armRecords && !s.ambient.hiddenPlaceholders)
      s!"operation {boundary.index}: final records, suspended activation or mode differs"
    require (boundary.result == (if boundary.index == 2 then 17 else 0))
      s!"operation {boundary.index}: syscall result differs"
  let first := (← cut audit 2).after
  let firstDevice ← device first
  let firstPeer ← peer first
  require (MAX_TIMER_HANDSHAKES == 18 && firstDevice.peers.size == 1 &&
    firstPeer.timerHandshakeAttempts == 0 && firstPeer.staged.length == 1 &&
    firstPeer.persistentKeepaliveInterval == 0 &&
    firstPeer.handshakeState == HANDSHAKE_CREATED_INITIATION &&
    firstPeer.timer .retransmitHandshake == some (tick 0 + 1250) &&
    (firstPeer.wheel .retransmitHandshake).isSome &&
    (firstPeer.timer .zeroKeyMaterial).isNone &&
    (firstPeer.wheel .zeroKeyMaterial).isNone &&
    first.wg.timerEnqueues == 1 && !firstPeer.handshakePending &&
    firstDevice.sendWorkQueue.isEmpty && first.fixture.listenerV4.length == 1 &&
    first.fixture.listenerV4.all (fun packet => packet.2.length == 148 && messageType packet.2 == 1))
    "initial send did not create the expected partial exchange and first retry timer"
  discard <| oneDecision first .initCreated true "initial send"
  let mut summary : List Json := []
  for i in [1:21] do
    match trace.ops[i + 2]? with
    | some (.wgAdvance 1450) => pure ()
    | _ => throw (IO.userError s!"retry {i}: expected advance by 1450 ticks")
    let before := (← cut audit (i + 1)).after
    let after := (← cut audit (i + 2)).after
    let pb ← peer before
    let pa ← peer after
    let da ← device after
    require (pb.internalId == firstPeer.internalId && pa.internalId == firstPeer.internalId &&
      pb.refcount == firstPeer.refcount && pa.refcount == firstPeer.refcount &&
      pb.timerHandshakeAttempts == i - 1 && pa.timerHandshakeAttempts == min i 19 &&
      pa.handshakeState == HANDSHAKE_CREATED_INITIATION &&
      da.ifindex == firstDevice.ifindex && da.peers.size == 1 &&
      !pa.handshakePending && da.sendWorkQueue.isEmpty && da.clearWorkQueue.isEmpty &&
      after.wg.timerEnqueues == before.wg.timerEnqueues + 1 &&
      after.wg.jiffiesLast == some (tick i + 1) &&
      after.ambient.fired.toList == [Worker.timerRetransmit.symbol])
      s!"retry {i}: identity, attempts, mode, timer enqueue or queue endpoint differs"
    let guard ← oneDecision after .retransmitGiveUp (i == 20) s!"retry {i}"
    require (guard.operands == some (Int.ofNat (i - 1), 18))
      s!"retry {i}: give-up operands differ"
    if i < 20 then
      discard <| oneDecision after .initCreated true s!"retry {i}"
      let sent := after.fixture.listenerV4.drop before.fixture.listenerV4.length
      let [packet] := sent | throw (IO.userError s!"retry {i}: expected one new initiation")
      require (after.fixture.listenerV4 == before.fixture.listenerV4 ++ [packet] &&
        packet.2.length == 148 && messageType packet.2 == 1 &&
        !(before.fixture.listenerV4.any (·.2 == packet.2)) &&
        after.fixture.listenerV4.length == i + 1 && pa.staged.length == 1 &&
        pa.lastSentHandshake == coarse i &&
        pa.timer .retransmitHandshake == some (tick i + 1250) &&
        (pa.wheel .retransmitHandshake).isSome &&
        (pa.timer .zeroKeyMaterial).isNone && (pa.wheel .zeroKeyMaterial).isNone)
        s!"retry {i}: fresh initiation, retry rearm or partial-exchange endpoint differs"
    else
      discard <| oneDecision after .retransmitZeroKeyNotPending true "give-up"
      require ((selectedSteps after .initCreated).isEmpty && pa.staged.isEmpty &&
        (pa.timer .retransmitHandshake).isNone && (pa.wheel .retransmitHandshake).isNone &&
        pa.timer .zeroKeyMaterial == some (tick i + ZERO_KEY_MATERIAL_TICKS.toUInt64) &&
        (pa.wheel .zeroKeyMaterial).isSome &&
        (pa.wheel .zeroKeyMaterial).map (·.enqueued) == some after.wg.timerEnqueues &&
        after.wg.timerEnqueues == 21 &&
        after.fixture.listenerV4 == before.fixture.listenerV4 &&
        after.fixture.listenerV4.length == 20 && da.txDropped == 1 &&
        da.txPackets == 20 && da.txBytes == 2960)
        "give-up did not purge, stop retries and enqueue zero-key without a session"
    summary := summary ++ [Json.mkObj [("callback", toJson i),
      ("attempts_after", toJson pa.timerHandshakeAttempts),
      ("keypair_counter", toJson after.wg.keypairCounter),
      ("timer_enqueues", toJson after.wg.timerEnqueues),
      ("initiations", toJson after.fixture.listenerV4.length)]]
  (← IO.getStdout).putStrLn (Json.mkObj [
    ("id", toJson trace.id), ("accepted", toJson true),
    ("original_audit_equal", toJson true), ("boundaries", toJson audit.boundaries.length),
    ("record_origin", toJson "generated clocks, draws, dispatch and wheel records; not a Linux capture"),
    ("validation", toJson "runtime assertions over actual initialized runner; not a kernel-proved closed trace"),
    ("retry_callbacks", toJson (19 : Nat)), ("give_up_callback", toJson (20 : Nat)),
    ("keypair_counter_at_every_boundary", toJson (0 : Nat)),
    ("keypair_allocation_or_session_decisions", toJson (0 : Nat)),
    ("zero_key_enqueued_on_give_up", toJson true), ("episode", toJson summary)]).compress
  return 0

end Leanux.Proofs.WG.TimerDiscipline.InitializedGiveUp

def main : IO UInt32 := Leanux.Proofs.WG.TimerDiscipline.InitializedGiveUp.run
