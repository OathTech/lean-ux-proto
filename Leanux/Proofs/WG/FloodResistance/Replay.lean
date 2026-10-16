import Leanux.Proofs.Logged.Checkpoints
import Leanux.Proofs.Logged.Advance

/-! A generated reset-free retry episode, not a Linux capture. Original
checkpoints and exact timer-unit observations distinguish callback counts,
counter values, new initiation transmissions and the eventual give-up arm.
The C and mirror both use `attempts > MAX_TIMER_HANDSHAKES`; C's diagnostic
reports `MAX_TIMER_HANDSHAKES + 2` (timers.c:49). -/
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged

/-- The original 43 store fields, excluding the former outer output fields.
This is a pure observation of the product, not an execution state. -/
private def store43 (w : World) :=
  ({ w.fs with userOut := none, userFds := none }, w.tasks,
    w.seccomp.filters, w.seccomp.nextFilter, w.wg.dev, w.wg.nlSock7, w.wg.nlSock8,
    w.wg.peerCounter, w.wg.keypairCounter, w.wg.netIfindexNext, w.wg.ratelimiter)

private def require (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def device (w : World) : IO Device :=
  match w.wg.dev with
  | some d => pure d
  | none => throw (IO.userError "missing retry device")

private def peer0 (w : World) : IO Peer := do
  let d ← device w
  match d.peers[0]? with
  | some p => pure p
  | none => throw (IO.userError "missing retry peer")

private def tick (i : Nat) : UInt64 := UInt64.ofNat (4294892296 + 2500 + 1451 * i)
private def coarse (i : Nat) : Int64 := Int64.ofNat ((2500 + 1451 * i) * 4000000)

private def checkpoint (ws : List World) (i : Nat) : IO World :=
  match ws[i]? with
  | some w => pure w
  | none => throw (IO.userError s!"missing checkpoint {i}")

def main : IO UInt32 := do
  let trace ← match Json.parse (← (← IO.getStdin).getLine) >>= parseTrace with
    | .error e => throw (IO.userError e)
    | .ok t => pure t
  require (trace.id == "r6_retransmit_limit" && trace.ops.size == 23 &&
    trace.hidden.isSome && trace.armRecords && !trace.dstCacheRecords)
    "expected 23-operation generated retry episode with explicit arms"
  let original ← match executeTrace trace false with
    | .error (i, e) => throw (IO.userError s!"original operation {i}: {e.message}")
    | .ok j => pure j
  let (observed, checkpoints) ← match
      (executeTraceCheckpoints (fun _ w => w) trace false).run [] with
    | .error (i, e) => throw (IO.userError s!"checkpoint operation {i}: {e.message}")
    | .ok r => pure r
  require (original.compress == observed.compress && checkpoints.length == 23)
    "original/checkpoint JSON or checkpoint count differs"
  let initial ← checkpoint checkpoints 2
  let d0 ← device initial
  let p0 ← peer0 initial
  require (MAX_TIMER_HANDSHAKES == 18 && d0.peers.size == 1 && d0.keypairs.isEmpty &&
    p0.timerHandshakeAttempts == 0 && p0.staged.length == 1 &&
    p0.persistentKeepaliveInterval == 0 && p0.timer .retransmitHandshake == some (tick 0 + 1250) &&
    p0.timer .zeroKeyMaterial == none && !p0.handshakePending && d0.sendWorkQueue.isEmpty &&
    initial.fixture.listenerV4.length == 1 && initial.fixture.listenerV4.all (fun p => p.2.length == 148 && messageType p.2 == 1))
    "initial send did not establish one initiation, a staged packet and retry counter zero"
  let observations ← match original.getObjValAs? (Array Json) "observations" with
    | .error e => throw (IO.userError e)
    | .ok xs => pure xs
  require ((observations[2]!.getObjValAs? Int "ret").toOption == some 17)
    "initial application transmit did not accept its 17-byte payload"
  let mut results : List Json := []
  for i in [1:21] do
    let before ← checkpoint checkpoints (i + 1)
    let after ← checkpoint checkpoints (i + 2)
    let pb ← peer0 before
    let pa ← peer0 after
    let da ← device after
    require (pb.internalId == p0.internalId && pa.internalId == p0.internalId &&
      pb.timerHandshakeAttempts == i - 1 && pa.timerHandshakeAttempts == min i 19 &&
      da.ifindex == d0.ifindex && da.keypairs.isEmpty && da.sendWorkQueue.isEmpty && !pa.handshakePending)
      s!"callback {i}: identity, attempts, or queue endpoint differs"
    match trace.ops[i + 2]? with
    | some (.wgAdvance 1450) => pure ()
    | _ => throw (IO.userError s!"callback {i}: expected original advance")
    let entry := { before with
      ambient := { before.ambient with hidden := trace.hidden.map (·[i + 2]!) }
      fixture := { before.fixture with hiddenAhead := trace.hidden.map (fun h => (h.drop (i + 3)).toList) }
      wg := { before.wg with netRxRaised := false } }
    let (result, units) := runPrefix (advanceSyscallObserved 1450) entry []
    let (ret, final) ← match result with
      | .error e => throw (IO.userError s!"callback {i}: observed advance syscall: {e.message}")
      | .ok r => pure r
    let expectedUnits := if i < 20 then [some .timerRetransmit, some .sendWorker, none]
      else [some .timerRetransmit, none]
    require (ret == 0 && units.map (·.worker) == expectedUnits &&
      final.ambient.hidden == some [] && after.ambient.hidden == some [] &&
      store43 after == store43 final && after.fixture.listenerV4 == final.fixture.listenerV4 && after.fixture.senderInbox == final.fixture.senderInbox &&
      after.ambient.steps == final.ambient.steps && after.wg.jiffiesLast == final.wg.jiffiesLast &&
      after.wg.jiffiesLast == some (tick i + 1) && after.ambient.fired == final.ambient.fired &&
      after.ambient.fired.toList == [Worker.timerRetransmit.symbol])
      s!"callback {i}: exact timer units or original checkpoint endpoint differs"
    let some callback := units[0]? | throw (IO.userError "missing retransmit callback")
    let pc ← peer0 callback.execution.after
    let dc ← device callback.execution.after
    require (pc.internalId == p0.internalId && pc.timerHandshakeAttempts == min i 19 &&
      pc.timer .retransmitHandshake == none &&
      callback.execution.after.fixture.listenerV4 == before.fixture.listenerV4 &&
      callback.execution.after.fixture.senderInbox == before.fixture.senderInbox)
      s!"callback {i}: detached timer, counter or transmission boundary differs"
    let branchName := "wg_expired_retransmit_handshake.give_up=" ++ (if i < 20 then "0" else "1")
    let guards := after.ambient.steps.toList.filter (fun s => s.label.startsWith "wg_expired_retransmit_handshake.give_up=")
    let [guard] := guards | throw (IO.userError s!"callback {i}: expected one give-up comparison")
    require (guard.label == branchName &&
      guard.operands == some (Int.ofNat (i - 1), 18))
      s!"callback {i}: original give-up comparison or operands differ"
    if i < 20 then
      require (pc.handshakePending && dc.sendWorkQueue == [0] && pc.staged.length == 1)
        s!"callback {i}: retry did not queue exactly its send worker"
      let some worker := units[1]? | throw (IO.userError "missing send worker")
      let pw ← peer0 worker.execution.after
      let sent := worker.execution.after.wg.sent.drop worker.execution.before.wg.sent.length
      let [packet] := sent | throw (IO.userError s!"callback {i}: expected one new transmission")
      require (worker.execution.after.wg.sent == worker.execution.before.wg.sent ++ sent &&
        packet.bytes.length == 148 && messageType packet.bytes == 1 &&
        !(before.fixture.listenerV4.any (·.2 == packet.bytes)) &&
        after.fixture.listenerV4 == before.fixture.listenerV4 ++ [(packet.ds, packet.bytes)] &&
        pw.timerHandshakeAttempts == i && pw.timer .retransmitHandshake == some (tick i + 1250) &&
        pw.lastSentHandshake == coarse i && !pw.handshakePending &&
        pa.staged.length == 1 && after.fixture.listenerV4.length == i + 1)
        s!"callback {i}: original worker did not transmit and rearm this retry"
    else
      require (!pc.handshakePending && dc.sendWorkQueue.isEmpty && pc.staged.isEmpty &&
        pa.timer .retransmitHandshake == none && pa.timer .zeroKeyMaterial == some (tick i + 135000) &&
        after.fixture.listenerV4 == before.fixture.listenerV4 && after.fixture.listenerV4.length == 20 &&
        da.txDropped == 1 && da.txPackets == 20 && da.txBytes == 2960)
        "give-up did not stop retries, purge the staged packet and arm deferred clearance"
    results := results ++ [Json.mkObj [("callback", toJson i),
      ("comparison", toJson [i - 1, MAX_TIMER_HANDSHAKES]),
      ("attempts_after", toJson pa.timerHandshakeAttempts),
      ("initiations_sent", toJson after.fixture.listenerV4.length),
      ("rearmed", toJson (pa.timer .retransmitHandshake).isSome)]]
  (← IO.getStdout).putStrLn (Json.mkObj [("id", toJson trace.id),
    ("accepted", toJson true), ("original_json_matches", toJson true),
    ("record_origin", toJson "generated explicit coherent coarse/jiffies clocks and timer arms; not a Linux capture"),
    ("max_timer_handshakes", toJson MAX_TIMER_HANDSHAKES),
    ("retry_callbacks", toJson (19 : Nat)), ("total_initiations", toJson (20 : Nat)),
    ("give_up_callback", toJson (20 : Nat)), ("episode", toJson results)]).compress
  return 0
