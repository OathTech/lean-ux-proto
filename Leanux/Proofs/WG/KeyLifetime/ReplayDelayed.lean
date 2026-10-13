import Leanux.Proofs.Logged.Checkpoints
import Leanux.Proofs.Logged.Advance

/-! A generated record stream admits a packet before expiry and encrypts it
after a later original guard records expiry. Coarse time and jiffies are
constructed coherently, with explicit arm records; no Linux capture is claimed.
The optional second variant also runs the original zero timer and clear worker
before encryption, retaining only the queued packet's key reference. -/
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged

private def require (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def device (w : World) : IO Device :=
  match w.k.wg with
  | some d => pure d
  | none => throw (IO.userError "missing witness device")

private def peer0 (d : Device) : IO Peer :=
  match d.peers[0]? with
  | some p => pure p
  | none => throw (IO.userError "missing witness peer")

def main : IO UInt32 := do
  let trace ← match Json.parse (← (← IO.getStdin).getLine) >>= parseTrace with
    | .error e => throw (IO.userError e)
    | .ok t => pure t
  let clears := trace.id == "r5_coherent_post_clear"
  require ((trace.id == "r5_delayed_encryption" || clears) && trace.ops.size == 7 &&
    trace.hidden.isSome && trace.armRecords && !trace.dstCacheRecords)
    "expected seven-operation generated delayed-encryption input with arm records"
  let original ← match executeTrace trace false with
    | .error (i, e) => throw (IO.userError s!"original operation {i}: {e.message}")
    | .ok j => pure j
  let (observed, checkpoints) ← match
      (executeTraceCheckpoints (fun _ w => w) trace false).run [] with
    | .error (i, e) => throw (IO.userError s!"checkpoint operation {i}: {e.message}")
    | .ok r => pure r
  require (original.compress == observed.compress && checkpoints.length == 7)
    "original/checkpoint JSON or checkpoint count differs"
  let some before := checkpoints[5]? | throw (IO.userError "missing receive checkpoint")
  let initial ← device before
  let peer ← peer0 initial
  let some slot := peer.keypairCurrent | throw (IO.userError "no current keypair")
  let some key := initial.keypairs[slot]? | throw (IO.userError "no current material")
  require (peer.timerNeedAnotherKeepalive && key.sending.isValid &&
    key.sending.birthdate == 132000000000 && key.sendingCounter == 1 && key.refcount == 1)
    "two nonempty receives did not establish the expected key/timer state"
  let entry := { before with
    hidden := trace.hidden.map (·[6]!)
    netRxRaised := false }
  let jEnd : UInt64 := if clears then 4295060796 else 4294973046
  let (result, units) := runPrefix (advanceSyscallObserved 44250) entry []
  let (ret, final) ← match result with
    | .error e => throw (IO.userError s!"observed advance syscall: {e.message}")
    | .ok r => pure r
  require (ret == 0 && !units.isEmpty) "advance failed or no timer fired"
  let expectedUnits := if clears then
      [some .timerSendKeepalive, some .timerSendKeepalive, some .timerZeroKey,
       some .clearPeerWorker, none, some .sendWorker, none]
    else [some .timerSendKeepalive, some .timerSendKeepalive, none, some .sendWorker, none]
  require (units.map (·.worker) == expectedUnits)
    "unexpected completed timer/scheduler unit order"
  let some admitted := units[0]? | throw (IO.userError "missing first callback")
  let da ← device admitted.execution.after
  let pa ← peer0 da
  let [(packetId, packet)] := da.txSkbs.toList
    | throw (IO.userError "first callback did not allocate exactly one packet")
  require (packet.keypair == slot && packet.peer == 0 && packet.nonce == 1 &&
    packet.plaintext.bytes.isEmpty && da.encryptQueue.count == 1 &&
    !pa.timerNeedAnotherKeepalive && pa.timer .sendKeepalive == some 4294972546)
    "first callback did not stage nonce one and rearm at 321 seconds"
  let some expired := units[1]? | throw (IO.userError "missing second callback")
  let de ← device expired.execution.after
  let pe ← peer0 de
  let some retained := de.keypairs[slot]? | throw (IO.userError "key disappeared before encryption")
  let expectedRetained := {key with
    sendingCounter := 2
    refcount := 2
    sending := {key.sending with isValid := false}}
  require (retained == expectedRetained &&
    pe.handshakePending && pe.staged.length == 1 && de.encryptQueue.count == 1 &&
    de.txSkbs[packetId]? == some packet)
    "second callback did not invalidate the same resident material and retain the first packet"
  let materialBoundary ← if clears then do
      let some cleared := units[3]? | throw (IO.userError "missing clear worker")
      let d ← device cleared.execution.after
      let p ← peer0 d
      require (p.keypairCurrent.isNone && p.keypairNext.isNone && p.keypairPrevious.isNone &&
        p.handshakeState == 0 && !d.indexTable.any (·.keypair == some slot) &&
        d.keypairs[slot]? == some {retained with refcount := 1} &&
        d.txSkbs[packetId]? == some packet) "clear did not retain exactly the packet-held material"
      pure cleared.execution.after
    else pure expired.execution.after
  let some crypt := units[if clears then 4 else 2]?
    | throw (IO.userError "missing encryption scheduler call")
  require (crypt.execution.before.k == materialBoundary.k)
    "kernel changed between the observed material boundary and encryption scheduler entry"
  let expected := dataMessage retained.remoteIndex packet.nonce retained.sending.key []
  require (!(crypt.execution.before.senderInbox.any (·.bytes == expected)) &&
    crypt.execution.after.senderInbox.any (·.bytes == expected))
    "old material did not produce the expected ciphertext after recorded expiry"
  let dc ← device crypt.execution.after
  let pc ← peer0 dc
  require ((if clears then dc.keypairs[slot]?.isNone
      else dc.keypairs[slot]? == some {retained with refcount := 1}) &&
    dc.txSkbs[packetId]?.isNone && pc.handshakePending &&
    pc.handshakeState == (if clears then 0 else pe.handshakeState))
    "transmission did not release its packet/reference before the queued handshake"
  require (final.hidden == some []) "observed advance left unconsumed records"
  let some last := checkpoints[6]? | throw (IO.userError "missing final checkpoint")
  require (last.k == final.k && last.steps == final.steps && last.senderInbox == final.senderInbox &&
    last.jiffiesLast == final.jiffiesLast && last.jiffiesLast == some jEnd && last.hidden == some [])
    "observed timer endpoint disagrees with original runner"
  let branches ← match original.getObjValAs? (Array Json) "branches" with
    | .error e => throw (IO.userError e)
    | .ok bs => pure bs
  let labels := ["wg_packet_send_staged_packets.birthdate_expired=0",
    "wg_packet_send_staged_packets.birthdate_expired=1",
    "wg_packet_encrypt_worker.encrypted=1", "wg_packet_create_data_done.sent=1"]
  let selected := branches.toList.filter fun b =>
    (b.getObjValAs? Nat "index").toOption == some 6 &&
    labels.contains ((b.getObjValAs? String "label").toOption.getD "")
  require (selected.map (fun b => (b.getObjValAs? String "label").toOption.getD "") == labels)
    "source branch order differs from admission, expiry, encryption and transmission"
  require ((selected[0]!.getObjValAs? (List Int) "operands").toOption ==
      some [312000000000, 311000000000] &&
    (selected[1]!.getObjValAs? (List Int) "operands").toOption ==
      some [312000000000, if clears then 673000000000 else 322000000000]) "unexpected recorded age operands"
  (← IO.getStdout).putStrLn (Json.mkObj [("id", toJson trace.id),
    ("accepted", toJson true), ("original_json_matches", toJson true),
    ("wire_nonce", toJson packet.nonce), ("lifetime", toJson retained.internalId),
    ("clear_before_encryption", toJson clears),
    ("ciphertext", toJson (hexBytesOf (ByteArray.mk expected.toArray))),
    ("record_origin", toJson "generated coherent coarse/jiffies values and timer arms; not a Linux capture"),
    ("finding", toJson (if clears then "packet-held material encrypts after recorded expiry, zero timer and clear worker, before the queued handshake" else "admitted packet encrypts under unchanged material after a later recorded age rejection")),
    ("branches", toJson selected)]).compress
  return 0
