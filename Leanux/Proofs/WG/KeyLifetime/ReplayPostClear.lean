import Leanux.Proofs.Logged.Checkpoints
import Leanux.Proofs.Logged.TimerPass

/-! An accepted synthetic record stream uses a packet-held keypair after the
clear worker. Its jiffies and coarse clocks are deliberately incoherent, and
arm records are disabled: this is a runner-domain witness, not a Linux capture.
The exact timer-pass observer also inspects the internal retained reference. -/
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged

private def require (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def getDevice (w : World) : IO Device :=
  match w.k.wg with
  | some d => pure d
  | none => throw (IO.userError "missing witness device")

private def getPeer0 (d : Device) : IO Peer :=
  match d.peers[0]? with
  | some p => pure p
  | none => throw (IO.userError "missing witness peer")

def main : IO UInt32 := do
  let input ← IO.getStdin
  let trace ← match Json.parse (← input.getLine) >>= parseTrace with
    | .error message => throw (IO.userError message)
    | .ok t => pure t
  require (trace.id == "r5_post_clear_transport" && trace.ops.size == 5 &&
    trace.hidden.isSome && !trace.armRecords && !trace.dstCacheRecords)
    "expected five-operation synthetic post-clear witness in legacy record mode"
  let original ← match executeTrace trace false with
    | .error (i, e) => throw (IO.userError s!"original operation {i}: {e.message}")
    | .ok j => pure j
  let (observed, checkpoints) ← match
      (executeTraceCheckpoints (fun _ w => w) trace false).run [] with
    | .error (i, e) => throw (IO.userError s!"checkpoint operation {i}: {e.message}")
    | .ok r => pure r
  require (original.compress == observed.compress && checkpoints.length == 5)
    "original/checkpoint JSON or checkpoint count differs"
  let some before := checkpoints[3]? | throw (IO.userError "missing session checkpoint")
  let initial ← getDevice before
  let peer ← getPeer0 initial
  let some slot := peer.keypairCurrent | throw (IO.userError "no current session")
  let some key := initial.keypairs[slot]? | throw (IO.userError "no session keypair")
  require (key.internalId == 1 && key.refcount == 1 && key.sendingCounter == 1)
    "unexpected initial keypair identity/reference/nonce"
  -- Runner's operation setup followed by syscall's literal reset. The
  -- intervening disabled-seccomp getter and idleTimers' peek do not modify it.
  let entry := { before with
    hidden := trace.hidden.map (·[4]!)
    netRxRaised := false
    steps := #[]
    userOut := none
    userFds := none
    extraOut := []
    queuedThisCall := []
    fired := #[]
    netRxSections := 0
    netRxSection := 0
    emitted := {}
    translatedLen := none }
  let (result, units) := runPrefix (timerPassObserved 135005) entry []
  let (fired, final) ← match result with
    | .error e => throw (IO.userError s!"observed timer pass: {e.message}")
    | .ok r => pure r
  require fired "timer pass did not fire"
  require (units.map (·.worker) == [some .timerPersistentKeepalive, some .timerZeroKey,
      some .clearPeerWorker, none, none]) "unexpected completed timer/scheduler unit order"
  let some cleared := units[2]? | throw (IO.userError "missing clear completion")
  let dc ← getDevice cleared.execution.after
  let pc ← getPeer0 dc
  let some retained := dc.keypairs[slot]? | throw (IO.userError "packet-held keypair was lost")
  require (pc.keypairCurrent.isNone && pc.keypairNext.isNone && pc.keypairPrevious.isNone &&
    pc.handshakeState == 0 && !dc.indexTable.any (·.keypair == some slot))
    "clear did not remove peer slots, handshake state and keypair index"
  require (retained == {key with sendingCounter := 2})
    "clear did not retain exactly the same key material and one packet reference"
  let [(packetId, packet)] := dc.txSkbs.toList
    | throw (IO.userError "expected exactly one allocated transmit packet after clear")
  require (packet.keypair == slot && packet.peer == 0 && packet.nonce == 1 &&
    packet.plaintext.bytes.isEmpty && dc.encryptQueue.count == 1)
    "unexpected packet awaiting encryption after clear"
  let some crypt := units[3]? | throw (IO.userError "missing crypt scheduler call")
  require (crypt.execution.before.k == cleared.execution.after.k)
    "kernel state changed between clear completion and crypt scheduler entry"
  let expected := dataMessage retained.remoteIndex packet.nonce retained.sending.key []
  require (!(crypt.execution.before.senderInbox.any (·.bytes == expected)) &&
    crypt.execution.after.senderInbox.any (·.bytes == expected))
    "crypt scheduler did not transmit the ciphertext under the retained key"
  let afterCrypt ← getDevice crypt.execution.after
  require (afterCrypt.keypairs[slot]?.isNone && afterCrypt.txSkbs[packetId]?.isNone)
    "transmission did not release the retained keypair and packet"
  require (final.hidden.map (List.map (·.site)) == some [128])
    "timer pass left records other than its caller's end-of-wait word"
  let some last := checkpoints[4]? | throw (IO.userError "missing final runner checkpoint")
  require (last.k == final.k && last.jiffiesLast == some 135005 && last.hidden == some [])
    "timer-pass endpoint disagrees with the accepted runner checkpoint"
  let branches ← match original.getObjValAs? (Array Json) "branches" with
    | .error e => throw (IO.userError e)
    | .ok bs => pure bs
  let labels := ["wg_expired_zero_key_material.alive=1",
    "wg_noise_keypair_put.unreference_now=1", "wg_noise_keypair_put.kref_put_released=0",
    "wg_packet_encrypt_worker.encrypted=1", "wg_packet_create_data_done.sent=1",
    "wg_noise_keypair_put.unreference_now=0", "wg_noise_keypair_put.kref_put_released=1"]
  let selected := branches.toList.filter fun b =>
    (b.getObjValAs? Nat "index").toOption == some 4 &&
    labels.contains ((b.getObjValAs? String "label").toOption.getD "")
  require (selected.map (fun b => (b.getObjValAs? String "label").toOption.getD "") == labels)
    "original branch order does not establish clear before encryption and final release"
  (← IO.getStdout).putStrLn (Json.mkObj [("id", toJson trace.id), ("accepted", toJson true),
    ("original_json_matches", toJson true), ("lifetime", toJson retained.internalId),
    ("held_references_after_clear", toJson retained.refcount), ("wire_nonce", toJson packet.nonce),
    ("ciphertext", toJson (hexBytesOf (ByteArray.mk expected.toArray))),
    ("record_origin", toJson "synthetic; incoherent coarse/jiffies clocks; no arm records"),
    ("finding", toJson "packet-held material is used after clear in an accepted mirror input; no Linux execution claimed"),
    ("branches", toJson selected)]).compress
  return 0
