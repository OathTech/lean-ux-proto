import Leanux.Proofs.Logged.Checkpoints
import Leanux.Proofs.Logged.Runner
import Leanux.Proofs.WG.Queues.GroState

/-! Generated explicit GRO scheduling witness, not a Linux capture. -/
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues (groTakesAlone groBypassesHeld)

private def require (p : Bool) (message : String) : IO Unit :=
  unless p do throw (IO.userError message)

private def held : List UInt8 :=
  [0x45,0,0,0x29,0,0,0x40,0,0x40,6,0x27,0xcd,10,0,0,2,10,0xff,0xfe,1,
   0x9c,0x41,0,0x50,0,0,0,7,0x55,0x66,0x77,0x88,0x50,0x10,0x20,0,0xcb,0x49,0,0,0x48]
private def normal : List UInt8 :=
  [0x45,0,0,0x28,0,0,0x40,0,0x40,6,0x27,0xce,10,0,0,2,10,0xff,0xfe,1,
   0x9c,0x42,1,0xbb,0x11,0x22,0x33,0x44,0,0,0,0,0x50,2,0x20,0,0x9a,0x7c,0,0]

private def packetHex (bytes : List UInt8) : String := hexBytesOf ⟨bytes.toArray⟩

def main : IO UInt32 := do
  let trace ← match Json.parse (← (← IO.getStdin).getLine) >>= parseTrace with
    | .error e => throw (IO.userError e)
    | .ok t => pure t
  if trace.id != "r4_gro_reorder" || trace.ops.size != 6 || trace.hidden.isNone then
    throw (IO.userError "expected six-operation explicit GRO reorder input")
  let original ← match executeTrace trace false with
    | .error (i, e) => throw (IO.userError s!"original operation {i}: {e.message}")
    | .ok j => pure j
  let (observed, checkpoints) ← match
      (executeTraceCheckpoints (fun _ w => w) trace false).run [] with
    | .error (i, e) => throw (IO.userError s!"checkpoint operation {i}: {e.message}")
    | .ok r => pure r
  require (observed.compress == original.compress && checkpoints.length == 6)
    "original/checkpoint JSON or checkpoint count differs"
  let some before := checkpoints[3]? | throw (IO.userError "missing session checkpoint")
  let some after := checkpoints[4]? | throw (IO.userError "missing batch checkpoint")
  let some d := before.wg.dev | throw (IO.userError "missing initial device")
  let some p := d.peers[0]? | throw (IO.userError "missing initial peer")
  let some slot := p.keypairCurrent | throw (IO.userError "missing current keypair")
  let some key := d.keypairs[slot]? | throw (IO.userError "missing session material")
  let (validated, acceptances) ← match (executeTraceLogged trace false).run [] with
    | .error (i, e) => throw (IO.userError s!"acceptance observer operation {i}: {e.message}")
    | .ok r => pure r
  require (validated.compress == original.compress &&
    acceptances.map (fun e => (e.keypair, e.nonce)) == [(key.internalId, 0), (key.internalId, 1)])
    "original acceptance history is not nonce zero then one under this exact key lifetime"
  require (d.keypairs.size == 1 && key.receivingCounter.counter == 0 &&
    key.sendingCounter == 1 && !groTakesAlone held && groTakesAlone normal &&
    groBypassesHeld held normal &&
    held.length == 41 && normal.length == 40) "unexpected starting nonce or packet classes"
  -- A separate direct GRO call demonstrates why the former helper equation
  -- needs its bypass premise. These bytes are helper inputs, not a capture
  -- or a second accepted runner trace; the original witness below is unchanged.
  let sameFlowNormal := normal.take 20 ++ (held.drop 20).take 4 ++ normal.drop 24
  require (groTakesAlone sameFlowNormal && !groBypassesHeld held sameFlowNormal)
    "same-flow helper input did not select the corrected path"
  let sameFlowCallback (packets : List (List UInt8)) : Leanux.M Unit :=
    if packets == [held, sameFlowNormal] then pure ()
    else unsupported "unexpected same-flow GRO callback order"
  let (sameFlowGro, _) ← match
      ((do let g ← napiGroReceive sameFlowCallback {} held
           let g ← napiGroReceive sameFlowCallback g sameFlowNormal
           napiGroFlushAll sameFlowCallback g
           pure g) : Leanux.M GroState).run before with
    | .error e => throw (IO.userError s!"same-flow GRO helper: {e.message}")
    | .ok r => pure r
  require (sameFlowGro.rxList == [held, sameFlowNormal] && sameFlowGro.held.isEmpty)
    "same-flow refusal did not complete the held segment before the newcomer"
  require (!((sameFlowCallback [sameFlowNormal, held]).run before).isOk)
    "same-flow helper did not distinguish the former normal-then-held claim"
  let expectedH := dataMessage 0x0a0b0c0d 0 key.receiving.key (held ++ List.replicate 7 0)
  let expectedN := dataMessage 0x0a0b0c0d 1 key.receiving.key (normal ++ List.replicate 8 0)
  match trace.ops[4]? with
  | some (Operation.wgBatch [Leanux.Env.BatchItem.inject 4 51820 h, Leanux.Env.BatchItem.inject 4 51820 n] 400) =>
    require (h == expectedH && n == expectedN) "input is not held ACK then distinct-flow SYN under one key"
  | _ => throw (IO.userError "unexpected input operation")
  let replyN := dataMessage key.remoteIndex 1 key.sending.key (Leanux.Env.Stack.rst4 normal ++ List.replicate 8 0)
  let replyH := dataMessage key.remoteIndex 2 key.sending.key (Leanux.Env.Stack.rst4 held ++ List.replicate 8 0)
  require (packetHex replyN == "04000000040302010100000000000000970a5c285c46d27c2a1da800d008a21ed85a87ed00a2e327a015c23d84703a9c90b90ed582a2d4eb8ad7bc6a7ba7bce30401e5603229bcee0dbde30baa1a2fbd" &&
    packetHex replyH == "04000000040302010200000000000000cd72867e65810e61d33daa6cc1a961503c85660d2076aaad546036179974b7674d7ca31bb974acb859d59677921b156bb90c029ea8debd0bf30a69efa55207be")
    "computed reply ciphertexts differ from the reproducible witness"
  require (after.fixture.senderInbox.map (·.bytes) == before.fixture.senderInbox.map (·.bytes) ++ [replyN, replyH])
    "actual output did not append normal SYN RST before held ACK RST"
  let some d' := after.wg.dev | throw (IO.userError "missing final device")
  let some p' := d'.peers[0]? | throw (IO.userError "missing final peer")
  let some key' := d'.keypairs[slot]? | throw (IO.userError "missing final keypair")
  require (p'.internalId == p.internalId && p'.keypairCurrent == some slot &&
    key'.internalId == key.internalId && key'.sendingCounter == 3 &&
    key'.receivingCounter.counter == 2 && d'.rxSkbs.isEmpty)
    "peer/key lifetime, counter progression or receive cleanup differs"
  let observations ← match original.getObjValAs? (Array Json) "observations" with
    | .error e => throw (IO.userError e)
    | .ok xs => pure xs
  let some observation := observations[5]? | throw (IO.userError "missing final observation")
  let replies ← match observation.getObjValAs? (Array (Array Json)) "replies" with
    | .error e => throw (IO.userError e)
    | .ok xs => pure xs
  require (replies.size == 3 && (replies[1]?.bind (·[9]?)) == some (toJson (packetHex replyN)) &&
    (replies[2]?.bind (·[9]?)) == some (toJson (packetHex replyH)))
    "original observable ciphertext rows do not carry the reversed nonce assignment"
  (← IO.getStdout).putStrLn (Json.mkObj [("id", toJson trace.id),
    ("accepted", toJson true), ("original_json_matches", toJson true),
    ("record_origin", toJson "generated explicit inputs; not a Linux capture"),
    ("receive_order", toJson ["held ACK, nonce 0", "normal SYN, nonce 1"]),
    ("reply_order", toJson ["normal SYN RST, nonce 1", "held ACK RST, nonce 2"]),
    ("same_flow_helper_order", toJson ["held ACK", "same-flow SYN"]),
    ("ciphertexts", toJson [packetHex replyN, packetHex replyH])]).compress
  return 0
