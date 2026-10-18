import Leanux.Proofs.WG.AuthenticatedEffects.TimerRootSource
import Leanux.Proofs.WG.Lifetimes.TxStaging

/-! Actual deferred-work creation inside the response receiver's keepalive.
Queue writes and createData calls retain their own native execution receipts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources TimerRoot
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def enqueue (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) : WGPrefix Event Unit :=
  receiptWGObserved
    (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))
    (fun r => .queued ⟨origin,kind,pid,r⟩)

def submit (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (items : List SkbId) : WGPrefix Event Unit :=
  receiptWGObserved (liftWGPrefix (createData pid items)) (fun r => .submitted ⟨origin,kind,pid,items,r⟩)

def queued (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (retry : Bool) : WGPrefix Event Unit := do
  if ← liftWGPrefix (branch .queuedNotRetry !retry) then
    liftWGPrefix (setPeer pid { (← liftWGPrefix (getPeer pid)) with timerHandshakeAttempts := 0 })
  let p ← liftWGPrefix (getPeer pid)
  if ← liftWGPrefix (branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·)) then return
  if ← liftWGPrefix (branch .queuedDead p.isDead) then return
  liftWGPrefix (peerGet pid)
  if ← liftWGPrefix (branch .queuedAlreadyQueued (p.handshakePending && !(← liftWGPrefix (peekQueuedUnit .sendWorker pid)))) then
    liftWGPrefix (peerPut (some pid))
    return
  liftWGPrefix (setPeer pid {(← liftWGPrefix (getPeer pid)) with handshakePending := true})
  liftWGPrefix (recordQueued .sendWorker pid)
  enqueue origin kind pid

def noKey (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) : WGPrefix Event Unit := do
  if invalid then
    let some id := keypair | liftWGPrefix (invariant "unreachable")
    let k ← liftWGPrefix (getKeypair id)
    liftWGPrefix (setKeypair id {k with sending := {k.sending with isValid := false}})
  liftWGPrefix (keypairPut keypair false)
  for _ in packets do _ ← liftWGPrefix (branch .stagedOrphanWalk true)
  _ ← liftWGPrefix (branch .stagedOrphanWalk false)
  liftWGPrefix (setPeer pid {(← liftWGPrefix (getPeer pid)) with
    staged := packets ++ (← liftWGPrefix (getPeer pid)).staged})
  queued origin kind pid false

def key (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) (id : KeypairId)
    (packets : List Packet) : WGPrefix Event Unit := do
  let k ← liftWGPrefix (getKeypair id)
  if ← liftWGPrefix (branch .stagedKeyInvalid !k.sending.isValid) then
    return ← noKey origin kind pid packets (some id) false
  if ← liftWGPrefix (branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME) then
    return ← noKey origin kind pid packets (some id) true
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← liftWGPrefix (branch .stagedNonceIterate true)
    let ds ← liftWGPrefix (ipTunnelEcnEncap pkt)
    let k ← liftWGPrefix (getKeypair id)
    let nonce := k.sendingCounter
    liftWGPrefix (setKeypair id {k with sendingCounter := k.sendingCounter + 1})
    if ← liftWGPrefix (branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES) then
      return ← noKey origin kind pid packets (some id) true
    packetsCb := packetsCb ++ [{peer := pid,keypair := id,nonce,plaintext := pkt,ds}]
  _ ← liftWGPrefix (branch .stagedNonceIterate false)
  liftWGPrefix (peerGet (← liftWGPrefix (IndexOwner.peerDeref (.keypair id))))
  let items ← liftWGPrefix (packetsCb.mapM newTxSkb)
  submit origin kind pid items

def staging (origin : Nat) (kind : HandshakeCausal.Kind) (pid : PeerId) : WGPrefix Event Unit := do
  let p ← liftWGPrefix (getPeer pid)
  if ← liftWGPrefix (branch .stagedEmpty p.staged.isEmpty) then return
  liftWGPrefix (setPeer pid {p with staged := []})
  let kp ← liftWGPrefix (keypairGet p.keypairCurrent)
  if ← liftWGPrefix (branch .stagedNoKeypair kp.isNone) then
    return ← noKey origin kind pid p.staged kp false
  let some id := kp | liftWGPrefix (invariant "unreachable")
  key origin kind pid id p.staged

def keepalive (origin : Nat) (pid : PeerId) : WGPrefix Event Unit := do
  let p ← liftWGPrefix (getPeer pid)
  if ← liftWGPrefix (branch .keepaliveStagedEmpty p.staged.isEmpty) then
    if ← liftWGPrefix (branch .keepaliveNoMem !(← liftWGPrefix (hiddenAlloc .keepaliveSkb))) then return
    liftWGPrefix (setPeer pid {p with staged := p.staged ++ [{mtu := (← liftWGPrefix getDev).mtu}]})
  staging origin .keepalive pid

def ops (mac : HandshakeMac) : Ops (WGPrefix Event) :=
  { TimerRoot.ops mac with keepalive := fun pid => TimerRoot.call .keepalive pid (fun origin => keepalive origin pid) }

def receive (msg : Key) (src : SkbSource) : WGPrefix Event Unit := do
  if ← liftWGPrefix (branch .hsCookie (messageType msg == MESSAGE_HANDSHAKE_COOKIE)) then
    liftWGPrefix (cookieMessageConsume msg)
    return
  let loaded ← liftWGPrefix Cookies.loadPhase
  let checked ← captureWGRun (cookieValidatePacket msg src loaded)
  afterMacWith (ops ⟨msg,src,loaded,checked⟩) msg src loaded checked.value

end Leanux.Proofs.WG.AuthenticatedEffects.WorkRoot
