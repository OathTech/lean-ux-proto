import Leanux.Proofs.WG.AuthenticatedEffects.CausalEffects
import Leanux.Proofs.WG.Queues.RxConsumeProtection

/-! Native packet-side maintenance with timer creation and handshake queue
append exposed through the same effect callbacks as timer and handshake work. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.PacketEffects
open Leanux Leanux.WG Leanux.Proofs.Logged TimerEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

def freshSendWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  let current := (← o.step (getPeer pid)).keypairCurrent
  let send ← o.step (WG.andM (branch .freshKeypair current.isSome) do
    let some id := current | invariant "unreachable"
    let k ← getKeypair id
    WG.andM (branch .freshValid k.sending.isValid) do
      WG.orM (branchCmp .freshCounter (k.sendingCounter > REKEY_AFTER_MESSAGES) k.sendingCounter REKEY_AFTER_MESSAGES) do
        WG.andM (branch .freshInitiator k.iAmTheInitiator) do
          branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME)
  if ← o.step (branch .freshSend send) then queuedWith o pid false

def freshReceiveWith [Monad m] (o : Ops m) (pid : PeerId) : m Unit := do
  if ← o.step (branch .rxFreshSentLastminute (← o.step (getPeer pid)).sentLastminuteHandshake) then return
  let current := (← o.step (getPeer pid)).keypairCurrent
  let send ← o.step (WG.andM (branch .rxFreshKeypair current.isSome) do
    let some id := current | invariant "unreachable"
    let k ← getKeypair id
    WG.andM (branch .rxFreshValid k.sending.isValid) do
      WG.andM (branch .rxFreshInitiator k.iAmTheInitiator) do
        branchExpired .rxFreshExpired k.sending.birthdate (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT))
  if ← o.step (branch .rxFreshSend send) then
    o.step (do setPeer pid { (← getPeer pid) with sentLastminuteHandshake := true })
    queuedWith o pid false

def noKeyWith [Monad m] (o : Ops m) (pid : PeerId) (packets : List Packet)
    (keypair : Option KeypairId) (invalid : Bool) : m Unit := do
  if invalid then
    let some id := keypair | o.step (invariant "unreachable")
    let k ← o.step (getKeypair id)
    o.step (setKeypair id {k with sending := {k.sending with isValid := false}})
  o.step (keypairPut keypair false)
  for _ in packets do _ ← o.step (branch .stagedOrphanWalk true)
  _ ← o.step (branch .stagedOrphanWalk false)
  o.step (do setPeer pid { (← getPeer pid) with staged := packets ++ (← getPeer pid).staged })
  queuedWith o pid false

def prepareWith [Monad m] (o : Ops m) (pid : PeerId) (pkt : RxPacket) : m (Option Packets.RxReady) := do
  freshReceiveWith o pid
  o.step (timersAnyAuthenticatedPacketReceived pid)
  traversalWith o pid
  let bytes := pkt.bytes
  let len := bytes.length
  let reject (why : Dishonest) : m (Option Packets.RxReady) := do
    o.step (dishonest why)
    return none
  if ← o.step (branch .doneRxKeepalive (len == 0)) then
    o.step (updateRxStats pid MESSAGE_DATA_LEN_0)
    return none
  dataReceivedWith o pid
  if ← o.step (branch .doneNetworkBelowHead false) then return ← reject .size
  let version := (bytes.headD 0).toNat / 16
  let honest ← o.step (WG.andM (branch .doneMayPullV4 (len ≥ 20)) do
    WG.orM (branch .doneVersion4 (version == 4)) do
      WG.andM (branch .doneVersion6 (version == 6)) (branch .doneMayPullV6 (len ≥ 40)))
  if !honest then return ← reject .type
  let protocol := ipTunnelParseProtocol bytes
  let ds := pkt.ds
  let mut ipLen := 0
  let mut bytes := bytes
  if ← o.step (branch .doneProtoIp (protocol == 4)) then
    ipLen := beAt bytes 2 2
    if ← o.step (branch .doneV4TooShort (ipLen < 20)) then return ← reject .size
    bytes ← o.step (inetEcnDecapsulate 4 ds bytes)
  else if ← o.step (branch .doneProtoIpv6 (protocol == 6)) then
    ipLen := beAt bytes 4 2 + 40
    bytes ← o.step (inetEcnDecapsulate 6 ds bytes)
  else return ← reject .type
  if ← o.step (branch .doneLenBeyond (ipLen > len)) then return ← reject .size
  let lenBeforeTrim := len
  if ← o.step (branch .doneTrimFailed false) then return none
  return some ⟨protocol,bytes,ipLen,lenBeforeTrim⟩

theorem freshSend_factor (pid : PeerId) : keepKeyFresh pid = freshSendWith native pid := rfl
theorem freshReceive_factor (pid : PeerId) : keepKeyFreshRx pid = freshReceiveWith native pid := by
  unfold keepKeyFreshRx freshReceiveWith
  rw [← queued_factor]
  simp only [native,id,bind_assoc]
  rfl
theorem noKey_factor (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    Lifetimes.stagedOutNokey pid packets keypair invalid = noKeyWith native pid packets keypair invalid := by
  unfold Lifetimes.stagedOutNokey noKeyWith
  rw [← queued_factor]
  simp only [native,id,bind_assoc]
  rfl
theorem prepare_factor (pid : PeerId) (pkt : RxPacket) :
    Queues.RxCredits.prepareRest pid pkt = prepareWith native pid pkt := by
  unfold Queues.RxCredits.prepareRest prepareWith
  rw [← freshReceive_factor,← traversal_factor,← dataReceived_factor]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.PacketEffects
