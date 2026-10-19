import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalEffectsSource
import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsSource

/-! Native receive-side rekey maintenance exposes the same nested repayment
as timer and no-key queueing, before any later packet-processing Stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PacketSource
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects TimerEffects

def freshReceiveWith [Monad m] (o : Ops m) (release : Option PeerId → m Unit) (pid : PeerId) : m Unit := do
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
    Effects.queuedWith o release pid false

def prepareWith [Monad m] (o : Ops m) (release : Option PeerId → m Unit) (pid : PeerId) (pkt : RxPacket) : m (Option Packets.RxReady) := do
  freshReceiveWith o release pid
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


theorem freshReceive_neutral [Monad m] (o : Ops m) (pid : PeerId) :
    freshReceiveWith o (fun peer => o.step (peerPut peer)) pid = PacketEffects.freshReceiveWith o pid := by
  unfold freshReceiveWith PacketEffects.freshReceiveWith
  simp only [Effects.queued_neutral]
  rfl

theorem prepare_neutral [Monad m] (o : Ops m) (pid : PeerId) (pkt : RxPacket) :
    prepareWith o (fun peer => o.step (peerPut peer)) pid pkt = PacketEffects.prepareWith o pid pkt := by
  unfold prepareWith PacketEffects.prepareWith
  rw [freshReceive_neutral]

end Leanux.Proofs.WG.HandshakeSecurity.StagedDisposal.PacketSource
