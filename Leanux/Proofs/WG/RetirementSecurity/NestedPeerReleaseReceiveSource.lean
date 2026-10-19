import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxSource

/-! The original packet and UDP receive entry with only its data-consumption
callback exposed. Header validation and handshake queue production remain in
source order; the data callback observes the nested peer repayments. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {m : Type → Type} [Monad m]

def packetReceiveWith (o : Ops m) (consume : Key → SkbSource → Nat → m Unit)
    (msg : Key) (src : SkbSource) : m Unit := do
  if ← o.step (branch .rxPrepareFailed !(← o.step (prepareSkbHeader msg))) then return
  let t := messageType msg
  if ← o.step (branch .rxHandshake (t == MESSAGE_HANDSHAKE_INITIATION ||
      t == MESSAGE_HANDSHAKE_RESPONSE || t == MESSAGE_HANDSHAKE_COOKIE)) then
    if ← o.step (branch .rxRngNotReady false) then o.step (unsupported "unreachable")
    _ ← o.step (branch .rxQueueBusy
      ((← o.step getDev).handshakeQueueLen > MAX_QUEUED_INCOMING_HANDSHAKES / 2))
    if ← o.step (branch .rxProduceFailed (← o.step getDev).handshakeQueue.full) then return
    o.step (modifyDev fun d => { d with handshakeQueue := d.handshakeQueue.produce (msg, src), handshakeQueueLen := d.handshakeQueueLen + 1 })
    o.step cpumaskNextOnline
    o.step (queueDeviceWork .receiveWorker)
    return
  if ← o.step (branch .rxData (t == MESSAGE_DATA)) then
    let ds ← o.step (ipTunnelGetDsfield
      (if src.family == 4 then ETH_P_IP else ETH_P_IPV6) (outerDsBytes src))
    consume msg src ds
    return
  o.step (invariant "validate_header_len admitted an unknown type")

def receiveWith (o : Ops m) (consume : Key → SkbSource → Nat → m Unit)
    (msg : Key) (src : SkbSource) : m Unit := do
  if ← o.step (branch .rxNoSock false) then o.step (unsupported "unreachable")
  if ← o.step (branch .rxNoWg false) then o.step (unsupported "unreachable")
  packetReceiveWith o consume msg src

def receive (o : Ops m) (msg : Key) (src : SkbSource) : m Unit :=
  receiveWith o (ingress o) msg src

theorem packetReceive_native (msg : Key) (src : SkbSource) :
    packetReceiveWith native consumeData msg src = packetReceive msg src := rfl

theorem receive_native (msg : Key) (src : SkbSource) :
    receive native msg src = wgReceive msg src := by
  have consume : ingress native = consumeData := by
    funext msg src ds
    exact ingress_native msg src ds
  unfold receive receiveWith
  rw [consume, packetReceive_native]
  rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
