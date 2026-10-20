import Leanux.Proofs.WG.HandshakeSecurity.ExchangeProductFrames

/-! Explicit native worker-frame projections of C2 H1 at `be8c209c`.
These are per-call operational facts, with no initialized history assumed. -/
namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Queues

abbrev H1ProductTagRetains (action : Leanux.M α) : Prop :=
  ∀ w value v, action.run w = .ok (value,v) → Exchange.Retains w.wg v.wg

structure H1WorkerTagFrames : Prop where
  /-- C2 `Noise.DriverTags.Poll.poll_native`, pin `be8c209c`. -/
  poll : ∀ pid budget, H1ProductTagRetains
    (rxPoll pid budget (fun bytes => bytes.forM Env.deliverInner))
  /-- C2 `Noise.DriverTags.Poll.softirq_native`, pin `be8c209c`. -/
  softirq : H1ProductTagRetains Env.napiSoftirq
  /-- C2 `Noise.DriverTags.Poll.inline_native`, pin `be8c209c`. -/
  inlinePoll : H1ProductTagRetains Env.pollScheduledInline
  /-- C2 `Noise.DriverTags.Poll.irqExit_native`, pin `be8c209c`. -/
  irqExit : H1ProductTagRetains Env.napiIrqExit
  /-- C2 `Noise.DriverTags.Silent.txStep_retained`, pin `be8c209c`. -/
  txStep : ∀ pid, H1TagRetains (WG.txStep pid)
  /-- C2 `Noise.DriverTags.Silent.decryptPrepare_retained`, pin `be8c209c`. -/
  decryptPrepare : H1TagRetains RxWorkers.prepareSource
  /-- C2 `Noise.DriverTags.Silent.enqueue_retained`, pin `be8c209c`. -/
  enqueue : ∀ item state, H1TagRetains (enqueuePerPeerTx item state)
  /-- C2 `Noise.DriverTags.Silent.encryptPacket_retained`, pin `be8c209c`. -/
  encryptPacket : ∀ kid pkt, H1ProductTagRetains (WG.encryptPacket Env.checksumHelp kid pkt)

end Leanux.Proofs.WG.HandshakeSecurity
