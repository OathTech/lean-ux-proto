import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseSource
import Leanux.Proofs.WG.Packets.RxOriginCuts
import Leanux.Proofs.WG.Packets.RoutingCuts

/-! Existing RX source factors with the nested repayment callbacks exposed.
Allocation, publication, IRQ and routing cuts keep their original order. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged

variable {m : Type → Type} [Monad m]

/-- The native publication cut acquires the temporary peer reference. The IRQ
callback runs before its repayment, including on the ingress DEAD arm. -/
def publishWith (o : Ops m) (irq : m Unit) (skb : SkbId) (state : PacketState) : m Unit := do
  let pid ← o.step (Queues.RxWorkers.publishSource skb state)
  irq
  o.release (some pid)

def admitWith (o : Ops m) (allocate : RxPacket → m SkbId)
    (msg : Key) (src : SkbSource) (ds : Nat) : m (Option RxOrigin.Admission) :=
  RxOrigin.admitWith (sourceM := WG.M)
    (fun mask index => o.step (indexLookup mask index))
    (fun key => o.step (keypairGet key)) (fun peer => o.step (getPeer peer))
    (fun key unreference => o.step (keypairPut key unreference)) o.release allocate o.step msg src ds

def ingressFinishWith (o : Ops m) (publish : SkbId → m Unit) (a : RxOrigin.Admission) : m Unit :=
  RxOrigin.finishWith (sourceM := WG.M)
    (fun key unreference => o.step (keypairPut key unreference)) o.release
    (fun skb => o.step (enqueuePerDeviceAndPeerRx skb)) publish
    (fun skb => o.step (freeRxSkb skb)) o.step a

def ingressWith (o : Ops m) (front : m (Option RxOrigin.Admission))
    (publish : SkbId → m Unit) : m Unit := do
  match ← front with
  | none => return
  | some a => ingressFinishWith o publish a

def ingress (o : Ops m) (msg : Key) (src : SkbSource) (ds : Nat) : m Unit :=
  ingressWith o (admitWith o (fun pkt => o.step (newRxSkb pkt)) msg src ds)
    (fun skb => publishWith o (pure ()) skb .dead)

def rxAfterLookupWith (o : Ops m) (pid : PeerId) (ready : Packets.RxReady)
    (routed : Option PeerId) : m (Option Key) := do
  o.release routed
  if ← o.step (branch .doneDishonestPeer (routed != some pid)) then
    o.step (dishonest .peer)
    return none
  o.step (updateRxStats pid (ready.originalLen + MESSAGE_DATA_LEN_0))
  return some (ready.bytes.take ready.ipLen)

def rxFinishWith (o : Ops m) (pid : PeerId) (ready : Packets.RxReady) : m (Option Key) := do
  let routed ← o.step (lookupSrc ready.protocol ready.bytes)
  rxAfterLookupWith o pid ready routed

theorem publish_native (irq : WG.M Unit) (skb : SkbId) (state : PacketState) :
    publishWith native irq skb state = enqueuePerPeerRx irq skb state := by
  unfold publishWith Queues.RxWorkers.publishSource enqueuePerPeerRx
  simp only [native,bind_assoc,monadLift_self]
  repeat' first
    | rfl
    | apply Queues.RxWorkers.bind_congr
    | (intro x; try dsimp only)
    | (split <;> simp only [bind_assoc,pure_bind])

theorem admit_native (msg : Key) (src : SkbSource) (ds : Nat) :
    admitWith native newRxSkb msg src ds = RxOrigin.admitSource msg src ds := rfl

theorem ingressFinish_native (publish : SkbId → WG.M Unit) (a : RxOrigin.Admission) :
    ingressFinishWith native publish a = RxOrigin.finishWith keypairPut peerPut
      enqueuePerDeviceAndPeerRx publish freeRxSkb (fun x => x) a := rfl

theorem ingress_native (msg : Key) (src : SkbSource) (ds : Nat) :
    ingress native msg src ds = consumeData msg src ds := by
  rw [←RxOrigin.consumeSource_eq]
  unfold ingress ingressWith RxOrigin.consumeSource RxOrigin.consumeWith
  simp only [publish_native]
  rfl

theorem rxAfterLookup_native (pid : PeerId) (ready : Packets.RxReady) (routed : Option PeerId) :
    rxAfterLookupWith native pid ready routed = Packets.rxAfterLookup pid ready routed := rfl

theorem rxFinish_native (pid : PeerId) (ready : Packets.RxReady) :
    rxFinishWith native pid ready = Packets.rxFinish pid ready := rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
