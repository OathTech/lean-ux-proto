import Leanux.Proofs.WG.Lifetimes.ReceiveEntry

/-! A conditional whole-call equation for device-work queue failure. The
premises name original prelude operations, including the setter's nested
getter; no observed prefix or allocation invariant is assumed. This is not a
recorded runner reproduction. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem enqueuePerDeviceAndPeerRxPrefix_queue_failure (id : SkbId)
    (w marked checked queued selected cpuSet queueEntry : World)
    (h : List LifetimeEvent) (initial pkt : RxPacket) (p : Peer) (d : Device)
    (cpu : Int) (e : Stop)
    (hfirst : (getRxSkb id).run w = .ok (initial, w))
    (hmark : (setRxSkb id fun p => {p with state := .uncrypted}).run w = .ok ((), marked))
    (hpacket : (getRxSkb id).run marked = .ok (pkt, marked))
    (hpeer : (getPeer pkt.peer).run marked = .ok (p, marked))
    (hfull : (branch .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS)).run marked =
      .ok (false, checked))
    (hwrite : (setPeer pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).run checked = .ok ((), queued))
    (hdev : getDev.run queued = .ok (d, queued))
    (hcpu : (cpumaskNextOnlineFrom d.decryptLastCpu).run queued = .ok (cpu, selected))
    (hset : (modifyDev fun d => {d with decryptLastCpu := cpu}).run selected = .ok ((), cpuSet))
    (hring : (branch .enqueueRingFull d.decryptQueue.full).run cpuSet = .ok (false, queueEntry))
    (hqueue : (queueDeviceWork .decryptWorker).run queueEntry = .error e) :
    runPrefix (enqueuePerDeviceAndPeerRxPrefix id) w h =
      (.error e, h ++ [.packet (.read (.inr id) (packetStamp w id)),
        .packet (.write (.inr id) (packetStamp w id)),
        .packet (.read (.inr id) (packetStamp marked id)),
        .peer (.read pkt.peer p.internalId), .peer (.write pkt.peer p.internalId)]) := by
  have present : checked.k.wg.isSome = true := by
    have hf := sameKernel_branch .enqueuePeerQueueFull
      (p.rxQueue.count ≥ MAX_QUEUED_PACKETS) marked false checked hfull
    rw [hf]
    cases hd : marked.k.wg with
    | none => simp [getPeer, getDev, getK, hd, invariant] at hpeer
    | some d => rfl
  simp [enqueuePerDeviceAndPeerRxPrefix, runPrefix_bind, setRxSkbPrefix_run,
    hfirst, hmark, getRxSkbPrefix_run, hpacket, getPeerMixed_run, hpeer,
    hfull, setPeerMixed_run, present, hwrite, hdev, hcpu, hset, hring, hqueue,
    List.append_assoc]

end Leanux.Proofs.WG.Lifetimes
