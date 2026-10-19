import Leanux.Proofs.WG.Lifetimes.ReceiveEntry

/-! A conditional whole-call equation for device-work queue failure. The
premises name original prelude operations, including the setter's nested
getter; no observed prefix or allocation invariant is assumed. This is not a
recorded runner reproduction. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem enqueuePerDeviceAndPeerRxPrefix_queue_failure (id : SkbId)
    (w marked checked queued selected cpuSet queueEntry : WGWorld)
    (ambient markedAmbient checkedAmbient queuedAmbient selectedAmbient cpuSetAmbient queueAmbient : Ambient)
    (h : List LifetimeEvent) (initial pkt : RxPacket) (p : Peer) (d : Device)
    (cpu : Int) (e : Stop)
    (hfirst : ((getRxSkb id).run w).run ambient = .ok ((initial, w), ambient))
    (hmark : ((setRxSkb id fun p => {p with state := .uncrypted}).run w).run ambient =
      .ok (((), marked), markedAmbient))
    (hpacket : ((getRxSkb id).run marked).run markedAmbient = .ok ((pkt, marked), markedAmbient))
    (hpeer : ((getPeer pkt.peer).run marked).run markedAmbient = .ok ((p, marked), markedAmbient))
    (hfull : ((branch .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS) : WG.M Bool).run marked).run markedAmbient =
      .ok ((false, checked), checkedAmbient))
    (hwrite : ((setPeer pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).run checked).run checkedAmbient =
      .ok (((), queued), queuedAmbient))
    (hdev : (getDev.run queued).run queuedAmbient = .ok ((d, queued), queuedAmbient))
    (hcpu : ((cpumaskNextOnlineFrom d.decryptLastCpu).run queued).run queuedAmbient =
      .ok ((cpu, selected), selectedAmbient))
    (hset : ((modifyDev fun d => {d with decryptLastCpu := cpu}).run selected).run selectedAmbient =
      .ok (((), cpuSet), cpuSetAmbient))
    (hring : ((branch .enqueueRingFull d.decryptQueue.full : WG.M Bool).run cpuSet).run cpuSetAmbient =
      .ok ((false, queueEntry), queueAmbient))
    (hqueue : ((queueDeviceWork .decryptWorker : WG.M Unit).run queueEntry).run queueAmbient = .error e) :
    runStatePrefix (enqueuePerDeviceAndPeerRxPrefix id) w ambient h =
      (.error e, h ++ [.packet (.read (.inr id) (packetStamp w id)),
        .packet (.write (.inr id) (packetStamp w id)),
        .packet (.read (.inr id) (packetStamp marked id)),
        .peer (.read pkt.peer p.internalId), .peer (.write pkt.peer p.internalId)]) := by
  have present : checked.dev.isSome = true := by
    have hf : checked = marked := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .enqueuePeerQueueFull
        (p.rxQueue.count ≥ MAX_QUEUED_PACKETS)) (fun g => g = marked))
      marked markedAmbient false checked checkedAmbient rfl hfull
    rw [hf]
    cases hd : marked.dev with
    | none =>
      simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hpeer
      change (Except.error (.invariant "no WireGuard device in this trace's fixture") :
        Except Stop ((Peer × WGWorld) × Ambient)) = .ok ((p, marked), markedAmbient) at hpeer
      cases hpeer
    | some d => rfl
  simp [enqueuePerDeviceAndPeerRxPrefix, runStatePrefix_bind, runStatePrefix_lift, liftWGPrefix, setRxSkbPrefix_run,
    hfirst, hmark, getRxSkbPrefix_run, hpacket, getPeerMixed_run, hpeer,
    hfull, setPeerMixed_run, present, hwrite, hdev, hcpu, hset, hring, hqueue,
    List.append_assoc]

end Leanux.Proofs.WG.Lifetimes
