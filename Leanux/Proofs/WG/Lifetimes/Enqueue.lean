import Leanux.Proofs.WG.Lifetimes.Acquire

/-! Receive enqueue with one shared, failure-retaining event stream. The
callback is an explicit parameter; its observations are composed in place. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged

def enqueuePerPeerRxPrefix (irq : MixedM Unit) (id : SkbId) (state : PacketState) : MixedM Unit := do
  let pid := (← getKeypairPrefix (← getRxSkbPrefix id).keypair).peer
  peerGetMixed pid
  let p ← getPeerMixed pid
  if !(p.rxQueue.all.contains id) then
    liftPrefix (invariant "a decrypted packet that is not on its peer's rx_queue")
  setRxSkbPrefix id fun q => { q with state }
  setPeerMixed pid { p with napiScheduled := true }
  irq
  peerPutMixed (some pid)

theorem enqueuePerPeerRxPrefix_erases (hi : ErasesPrefix irq original)
    (id : SkbId) (state : PacketState) :
    ErasesPrefix (enqueuePerPeerRxPrefix irq id state) (enqueuePerPeerRx original id state) := by
  unfold enqueuePerPeerRxPrefix enqueuePerPeerRx
  apply erasesPrefix_bind (getRxSkbPrefix_erases id)
  intro pkt
  apply erasesPrefix_bind (getKeypairPrefix_erases pkt.keypair)
  intro kp
  apply erasesPrefix_bind (peerGetMixed_erases kp.peer)
  intro _
  apply erasesPrefix_bind (getPeerMixed_erases kp.peer)
  intro p
  dsimp only
  split
  · apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    apply erasesPrefix_bind (setRxSkbPrefix_erases id _)
    intro _
    apply erasesPrefix_bind (setPeerMixed_erases kp.peer _)
    intro _
    apply erasesPrefix_bind hi
    intro _
    exact peerPutMixed_erases (some kp.peer)
  · apply erasesPrefix_bind (setRxSkbPrefix_erases id _)
    intro _
    apply erasesPrefix_bind (setPeerMixed_erases kp.peer _)
    intro _
    apply erasesPrefix_bind hi
    intro _
    exact peerPutMixed_erases (some kp.peer)

theorem enqueuePerPeerRxPrefix_pure_erases (id : SkbId) (state : PacketState) :
    ErasesPrefix (enqueuePerPeerRxPrefix (pure ()) id state)
      (enqueuePerPeerRx (pure ()) id state) :=
  enqueuePerPeerRxPrefix_erases (erasesPrefix_pure ()) id state

theorem mixed_drop (hg : MixedSpec (fun _ => True) g Q) :
    PrefixPreserves MixedInv LifetimeEvent.Safe g :=
  (hg.consequence (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => hi.1)).preserves

theorem enqueuePerPeerRxPrefix_preserves
    (hi : PrefixPreserves MixedInv LifetimeEvent.Safe irq) (id : SkbId) (state : PacketState) :
    PrefixPreserves MixedInv LifetimeEvent.Safe (enqueuePerPeerRxPrefix irq id state) := by
  unfold enqueuePerPeerRxPrefix
  apply PrefixPreserves.bind (mixed_drop (mixed_getRxSkb (fun _ => True) id))
  intro pkt
  apply PrefixPreserves.bind (mixed_drop (mixed_getKeypair (fun _ => True) pkt.keypair))
  intro kp
  apply PrefixPreserves.bind (peerGetMixed_preserves kp.peer)
  intro _
  apply PrefixEnsures.preserves
  have hget : PrefixEnsures MixedInv LifetimeEvent.Safe (getPeerMixed kp.peer)
      (fun p h w => MixedInv h w ∧ (identityView w).1.slots kp.peer = some p.internalId) :=
    (mixed_getPeer (fun _ => True) kp.peer).consequence
      (fun _ _ hn => ⟨hn, True.intro⟩) (fun _ _ _ hn => ⟨hn.1, hn.2.2⟩)
  apply PrefixEnsures.bind hget
  intro p
  dsimp only
  have tail : PrefixEnsures
      (fun h w => MixedInv h w ∧ (identityView w).1.slots kp.peer = some p.internalId)
      LifetimeEvent.Safe
      (do setRxSkbPrefix id fun q => {q with state}
          setPeerMixed kp.peer {p with napiScheduled := true}
          irq
          peerPutMixed (some kp.peer)) (fun _ => MixedInv) := by
    apply PrefixEnsures.bind (mixed_setRxSkb (fun s => s.1.slots kp.peer = some p.internalId) id _)
    intro _
    apply PrefixEnsures.bind ((mixed_setPeer (fun _ => True) kp.peer
      {p with napiScheduled := true}).consequence
        (fun _ _ hn => ⟨hn.1, True.intro, hn.2⟩) (fun _ _ _ hn => hn.1))
    intro _
    exact PrefixPreserves.bind hi (fun _ => peerPutMixed_preserves (some kp.peer))
  split
  · apply PrefixEnsures.bind (Q := fun (_ : Unit) h w =>
        MixedInv h w ∧ (identityView w).1.slots kp.peer = some p.internalId)
    · apply PrefixEnsures.lift _ (fun _ _ hn => hn.1.safe)
      intro h w x v hn hr
      simp [invariant] at hr
    intro _
    exact tail
  · exact tail

theorem enqueuePerPeerRxPrefix_pure_preserves (id : SkbId) (state : PacketState) :
    PrefixPreserves MixedInv LifetimeEvent.Safe (enqueuePerPeerRxPrefix (pure ()) id state) :=
  enqueuePerPeerRxPrefix_preserves
    (PrefixPreserves.pure (fun _ _ hi => hi.safe) ()) id state

/-- Failure to resolve the packet's keypair retains the successful packet
read, and performs no peer access or callback. This holds on every World. -/
theorem enqueuePerPeerRxPrefix_keypair_failure (irq : MixedM Unit) (id : SkbId)
    (state : PacketState) (w : World) (h : List LifetimeEvent) (pkt : RxPacket) (e : Stop)
    (hr : (getRxSkb id).run w = .ok (pkt, w))
    (hk : (getKeypair pkt.keypair).run w = .error e) :
    runPrefix (enqueuePerPeerRxPrefix irq id state) w h =
      (.error e, h ++ [.packet (.read (.inr id) (packetStamp w id))]) := by
  simp only [enqueuePerPeerRxPrefix, runPrefix_bind, getRxSkbPrefix_run, hr,
    getKeypairPrefix_run, hk]

end Leanux.Proofs.WG.Lifetimes
