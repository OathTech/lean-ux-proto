import Leanux.Proofs.WG.Lifetimes.ProductAmbient

/-! Receive enqueue with one shared, failure-retaining event stream. The
callback is an explicit parameter; its observations are composed in place. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def enqueuePerPeerRxPrefix (irq : PrefixM LifetimeEvent Unit) (id : SkbId) (state : PacketState) : PrefixM LifetimeEvent Unit := do
  let pid ← liftWGObserver (peerDerefPrefix (.keypair (← liftWGObserver (getRxSkbPrefix id)).keypair))
  liftWGObserver (peerGetMixed pid)
  let p ← liftWGObserver (getPeerMixed pid)
  if !(p.rxQueue.all.contains id) then
    liftPrefix (invariant "a decrypted packet that is not on its peer's rx_queue")
  liftWGObserver (setRxSkbPrefix id fun q => { q with state })
  liftWGObserver (setPeerMixed pid { p with napiScheduled := true })
  irq
  liftWGObserver (peerPutMixed (some pid))

theorem enqueuePerPeerRxPrefix_erases (hi : ErasesPrefix irq original)
    (id : SkbId) (state : PacketState) :
    ErasesPrefix (enqueuePerPeerRxPrefix irq id state) (enqueuePerPeerRx original id state) := by
  unfold enqueuePerPeerRxPrefix enqueuePerPeerRx
  apply erasesPrefix_bind (liftWGObserver_erases (getRxSkbPrefix_erases id))
  intro pkt
  apply erasesPrefix_bind (liftWGObserver_erases (peerDerefPrefix_erases (.keypair pkt.keypair)))
  intro pid
  apply erasesPrefix_bind (liftWGObserver_erases (peerGetMixed_erases pid))
  intro _
  apply erasesPrefix_bind (liftWGObserver_erases (getPeerMixed_erases pid))
  intro p
  dsimp only
  split
  · apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    apply erasesPrefix_bind (liftWGObserver_erases (setRxSkbPrefix_erases id _))
    intro _
    apply erasesPrefix_bind (liftWGObserver_erases (setPeerMixed_erases pid _))
    intro _
    apply erasesPrefix_bind hi
    intro _
    exact liftWGObserver_erases (peerPutMixed_erases (some pid))
  · apply erasesPrefix_bind (liftWGObserver_erases (setRxSkbPrefix_erases id _))
    intro _
    apply erasesPrefix_bind (liftWGObserver_erases (setPeerMixed_erases pid _))
    intro _
    apply erasesPrefix_bind hi
    intro _
    exact liftWGObserver_erases (peerPutMixed_erases (some pid))

theorem enqueuePerPeerRxPrefix_pure_erases (id : SkbId) (state : PacketState) :
    ErasesPrefix (enqueuePerPeerRxPrefix (pure ()) id state)
      (enqueuePerPeerRx (pure ()) id state) :=
  enqueuePerPeerRxPrefix_erases (erasesPrefix_pure ()) id state

theorem mixed_drop {S α : Type} {project : S → WGWorld}
    {g : PrefixT LifetimeEvent S α} {Q : α → IdentityView → Prop}
    (hg : ProjectedAmbientSpec project (fun h w => MixedInv h (project w)) (fun _ => True) g Q) :
    PrefixPreserves (fun h w => MixedInv h (project w)) LifetimeEvent.Safe g :=
  AmbientContracts.projectedDrop hg

theorem enqueuePerPeerRxPrefix_preserves_ambient (c : ProductAmbientContracts I)
    (hi : PrefixPreserves I LifetimeEvent.Safe irq) (id : SkbId) (state : PacketState) :
    PrefixPreserves I LifetimeEvent.Safe (enqueuePerPeerRxPrefix irq id state) := by
  unfold enqueuePerPeerRxPrefix
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getRx (fun _ => True) id))
  intro pkt
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.peerDeref (fun _ => True) (.keypair pkt.keypair)))
  intro pid
  apply PrefixPreserves.bind (c.peerGet pid)
  intro _
  apply PrefixEnsures.preserves
  have hget : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (getPeerMixed pid))
      (fun p h w => I h w ∧ (identityView w.wg).1.slots pid = some p.internalId) :=
    (c.getPeer (fun _ => True) pid).consequence
      (fun _ _ hn => ⟨hn, True.intro⟩) (fun _ _ _ hn => ⟨hn.1, hn.2.2⟩)
  apply PrefixEnsures.bind hget
  intro p
  dsimp only
  have tail : PrefixEnsures
      (fun h w => I h w ∧ (identityView w.wg).1.slots pid = some p.internalId)
      LifetimeEvent.Safe
      (do liftWGObserver (setRxSkbPrefix id fun q => {q with state})
          liftWGObserver (setPeerMixed pid {p with napiScheduled := true})
          irq
          liftWGObserver (peerPutMixed (some pid))) (fun _ => I) := by
    apply PrefixEnsures.bind (c.setRx (fun s => s.1.slots pid = some p.internalId) id _)
    intro _
    apply PrefixEnsures.bind ((c.setPeer (fun _ => True) pid
      {p with napiScheduled := true}).consequence
        (fun _ _ hn => ⟨hn.1, True.intro, hn.2⟩) (fun _ _ _ hn => hn.1))
    intro _
    exact PrefixPreserves.bind hi (fun _ => c.peerPut (some pid))
  split
  · apply PrefixEnsures.bind (Q := fun (_ : Unit) h w =>
        I h w ∧ (identityView w.wg).1.slots pid = some p.internalId)
    · apply PrefixEnsures.lift _ (fun h w hn => c.safe h w hn.1)
      intro h w x v hn hr
      simp [invariant, liftAmbient_run, AmbientM.invariant] at hr
      cases hr
    intro _
    exact tail
  · exact tail

theorem enqueuePerPeerRxPrefix_preserves
    (hi : PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe irq) (id : SkbId) (state : PacketState) :
    PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe (enqueuePerPeerRxPrefix irq id state) :=
  enqueuePerPeerRxPrefix_preserves_ambient (ProductAmbientContracts.ofNative mixedAmbient) hi id state

theorem enqueuePerPeerRxPrefix_pure_preserves (id : SkbId) (state : PacketState) :
    PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe (enqueuePerPeerRxPrefix (pure ()) id state) :=
  enqueuePerPeerRxPrefix_preserves
    (PrefixPreserves.pure (fun _ _ hi => hi.safe) ()) id state

/-- Failure to resolve the packet's keypair retains the successful packet
read, and performs no peer access or callback. This holds on every World. -/
theorem enqueuePerPeerRxPrefix_keypair_failure (irq : PrefixM LifetimeEvent Unit) (id : SkbId)
    (state : PacketState) (w : World) (h : List LifetimeEvent) (pkt : RxPacket) (e : Stop)
    (hr : ((getRxSkb id).run w.wg).run w.ambient = .ok ((pkt, w.wg), w.ambient))
    (hk : ((getKeypair pkt.keypair).run w.wg).run w.ambient = .error e) :
    runPrefix (enqueuePerPeerRxPrefix irq id state) w h =
      (.error e, h ++ [.packet (.read (.inr id) (packetStamp w.wg id))]) := by
  have packet : runPrefix (liftWGObserver (getRxSkbPrefix id)) w h =
      (.ok (pkt, w), h ++ [.packet (.read (.inr id) (packetStamp w.wg id))]) := by
    rw [liftWGObserver_run]
    simp only [runWGPrefix, getRxSkbPrefix_run, hr, Except.map]
  have key (hist : List LifetimeEvent) :
      runPrefix (liftWGObserver (peerDerefPrefix (.keypair pkt.keypair))) w hist =
        (.error e, hist) := by
    rw [liftWGObserver_run]
    simp only [runWGPrefix, peerDerefPrefix, peerWordPrefix, runStatePrefix_bind,
      getKeypairPrefix_run, hk, Except.map]
  simp only [enqueuePerPeerRxPrefix, runPrefix_bind, packet, key]

/-- The concrete native, pure-interrupt call used by consumeData. The product
observer above retains its unrestricted callback. -/
def enqueuePerPeerRxNativePrefix (id : SkbId) (state : PacketState) : MixedM Unit := do
  let pid ← peerDerefPrefix (.keypair (← getRxSkbPrefix id).keypair)
  peerGetMixed pid
  let p ← getPeerMixed pid
  if !(p.rxQueue.all.contains id) then
    liftWGPrefix (invariant "a decrypted packet that is not on its peer's rx_queue")
  setRxSkbPrefix id fun q => {q with state}
  setPeerMixed pid {p with napiScheduled := true}
  pure ()
  peerPutMixed (some pid)

theorem enqueuePerPeerRxNativePrefix_erases (id : SkbId) (state : PacketState) :
    ErasesStatePrefix (enqueuePerPeerRxNativePrefix id state)
      (enqueuePerPeerRx (pure () : WG.M Unit) id state) := by
  unfold enqueuePerPeerRxNativePrefix enqueuePerPeerRx
  apply erasesStatePrefix_bind (getRxSkbPrefix_erases id)
  intro pkt
  apply erasesStatePrefix_bind (peerDerefPrefix_erases (.keypair pkt.keypair))
  intro pid
  apply erasesStatePrefix_bind (peerGetMixed_erases pid)
  intro _
  apply erasesStatePrefix_bind (getPeerMixed_erases pid)
  intro p
  dsimp only
  split
  · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro _
    apply erasesStatePrefix_bind (setRxSkbPrefix_erases id _)
    intro _
    apply erasesStatePrefix_bind (setPeerMixed_erases pid _)
    intro _
    simpa only [pure_bind, liftM, monadLift, monadLift_self] using peerPutMixed_erases (some pid)
  · apply erasesStatePrefix_bind (setRxSkbPrefix_erases id _)
    intro _
    apply erasesStatePrefix_bind (setPeerMixed_erases pid _)
    intro _
    simpa only [pure_bind, liftM, monadLift, monadLift_self] using peerPutMixed_erases (some pid)

theorem enqueuePerPeerRxNativePrefix_preserves_ambient (c : AmbientContracts I)
    (id : SkbId) (state : PacketState) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (enqueuePerPeerRxNativePrefix id state) := by
  unfold enqueuePerPeerRxNativePrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getRx (fun _ => True) id))
  intro pkt
  apply StatePrefixEnsures.bind (AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) (.keypair pkt.keypair)))
  intro pid
  apply StatePrefixEnsures.bind (c.peerGet pid)
  intro _
  have hget : StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe (getPeerMixed pid)
      (fun p h w _ => I h w ∧ (identityView w).1.slots pid = some p.internalId) :=
    (c.getPeer (fun _ => True) pid).consequence
      (fun _ _ _ hn => ⟨hn, True.intro⟩) (fun _ _ _ _ hn => ⟨hn.1, hn.2.2⟩)
  apply StatePrefixEnsures.bind hget
  intro p
  dsimp only
  have tail : StatePrefixEnsures
      (fun h w _ => I h w ∧ (identityView w).1.slots pid = some p.internalId)
      LifetimeEvent.Safe
      (do setRxSkbPrefix id fun q => {q with state}
          setPeerMixed pid {p with napiScheduled := true}
          pure ()
          peerPutMixed (some pid)) (fun _ h w _ => I h w) := by
    apply StatePrefixEnsures.bind (c.setRx (fun s => s.1.slots pid = some p.internalId) id _)
    intro _
    apply StatePrefixEnsures.bind ((c.setPeer (fun _ => True) pid
      {p with napiScheduled := true}).consequence
        (fun _ _ _ hn => ⟨hn.1, True.intro, hn.2⟩) (fun _ _ _ _ hn => hn.1))
    intro _
    simpa only [pure_bind] using c.peerPut (some pid)
  split
  · apply StatePrefixEnsures.bind (Q := fun (_ : Unit) h w _ =>
        I h w ∧ (identityView w).1.slots pid = some p.internalId)
    · apply StatePrefixEnsures.lift _ (fun h w _ hn => c.safe h w hn.1)
      intro h w ambient x v ambient' hn hr
      simp [invariant, AmbientM.invariant] at hr
      cases hr
    intro _
    exact tail
  · exact tail

theorem enqueuePerPeerRxNativePrefix_lift (id : SkbId) (state : PacketState) :
    liftWGObserver (enqueuePerPeerRxNativePrefix id state) =
      enqueuePerPeerRxPrefix (pure ()) id state := by
  unfold enqueuePerPeerRxNativePrefix enqueuePerPeerRxPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, pure_bind]
  congr 1
  funext pkt
  congr 1
  funext pid
  congr 1
  funext u
  congr 1
  funext p
  split <;> simp only [liftWGObserver_bind, liftWGObserver_lift, liftWGObserver_pure, pure_bind]
  all_goals rfl

end Leanux.Proofs.WG.Lifetimes
