import Leanux.Proofs.WG.Queues.RxNapiHistory

/-! Nonpolling source cuts at the encryption callback and RX publication.
The publication cut retains its resolved peer through the cached setter, then
returns the original numeric peer reference for the later IRQ and put. -/
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxWorkers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem bind_congr {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (h : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext h)

def publishSource (id : SkbId) (state : PacketState) : M PeerId := do
  let pid := (← getKeypair (← getRxSkb id).keypair).peer
  peerGet pid
  let p ← getPeer pid
  if !(p.rxQueue.all.contains id) then invariant "a decrypted packet that is not on its peer's rx_queue"
  setRxSkb id fun q => {q with state}
  setPeer pid {p with napiScheduled := true}
  return pid

def publishPrefix (id : SkbId) (state : PacketState) : MixedM PeerId := do
  let pid := (← getKeypairPrefix (← getRxSkbPrefix id).keypair).peer
  peerGetMixed pid
  let p ← getPeerMixed pid
  if !(p.rxQueue.all.contains id) then liftPrefix (invariant "a decrypted packet that is not on its peer's rx_queue")
  setRxSkbPrefix id fun q => {q with state}
  setPeerMixed pid {p with napiScheduled := true}
  return pid

theorem publish_erases (id : SkbId) (state : PacketState) :
    ErasesPrefix (publishPrefix id state) (publishSource id state) := by
  unfold publishPrefix publishSource
  repeat' first
    | with_reducible exact getRxSkbPrefix_erases _
    | with_reducible exact getKeypairPrefix_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setRxSkbPrefix_erases _ _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | split
    | (intro x; try dsimp only)

theorem publish_preserves (id : SkbId) (state : PacketState) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (publishPrefix id state) := by
  unfold publishPrefix
  let c := allocationAmbient
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getRx (fun _ => True) id))
  intro pkt
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getKeypair (fun _ => True) pkt.keypair))
  intro kp
  apply PrefixPreserves.bind (c.peerGet kp.peer)
  intro _
  apply PrefixEnsures.preserves
  have hget : PrefixEnsures AllocationInv LifetimeEvent.Safe (getPeerMixed kp.peer)
      (fun p h w => AllocationInv h w ∧ (identityView w).1.slots kp.peer = some p.internalId) :=
    (c.getPeer (fun _ => True) kp.peer).consequence
      (fun _ _ hn => ⟨hn, True.intro⟩) (fun _ _ _ hn => ⟨hn.1, hn.2.2⟩)
  apply PrefixEnsures.bind hget
  intro p
  dsimp only
  have tail : PrefixEnsures
      (fun h w => AllocationInv h w ∧ (identityView w).1.slots kp.peer = some p.internalId)
      LifetimeEvent.Safe
      (do setRxSkbPrefix id fun q => {q with state}
          setPeerMixed kp.peer {p with napiScheduled := true}
          pure kp.peer) (fun _ => AllocationInv) := by
    apply PrefixEnsures.bind (c.setRx (fun s => s.1.slots kp.peer = some p.internalId) id _)
    intro _
    apply PrefixEnsures.bind ((c.setPeer (fun _ => True) kp.peer
      {p with napiScheduled := true}).consequence
      (fun _ _ hn => ⟨hn.1, True.intro, hn.2⟩) (fun _ _ _ hn => hn.1))
    intro _
    exact PrefixPreserves.pure c.safe kp.peer
  split
  · apply PrefixEnsures.bind (Q := fun (_ : Unit) h w =>
      AllocationInv h w ∧ (identityView w).1.slots kp.peer = some p.internalId)
    · apply PrefixEnsures.lift _ (fun h w hn => c.safe h w hn.1)
      intro h w x v hn hr
      simp [invariant] at hr
    · intro _; exact tail
  · exact tail

theorem enqueue_source (irq : M Unit) (id : SkbId) (state : PacketState) :
    enqueuePerPeerRx irq id state = (do let pid ← publishSource id state; irq; peerPut (some pid)) := by
  simp only [enqueuePerPeerRx, publishSource, bind_assoc]
  repeat' first
    | with_reducible rfl
    | with_reducible apply bind_congr
    | (intro x; try dsimp only)
    | split
    | (simp only [bind_assoc, pure_bind]; done)

theorem enqueue_prefix (irq : MixedM Unit) (id : SkbId) (state : PacketState) :
    enqueuePerPeerRxPrefix irq id state =
      (do let pid ← publishPrefix id state; irq; peerPutMixed (some pid)) := by
  simp only [enqueuePerPeerRxPrefix, publishPrefix, bind_assoc]
  repeat' first
    | with_reducible rfl
    | with_reducible apply bind_congr
    | (intro x; try dsimp only)
    | split
    | (simp only [bind_assoc, pure_bind]; done)

def prepareSource : M (Option PeerId) := do
  match (← getDev).decryptQueue.consume with
  | (none, _) =>
    _ ← branch .decWorkerConsumed false
    return none
  | (some id, ring) =>
    _ ← branch .decWorkerConsumed true
    modifyDev fun d => {d with decryptQueue := ring}
    let decrypted ← decryptPacket (← getRxSkb id)
    if ← branch .decWorkerDecrypted decrypted.isSome then
      let some d := decrypted | invariant "unreachable"
      setRxSkb id fun _ => d
      return some (← publishSource id .crypted)
    else return some (← publishSource id .dead)

def preparePrefix : MixedM (Option PeerId) := do
  match (← liftPrefix getDev).decryptQueue.consume with
  | (none, _) =>
    _ ← liftPrefix (branch .decWorkerConsumed false)
    return none
  | (some id, ring) =>
    _ ← liftPrefix (branch .decWorkerConsumed true)
    liftPrefix (modifyDev fun d => {d with decryptQueue := ring})
    let decrypted ← decryptPacketPrefix (← getRxSkbPrefix id)
    if ← liftPrefix (branch .decWorkerDecrypted decrypted.isSome) then
      let some d := decrypted | liftPrefix (invariant "unreachable")
      setRxSkbPrefix id fun _ => d
      return some (← publishPrefix id .crypted)
    else return some (← publishPrefix id .dead)

theorem prepare_erases : ErasesPrefix preparePrefix prepareSource := by
  unfold preparePrefix prepareSource
  repeat' first
    | with_reducible exact publish_erases _ _
    | with_reducible exact decryptPacketPrefix_erases _
    | with_reducible exact getRxSkbPrefix_erases _
    | with_reducible exact setRxSkbPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | split
    | (intro x; try dsimp only)

theorem prepare_preserves : PrefixPreserves AllocationInv LifetimeEvent.Safe preparePrefix := by
  unfold preparePrefix
  repeat' first
    | with_reducible exact publish_preserves _ _
    | with_reducible exact decryptPacketPrefix_allocation _
    | with_reducible exact decryptQueue_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getRx (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.setRx (fun _ => True) _ _)
    | with_reducible exact allocation_kernel _ getDev_sameKernel
    | with_reducible exact allocation_kernel _ (sameKernel_branch _ _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.bind
    | split
    | (intro x; try dsimp only)

def decryptSource (softirq irq : M Unit) : M Bool := do
  softirq
  match ← prepareSource with
  | none => return false
  | some pid => irq; peerPut (some pid); softirq; return true

def decryptWith (prepare : PrefixM E (Option PeerId)) (put : PeerId → PrefixM E Unit)
    (softirq irq : PrefixM E Unit) : PrefixM E Bool := do
  softirq
  match ← prepare with
  | none => return false
  | some pid => irq; put pid; softirq; return true

theorem decrypt_source (softirq irq : M Unit) : decryptSource softirq irq = decryptStep softirq irq := by
  unfold decryptSource prepareSource decryptStep
  simp only [enqueue_source, bind_assoc]
  apply bind_congr
  intro _
  apply bind_congr
  intro d
  cases hc : d.decryptQueue.consume with
  | mk item ring =>
    cases item with
    | none => simp only [bind_assoc, pure_bind]
    | some id =>
      simp only [bind_assoc]
      apply bind_congr
      intro _
      apply bind_congr
      intro _
      apply bind_congr
      intro pkt
      apply bind_congr
      intro decrypted
      apply bind_congr
      intro yes
      cases decrypted <;> cases yes
      all_goals simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      all_goals first | rfl | simp [invariant]

theorem decrypt_prefix (softirq irq : MixedM Unit) :
    decryptWith preparePrefix (fun pid => peerPutMixed (some pid)) softirq irq =
      decryptStepPrefix softirq irq := by
  unfold decryptWith preparePrefix decryptStepPrefix
  simp only [enqueue_prefix, bind_assoc]
  apply bind_congr
  intro _
  apply bind_congr
  intro d
  cases hc : d.decryptQueue.consume with
  | mk item ring =>
    cases item with
    | none => simp only [bind_assoc, pure_bind]
    | some id =>
      simp only [bind_assoc]
      apply bind_congr
      intro _
      apply bind_congr
      intro _
      apply bind_congr
      intro pkt
      apply bind_congr
      intro decrypted
      apply bind_congr
      intro yes
      cases decrypted <;> cases yes
      all_goals simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind]
      all_goals first | rfl | simp [invariant]

def encryptTail : MixedM IterResult :=
  encryptIterPrefix (fun p => liftPrefix (Env.checksumHelp p)) (pure ())
    (liftPrefix (Env.condResched .encryptWorker))

def encryptTailSource : M IterResult :=
  encryptIter Env.checksumHelp (pure ()) (Env.condResched .encryptWorker)

theorem encrypt_source (softirq : M Unit) :
    encryptIter Env.checksumHelp softirq (Env.condResched .encryptWorker) =
      (do softirq; encryptTailSource) := by
  simp only [encryptTailSource, encryptIter, workerIter, encryptStep, bind_assoc, pure_bind]

theorem encrypt_prefix (softirq : MixedM Unit) :
    encryptIterPrefix (fun p => liftPrefix (Env.checksumHelp p)) softirq
      (liftPrefix (Env.condResched .encryptWorker)) = (do softirq; encryptTail) := by
  simp only [encryptTail, encryptIterPrefix, workerIterPrefix, encryptStepPrefix, bind_assoc, pure_bind]

theorem encryptTail_erases : ErasesPrefix encryptTail encryptTailSource :=
  encryptIterPrefix_erases (fun _ => erasesPrefix_lift _) (erasesPrefix_pure ()) (erasesPrefix_lift _)

theorem encryptTail_preserves : PrefixPreserves AllocationInv LifetimeEvent.Safe encryptTail :=
  encryptIterPrefix_allocation (PrefixPreserves.pure allocationAmbient.safe ())
    (allocation_kernel _ (condResched_sameKernel _))

end Leanux.Proofs.WG.Queues.RxWorkers
