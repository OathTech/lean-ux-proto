import Leanux.Proofs.WG.Lifetimes.DecryptWorker
import Leanux.Proofs.WG.Lifetimes.EncryptWorker
import Leanux.Proofs.WG.Lifetimes.AllocationAmbient
import Leanux.Proofs.WG.Queues.TxRingCuts
import Leanux.Proofs.Framing.Batch

/-! Source cuts around the encryption callback and RX publication.
The publication cut retains its resolved peer through the cached setter, then
returns the original numeric peer reference for the later IRQ and put. -/
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxWorkers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem bind_congr {m : Type → Type} [Monad m] (a : m α) (f g : α → m β)
    (h : ∀ x, f x = g x) : (a >>= f) = (a >>= g) :=
  congrArg (fun k => a >>= k) (funext h)

def publishSource (id : SkbId) (state : PacketState) : WG.M PeerId := do
  let pid ← IndexOwner.peerDeref (.keypair (← getRxSkb id).keypair)
  peerGet pid
  let p ← getPeer pid
  if !(p.rxQueue.all.contains id) then invariant "a decrypted packet that is not on its peer's rx_queue"
  setRxSkb id fun q => {q with state}
  setPeer pid {p with napiScheduled := true}
  return pid

def publishPrefix (id : SkbId) (state : PacketState) : MixedM PeerId := do
  let pid ← peerDerefPrefix (.keypair (← getRxSkbPrefix id).keypair)
  peerGetMixed pid
  let p ← getPeerMixed pid
  if !(p.rxQueue.all.contains id) then liftWGPrefix (invariant "a decrypted packet that is not on its peer's rx_queue")
  setRxSkbPrefix id fun q => {q with state}
  setPeerMixed pid {p with napiScheduled := true}
  return pid

theorem publish_erases (id : SkbId) (state : PacketState) :
    ErasesStatePrefix (publishPrefix id state) (publishSource id state) := by
  unfold publishPrefix publishSource
  repeat' first
    | with_reducible exact getRxSkbPrefix_erases _
    | with_reducible exact peerDerefPrefix_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setRxSkbPrefix_erases _ _
    | with_reducible exact setPeerMixed_erases _ _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem publish_preserves (id : SkbId) (state : PacketState) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (publishPrefix id state) := by
  unfold publishPrefix
  let c := allocationAmbient
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getRx (fun _ => True) id))
  intro pkt
  apply StatePrefixEnsures.bind (AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) (.keypair pkt.keypair)))
  intro pid
  apply StatePrefixEnsures.bind (c.peerGet pid)
  intro _
  have hget : StatePrefixEnsures (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (getPeerMixed pid)
      (fun p h w _ => AllocationInv h w ∧ (identityView w).1.slots pid = some p.internalId) :=
    (c.getPeer (fun _ => True) pid).consequence
      (fun _ _ _ hn => ⟨hn, True.intro⟩) (fun _ _ _ _ hn => ⟨hn.1, hn.2.2⟩)
  apply StatePrefixEnsures.bind hget
  intro p
  dsimp only
  have tail : StatePrefixEnsures
      (fun h w _ => AllocationInv h w ∧ (identityView w).1.slots pid = some p.internalId)
      LifetimeEvent.Safe
      (do setRxSkbPrefix id fun q => {q with state}
          setPeerMixed pid {p with napiScheduled := true}
          pure pid) (fun _ h w _ => AllocationInv h w) := by
    apply StatePrefixEnsures.bind (c.setRx (fun s => s.1.slots pid = some p.internalId) id _)
    intro _
    apply StatePrefixEnsures.bind ((c.setPeer (fun _ => True) pid
      {p with napiScheduled := true}).consequence
      (fun _ _ _ hn => ⟨hn.1, True.intro, hn.2⟩) (fun _ _ _ _ hn => hn.1))
    intro _
    exact StatePrefixEnsures.pure pid (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
  split
  · apply StatePrefixEnsures.bind (Q := fun (_ : Unit) h w _ =>
      AllocationInv h w ∧ (identityView w).1.slots pid = some p.internalId)
    · apply StatePrefixEnsures.lift _ (fun h w _ hn => c.safe h w hn.1)
      intro h w ambient x v ambient' hn hr
      cases hr
    · intro _; exact tail
  · exact tail

theorem enqueue_source (irq : Leanux.M Unit) (id : SkbId) (state : PacketState) :
    enqueuePerPeerRx irq id state =
      (do let pid ← liftWG (publishSource id state); irq; liftWG (peerPut (some pid))) := by
  unfold enqueuePerPeerRx publishSource
  simp only [liftWG_bind, bind_assoc]
  repeat' first
    | rfl
    | apply bind_congr
    | (with_reducible intro x; try dsimp only)
    | (split <;> simp only [liftWG_bind, liftWG_pure, bind_assoc, pure_bind])
    | (simp only [liftWG_bind, liftWG_pure, liftWG_ambient, bind_assoc, pure_bind]; done)

theorem enqueue_prefix (irq : PrefixM LifetimeEvent Unit) (id : SkbId) (state : PacketState) :
    enqueuePerPeerRxPrefix irq id state =
      (do let pid ← liftWGObserver (publishPrefix id state); irq;
          liftWGObserver (peerPutMixed (some pid))) := by
  unfold enqueuePerPeerRxPrefix publishPrefix
  simp only [liftWGObserver_bind, bind_assoc]
  repeat' first
    | rfl
    | apply bind_congr
    | (with_reducible intro x; try dsimp only)
    | split
    | (simp only [liftWGObserver_bind, liftWGObserver_pure,
        bind_assoc, pure_bind]; done)

def prepareSource : WG.M (Option PeerId) := do
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
  match (← liftWGPrefix getDev).decryptQueue.consume with
  | (none, _) =>
    _ ← liftWGPrefix (branch .decWorkerConsumed false)
    return none
  | (some id, ring) =>
    _ ← liftWGPrefix (branch .decWorkerConsumed true)
    liftWGPrefix (modifyDev fun d => {d with decryptQueue := ring})
    let decrypted ← decryptPacketPrefix (← getRxSkbPrefix id)
    if ← liftWGPrefix (branch .decWorkerDecrypted decrypted.isSome) then
      let some d := decrypted | liftWGPrefix (invariant "unreachable")
      setRxSkbPrefix id fun _ => d
      return some (← publishPrefix id .crypted)
    else return some (← publishPrefix id .dead)

theorem prepare_erases : ErasesStatePrefix preparePrefix prepareSource := by
  unfold preparePrefix prepareSource
  repeat' first
    | with_reducible exact publish_erases _ _
    | with_reducible exact decryptPacketPrefix_erases _
    | with_reducible exact getRxSkbPrefix_erases _
    | with_reducible exact setRxSkbPrefix_erases _ _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem prepare_preserves : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe preparePrefix := by
  unfold preparePrefix
  repeat' first
    | with_reducible exact publish_preserves _ _
    | with_reducible exact decryptPacketPrefix_allocation _
    | with_reducible exact decryptQueue_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getRx (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.setRx (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.store (fun _ => True) getDev getDev_sameWGStore)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | split
    | (with_reducible intro x; try dsimp only)

def decryptSource (softirq irq : Leanux.M Unit) : Leanux.M Bool := do
  softirq
  match ← liftWG prepareSource with
  | none => return false
  | some pid => irq; liftWG (peerPut (some pid)); softirq; return true

def decryptWith (prepare : PrefixM E (Option PeerId)) (put : PeerId → PrefixM E Unit)
    (softirq irq : PrefixM E Unit) : PrefixM E Bool := do
  softirq
  match ← prepare with
  | none => return false
  | some pid => irq; put pid; softirq; return true

theorem decrypt_source (softirq irq : Leanux.M Unit) : decryptSource softirq irq = decryptStep softirq irq := by
  unfold decryptSource prepareSource decryptStep
  simp only [enqueue_source, liftWG_bind, bind_assoc]
  apply bind_congr
  intro _
  apply bind_congr
  intro d
  cases hc : d.decryptQueue.consume with
  | mk item ring =>
    cases item with
    | none => simp only [liftWG_bind, liftWG_pure,
        bind_assoc, pure_bind] <;> rfl
    | some id =>
      simp only [liftWG_bind,
        bind_assoc]
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
      all_goals simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals first | rfl | simp only [liftWG_bind, liftWG_pure,
        bind_assoc, pure_bind]
      all_goals first | rfl | simp [invariant, liftWG_bind, liftWG_pure, liftWG_ambient,
        liftWGObserver_bind, liftWGObserver_lift, liftWGObserver_pure]

theorem decrypt_prefix (softirq irq : PrefixM LifetimeEvent Unit) :
    decryptWith (liftWGObserver preparePrefix) (fun pid => liftWGObserver (peerPutMixed (some pid))) softirq irq =
      decryptStepPrefix softirq irq := by
  unfold decryptWith preparePrefix decryptStepPrefix
  simp only [enqueue_prefix, liftWGObserver_bind, liftWGObserver_lift,
    bind_assoc]
  apply bind_congr
  intro _
  apply bind_congr
  intro d
  cases hc : d.decryptQueue.consume with
  | mk item ring =>
    cases item with
    | none => simp only [liftWGObserver_bind,
        liftWGObserver_lift, liftWGObserver_pure, bind_assoc, pure_bind] <;> rfl
    | some id =>
      simp only [liftWGObserver_bind,
        liftWGObserver_lift, bind_assoc]
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
      all_goals simp only [Bool.false_eq_true, ↓reduceIte]
      all_goals first | rfl | simp only [
        liftWGObserver_bind, liftWGObserver_pure, bind_assoc, pure_bind]
      all_goals first | rfl | simp [invariant, liftWG_bind, liftWG_pure, liftWG_ambient,
        liftWGObserver_bind, liftWGObserver_lift, liftWGObserver_pure]

/-- The continuation begins after the actual consume/install and the callback.
It retains the consumed item even when the callback changes the current ring. -/
def encryptStepTailSource (item : Option (List SkbId)) : Leanux.M Bool := do
  _ ← branch .encWorkerConsumed item.isSome
  match item with
  | none => return false
  | some first =>
    let some headId := first.head? | invariant "an empty ring item"
    let head ← getTxSkb headId
    -- skb_list_walk_safe(first, skb, next): each skb encrypted in place
    -- (the store, review 4.2)
    let mut state := PacketState.crypted
    for id in first do
      _ ← branch .encWorkerSkbIterate true
      let encrypted ← encryptPacket Env.checksumHelp head.keypair (← getTxSkb id)
      if ← branch .encWorkerEncrypted encrypted.isSome then
        -- wg_reset_packet(skb, true) (a cut point)
        setTxSkb id fun p => { p with bytes := encrypted.getD [] }
      else
        state := .dead   -- break
        break
    if state == .crypted then _ ← branch .encWorkerSkbIterate false
    enqueuePerPeerTx first state
    return true

def encryptStepTail (item : Option (List SkbId)) : PrefixM LifetimeEvent Bool := do
  _ ← liftPrefix (branch .encWorkerConsumed item.isSome)
  match item with
  | none => return false
  | some first =>
    let some headId := first.head? | liftPrefix (invariant "an empty ring item")
    let head ← liftWGObserver (getTxSkbPrefix headId)
    let mut state := PacketState.crypted
    for id in first do
      _ ← liftPrefix (branch .encWorkerSkbIterate true)
      let encrypted ← encryptPacketPrefix (fun p => liftPrefix (Env.checksumHelp p)) head.keypair (← liftWGObserver (getTxSkbPrefix id))
      if ← liftPrefix (branch .encWorkerEncrypted encrypted.isSome) then
        liftWGObserver (setTxSkbPrefix id fun p => {p with bytes := encrypted.getD []})
      else
        state := .dead
        break
    if state == .crypted then _ ← liftPrefix (branch .encWorkerSkbIterate false)
    liftWGObserver (enqueuePerPeerTxPrefix first state)
    return true

def encryptTail (item : Option (List SkbId)) : PrefixM LifetimeEvent IterResult :=
  workerIterPrefix .encryptWorker none (encryptStepTail item)
    (do liftPrefix (branch .encWorkerNeedResched (← liftPrefix (Env.condResched .encryptWorker))))

def encryptTailSource (item : Option (List SkbId)) : Leanux.M IterResult :=
  workerIter .encryptWorker none (encryptStepTailSource item)
    (do branch .encWorkerNeedResched (← Env.condResched .encryptWorker))

theorem encrypt_source (softirq : Leanux.M Unit) :
    encryptIter Env.checksumHelp softirq (Env.condResched .encryptWorker) =
      (do let item ← liftWG TxRing.pollSource; softirq; encryptTailSource item) := by
  simp only [encryptTailSource, encryptStepTailSource, TxRing.pollSource, encryptIter,
    workerIter, encryptStep, encryptRingPoll, liftWG_bind, liftWG_pure, bind_assoc, pure_bind]
  rfl

theorem encrypt_prefix (softirq : PrefixM LifetimeEvent Unit) :
    encryptIterPrefix (fun p => liftPrefix (Env.checksumHelp p)) softirq
      (liftPrefix (Env.condResched .encryptWorker)) =
      (do let item ← liftWGObserver (liftWGPrefix TxRing.pollSource); softirq; encryptTail item) := by
  have lb {α β : Type} (a : WG.M α) (f : α → WG.M β) :
      liftWGPrefix (a >>= f) =
        (liftWGPrefix a >>= fun x => liftWGPrefix (f x) : MixedM β) := by
    funext w ambient h
    change runStatePrefix (liftWGPrefix (a >>= f)) w ambient h =
      runStatePrefix (liftWGPrefix a >>= fun x => liftWGPrefix (f x)) w ambient h
    rw [runStatePrefix_bind]
    simp only [liftWGPrefix, runStatePrefix_lift, StateT.run_bind]
    cases (a.run w).run ambient <;> rfl
  have lp {α : Type} (x : α) : liftWGPrefix (pure x) = (pure x : MixedM α) := rfl
  simp only [encryptTail, encryptStepTail, TxRing.pollSource, encryptIterPrefix,
    workerIterPrefix, encryptStepPrefix, lb, lp,
    liftWGObserver_bind, liftWGObserver_pure, bind_assoc, pure_bind]
  rfl

theorem encryptTail_erases (item : Option (List SkbId)) :
    ErasesPrefix (encryptTail item) (encryptTailSource item) := by
  apply workerIterPrefix_erases
  · unfold encryptStepTail encryptStepTailSource
    repeat' first
      | exact encryptPacketPrefix_erases (fun _ => erasesPrefix_lift _) _ _
      | exact liftWGObserver_erases (getTxSkbPrefix_erases _)
      | exact liftWGObserver_erases (setTxSkbPrefix_erases _ _)
      | exact liftWGObserver_erases (enqueuePerPeerTxPrefix_erases _ _)
      | exact erasesPrefix_lift _
      | exact erasesPrefix_pure _
      | apply erasesPrefix_forIn
      | apply erasesPrefix_bind
      | apply erasesPrefix_ite
      | split
      | (with_reducible intro x; try dsimp only)
  · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _)

theorem encryptTail_preserves (item : Option (List SkbId)) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (encryptTail item) := by
  let c := ProductAmbientContracts.ofNative allocationAmbient
  let t := ProductTxContracts.ofNative allocationTx
  apply workerIterPrefix_preserves _ _ c.safe
  · unfold encryptStepTail
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro _
    cases item with
    | none => exact PrefixPreserves.pure c.safe _
    | some first =>
      dsimp only
      cases he : first.head? with
      | none => exact ProductAmbientContracts.drop (c.invariant (fun _ => True) _)
      | some headId =>
        repeat' first
          | with_reducible exact encryptPacketPrefix_allocation _ _
          | with_reducible exact enqueuePerPeerTxPrefix_preserves_product c t _ _
          | with_reducible exact ProductAmbientContracts.drop (t.get (fun _ => True) _)
          | with_reducible exact ProductAmbientContracts.drop (t.set (fun _ => True) _ _)
          | with_reducible exact ProductAmbientContracts.drop (c.branch (fun _ => True) _ _)
          | with_reducible exact PrefixPreserves.pure c.safe _
          | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
          | with_reducible apply PrefixPreserves.bind
          | with_reducible apply PrefixPreserves.ite
          | (with_reducible split)
          | (with_reducible intro x; try dsimp only)
  · apply PrefixPreserves.bind (ProductAmbientContracts.drop
      (c.store (fun _ => True) _ (condResched_sameKernel _)))
    intro _
    exact ProductAmbientContracts.drop (c.branch (fun _ => True) _ _)

end Leanux.Proofs.WG.Queues.RxWorkers
