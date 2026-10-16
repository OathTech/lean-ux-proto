import Leanux.Proofs.WG.Lifetimes.KeyMaintenance
import Leanux.Proofs.WG.Lifetimes.HandshakeSend
import Leanux.Proofs.WG.Lifetimes.AllowedIpsAccess
import Leanux.Proofs.Logged.PrefixBatch
import Leanux.WG.PeerRemove

/-! Complete peer-removal and inline workqueue-flush observations. Saved queue
and peer-list values are scalar IDs; each actual peer access resolves the current
store. peekUnit/resolveUnit inspect records and Ambient dispatch labels, not peers.
The finite drain keeps its original early returns, placeholder order and Stop.
No pending-work, reference-ownership, distinctness or drain-success premise is
used. These contracts do not cover the enclosing device/environment lifecycle. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def runFlushedSendWorkPrefix (pid : PeerId) : MixedM Unit := do
  liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})
  let p ← getPeerMixed pid
  if !p.handshakePending then liftWGPrefix (invariant "queued work without a pending flag")
  setPeerMixed pid {p with handshakePending := (← liftWGPrefix getDev).sendWorkQueue.contains pid}
  _ ← liftWGPrefix (hidden (.sectionStart .sendWorker))
  handshakeSendWorkerPrefix pid
  _ ← liftWGPrefix (hidden (.sectionStop .sendWorker))

def runFlushedClearWorkPrefix (pid : PeerId) : MixedM Unit := do
  liftWGPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
  _ ← liftWGPrefix (hidden (.sectionStart .clearPeerWorker))
  queuedExpiredZeroKeyMaterialPrefix pid
  _ ← liftWGPrefix (hidden (.sectionStop .clearPeerWorker))

def drainHandshakeSendWqPrefix (upTo : Option PeerId) : MixedM Unit := do
  for _ in [0:4096] do
    let d ← liftWGPrefix getDev
    if d.sendWorkQueue.isEmpty && d.clearWorkQueue.isEmpty then return
    match ← liftWGPrefix (peekUnit .sendWorker) with
    | some u =>
      let pid ← liftWGPrefix (resolveUnit .sendWorker u d.sendWorkQueue)
      runFlushedSendWorkPrefix pid
    | none =>
      match ← liftWGPrefix (peekUnit .clearPeerWorker) with
      | some u =>
        let pid ← liftWGPrefix (resolveUnit .clearPeerWorker u d.clearWorkQueue)
        runFlushedClearWorkPrefix pid
        if upTo == some pid then return
      | none =>
        if (← liftWGPrefix getAmbient).hidden.isSome then
          liftWGPrefix (throw (.hidden s!"a flush of handshake_send_wq must run queued work ({d.sendWorkQueue.length} send, {d.clearWorkQueue.length} clear items), but no section names it"))
        match d.sendWorkQueue.head?, d.clearWorkQueue.head? with
        | some pid, _ => runFlushedSendWorkPrefix pid
        | none, some pid =>
          runFlushedClearWorkPrefix pid
          if upTo == some pid then return
        | none, none => return
  liftWGPrefix (invariant "handshake_send_wq did not drain")

def timersStopPrefix (pid : PeerId) : MixedM Unit := do
  for t in PeerTimer.all do delTimerPrefix pid t
  if (← liftWGPrefix getDev).clearWorkQueue.contains pid then drainHandshakeSendWqPrefix (some pid)

def peerRemoveAfterDeadPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftWGPrefix (branch .peerRemoveNotDead !(← getPeerMixed pid).isDead) then
    liftWGPrefix (unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)")
  keypairsClearPrefix pid
  timersStopPrefix pid
  let d ← liftWGPrefix getDev
  if !d.encryptQueue.empty || !d.decryptQueue.empty || !d.txWorkQueue.isEmpty
      || d.peers.toList.any (·.2.napiScheduled) then
    liftWGPrefix (unsupported "crypt work queued at a peer removal (peer.c:116-120 would run it: W3b)")
  drainHandshakeSendWqPrefix none
  if (← liftWGPrefix getDev).numPeers == 0 then liftWGPrefix (invariant "--num_peers below zero")
  liftWGPrefix (modifyDev fun d => {d with numPeers := d.numPeers - 1})
  peerPutMixed (some pid)

def peerRemovePrefix (peer : Option PeerId) : MixedM Unit := do
  if ← liftWGPrefix (branch .peerRemoveNull peer.isNone) then return
  let some pid := peer | liftWGPrefix (invariant "unreachable")
  peerMakeDeadPrefix pid
  peerRemoveAfterDeadPrefix pid

def peerRemoveAllPrefix : MixedM Unit := do
  freeAllowedIpsPrefix
  let dead := (← liftWGPrefix getDev).peerList
  for pid in dead do
    _ ← liftWGPrefix (branch .peerRemoveAllIter1 true)
    peerMakeDeadPrefix pid
  _ ← liftWGPrefix (branch .peerRemoveAllIter1 false)
  for pid in dead do
    _ ← liftWGPrefix (branch .peerRemoveAllIter2 true)
    peerRemoveAfterDeadPrefix pid
  _ ← liftWGPrefix (branch .peerRemoveAllIter2 false)

theorem runFlushedSendWorkPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (runFlushedSendWorkPrefix pid) (runFlushedSendWork pid) := by
  unfold runFlushedSendWorkPrefix runFlushedSendWork
  repeat' first
    | with_reducible exact handshakeSendWorkerPrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem runFlushedClearWorkPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (runFlushedClearWorkPrefix pid) (runFlushedClearWork pid) := by
  unfold runFlushedClearWorkPrefix runFlushedClearWork
  repeat' first
    | with_reducible exact queuedExpiredZeroKeyMaterialPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)

theorem drainHandshakeSendWqPrefix_erases (upTo : Option PeerId) :
    ErasesStatePrefix (drainHandshakeSendWqPrefix upTo) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWqPrefix drainHandshakeSendWq
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | with_reducible exact runFlushedSendWorkPrefix_erases _
    | with_reducible exact runFlushedClearWorkPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals try simp_all
  all_goals subst_vars
  all_goals
    repeat' first
      | with_reducible exact runFlushedSendWorkPrefix_erases _
      | with_reducible exact runFlushedClearWorkPrefix_erases _
      | exact erasesStatePrefix_lift _
      | with_reducible exact erasesStatePrefix_pure _
      | with_reducible apply erasesStatePrefix_bind
      | (with_reducible intro x; try dsimp only)

theorem timersStopPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (timersStopPrefix pid) (timersStop pid) := by
  unfold timersStopPrefix timersStop
  repeat' first
    | with_reducible exact delTimerPrefix_erases _ _
    | with_reducible exact drainHandshakeSendWqPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem peerRemoveAfterDeadPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (peerRemoveAfterDeadPrefix pid) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDeadPrefix peerRemoveAfterDead
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact keypairsClearPrefix_erases _
    | with_reducible exact timersStopPrefix_erases _
    | with_reducible exact drainHandshakeSendWqPrefix_erases _
    | with_reducible exact peerPutMixed_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem peerRemovePrefix_erases (peer : Option PeerId) :
    ErasesStatePrefix (peerRemovePrefix peer) (peerRemove peer) := by
  unfold peerRemovePrefix peerRemove
  cases peer <;> simp only
  all_goals
    repeat' first
      | with_reducible exact peerMakeDeadPrefix_erases _
      | with_reducible exact peerRemoveAfterDeadPrefix_erases _
      | exact erasesStatePrefix_lift _
      | with_reducible exact erasesStatePrefix_pure _
      | with_reducible apply erasesStatePrefix_bind
      | (with_reducible split)
      | (with_reducible intro x; try dsimp only)

theorem peerRemoveAllPrefix_erases : ErasesStatePrefix peerRemoveAllPrefix peerRemoveAll := by
  unfold peerRemoveAllPrefix peerRemoveAll
  repeat' first
    | with_reducible exact freeAllowedIpsPrefix_erases
    | with_reducible exact peerMakeDeadPrefix_erases _
    | with_reducible exact peerRemoveAfterDeadPrefix_erases _
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_forIn
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

/-- Independent lower-call and scalar bookkeeping contracts. They impose no
queue progress, pending-work consistency or saved-reference credit condition. -/
structure PeerRemovalContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  socket : SocketContracts I
  indexInsert : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (WG.indexInsert owner)))
  indexRemove : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (WG.indexRemove owner)))
  keypairPut : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now)
  allowedIps : AllowedIpsContracts I
  sendErase : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}))
  clearErase : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}))
  decrement : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev fun d => {d with numPeers := d.numPeers - 1}))

theorem allocationPeerRemoval : PeerRemovalContracts AllocationInv := by
  have indexInsertAllocation (owner : IndexOwner) :
      StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
        (liftWGPrefix (liftIndex (indexInsert owner))) := by
    apply StatePrefixEnsures.lift _ (fun h w _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    have hp : Hoare (liftIndex (indexInsert owner)) (AllocationInv h) (fun _ => AllocationInv h) := by
      apply hoare_liftIndex
      intro g d table hg hd
      apply hg.congr
      · unfold identityView Peers.snapshot keypairResidents packetResidents
        simp [hd]
      · simp [allocationMetadata, deviceAllocationMetadata, hd]
    exact (hoare_iff_run_ambient _ _ _).mp hp w ambient x v ambient' hi hr
  refine ⟨allocationSocket, indexInsertAllocation, indexRemove_allocation,
    keypairPutPrefix_allocation, allocationAllowedIps, ?_, ?_, ?_⟩
  · intro pid
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl
  · intro pid
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl
  · apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    cases hr
    apply hi.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl

structure ProductPeerRemovalContracts (I : List LifetimeEvent → World → Prop) : Prop where
  socket : ProductSocketContracts I
  indexInsert : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (WG.indexInsert owner))))
  indexRemove : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (WG.indexRemove owner))))
  keypairPut : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now))
  allowedIps : ProductAllowedIpsContracts I
  sendErase : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})))
  clearErase : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})))
  decrement : PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with numPeers := d.numPeers - 1})))


private theorem removal_forIn {α β : Type} (c : AmbientContracts I) (xs : List α) (init : β)
    (f : α → β → MixedM (ForInStep β))
    (hf : ∀ x b, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (f x b)) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (forIn xs init f) :=
  StatePrefixEnsures.forInInvariant xs init f (fun _ h w _ => I h w) LifetimeEvent.Safe
    (fun _ h w _ hi => c.safe h w hi) hf

private theorem removal_lift_forIn (xs : List α) (init : β)
    (f : α → β → MixedM (ForInStep β)) :
    liftWGObserver (forIn xs init f) = forIn xs init (fun x b => liftWGObserver (f x b)) := by
  induction xs generalizing init with
  | nil => simp only [List.forIn_nil, liftWGObserver_pure]
  | cons x xs ih =>
    simp only [List.forIn_cons, liftWGObserver_bind]
    congr 1
    funext step
    cases step <;> simp only [liftWGObserver_pure, ih]

theorem runFlushedSendWorkPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (runFlushedSendWorkPrefix pid) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold runFlushedSendWorkPrefix
  apply StatePrefixEnsures.bind (r.sendErase pid)
  intro _
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply StatePrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  have tail : AmbientSpec I (fun v => True ∧ v.1.slots pid = some p.internalId)
      (do
        let d ← liftWGPrefix getDev
        setPeerMixed pid {p with handshakePending := d.sendWorkQueue.contains pid}
        _ ← liftWGPrefix (hidden (.sectionStart .sendWorker))
        handshakeSendWorkerPrefix pid
        _ ← liftWGPrefix (hidden (.sectionStop .sendWorker))) (fun _ _ => True) := by
    change StatePrefixEnsures _ _ _ _
    with_reducible apply StatePrefixEnsures.bind (c.store (fun v => True ∧ v.1.slots pid = some p.internalId) getDev getDev_sameWGStore)
    intro d
    apply StatePrefixEnsures.bind (c.setPeer (fun _ => True) pid {p with handshakePending := d.sendWorkQueue.contains pid})
    intro _
    apply StatePrefixEnsures.bind (ambient (fun _ => True) (AmbientM.hidden _))
    intro _
    apply StatePrefixEnsures.bind (StatePrefixEnsures.consequence (Q' := fun _ h w _ => I h w ∧ True)
      (handshakeSendWorkerPrefix_preserves c r.socket r.indexInsert pid)
      (fun _ _ _ hi => hi.1) (fun _ _ _ _ hi => ⟨hi, True.intro⟩))
    intro _
    apply StatePrefixEnsures.bind (ambient (fun _ => True) (AmbientM.hidden _))
    intro _
    exact c.pure (fun _ => True) ()
  dsimp only
  split
  · exact StatePrefixEnsures.bind (ambient
      (fun v => True ∧ v.1.slots pid = some p.internalId)
      (AmbientM.invariant (α := Unit) "queued work without a pending flag")) (fun _ => tail)
  · exact tail

theorem runFlushedClearWorkPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (runFlushedClearWorkPrefix pid) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold runFlushedClearWorkPrefix
  with_reducible apply StatePrefixEnsures.bind (r.clearErase pid)
  intro _
  apply StatePrefixEnsures.bind (AmbientContracts.drop (ambient (fun _ => True) (AmbientM.hidden _)))
  intro _
  apply StatePrefixEnsures.bind (queuedExpiredZeroKeyMaterialPrefix_preserves c r.indexRemove r.keypairPut pid)
  intro _
  apply StatePrefixEnsures.bind (AmbientContracts.drop (ambient (fun _ => True) (AmbientM.hidden _)))
  intro _
  exact StatePrefixEnsures.pure () (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)

theorem drainHandshakeSendWqPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (upTo : Option PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (drainHandshakeSendWqPrefix upTo) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold drainHandshakeSendWqPrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (maintenance_head runFlushedSendWorkPrefix; exact runFlushedSendWorkPrefix_preserves c r _)
    | (maintenance_head runFlushedClearWorkPrefix; exact runFlushedClearWorkPrefix_preserves c r _)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact AmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_head; exact AmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply removal_forIn c; intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem timersStopPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (timersStopPrefix pid) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold timersStopPrefix
  repeat' first
    | (maintenance_head delTimerPrefix; exact AmbientContracts.drop (delTimerPrefix_spec c (fun _ => True) _ _))
    | (maintenance_head drainHandshakeSendWqPrefix; exact drainHandshakeSendWqPrefix_preserves c r _)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact AmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_head; exact AmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply removal_forIn c; intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem peerRemoveAfterDeadPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (peerRemoveAfterDeadPrefix pid) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold peerRemoveAfterDeadPrefix
  repeat' first
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head keypairsClearPrefix; exact keypairsClearPrefix_preserves_ambient c r.keypairPut _)
    | (maintenance_head timersStopPrefix; exact timersStopPrefix_preserves c r _)
    | (maintenance_head drainHandshakeSendWqPrefix; exact drainHandshakeSendWqPrefix_preserves c r _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_lift_action_head modifyDev; exact r.decrement)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact AmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_head; exact AmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply removal_forIn c; intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem peerRemovePrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (peer : Option PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (peerRemovePrefix peer) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold peerRemovePrefix
  repeat' first
    | (maintenance_head peerMakeDeadPrefix; exact peerMakeDeadPrefix_preserves c r.allowedIps _)
    | (maintenance_head peerRemoveAfterDeadPrefix; exact peerRemoveAfterDeadPrefix_preserves c r _)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact AmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_head; exact AmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply removal_forIn c; intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem peerRemoveAllPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (peerRemoveAllPrefix) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change StatePrefixEnsures _ _ _ _
  unfold peerRemoveAllPrefix
  repeat' first
    | (maintenance_head freeAllowedIpsPrefix; exact freeAllowedIpsPrefix_preserves c r.allowedIps.nodes)
    | (maintenance_head peerMakeDeadPrefix; exact peerMakeDeadPrefix_preserves c r.allowedIps _)
    | (maintenance_head peerRemoveAfterDeadPrefix; exact peerRemoveAfterDeadPrefix_preserves c r _)
    | (maintenance_lift_action_head getDev; exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact AmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact AmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_lift_head; exact AmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply removal_forIn c; intro x b; change StatePrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem runFlushedSendWorkPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductPeerRemovalContracts I)
    (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (runFlushedSendWorkPrefix pid)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold runFlushedSendWorkPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  apply PrefixPreserves.bind (r.sendErase pid)
  intro _
  apply ProductAmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  have tail : ProductAmbientSpec I (fun v => True ∧ v.1.slots pid = some p.internalId)
      (liftWGObserver (do
        let d ← liftWGPrefix getDev
        setPeerMixed pid {p with handshakePending := d.sendWorkQueue.contains pid}
        _ ← liftWGPrefix (hidden (.sectionStart .sendWorker))
        handshakeSendWorkerPrefix pid
        _ ← liftWGPrefix (hidden (.sectionStop .sendWorker)))) (fun _ _ => True) := by
    simp only [liftWGObserver_bind]
    change PrefixEnsures _ _ _ _
    with_reducible apply PrefixEnsures.bind (c.nativeStore (fun v => True ∧ v.1.slots pid = some p.internalId) getDev getDev_sameWGStore)
    intro d
    apply PrefixEnsures.bind (c.setPeer (fun _ => True) pid {p with handshakePending := d.sendWorkQueue.contains pid})
    intro _
    apply PrefixEnsures.bind (ambient (fun _ => True) (AmbientM.hidden _))
    intro _
    apply PrefixEnsures.bind (PrefixEnsures.consequence (Q' := fun _ h w => I h w ∧ True)
      (show PrefixEnsures I LifetimeEvent.Safe
        (liftWGObserver (handshakeSendWorkerPrefix pid)) (fun _ => I) from
        handshakeSendWorkerPrefix_preserves_product c r.socket r.indexInsert pid)
      (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩))
    intro _
    apply PrefixEnsures.bind (ambient (fun _ => True) (AmbientM.hidden _))
    intro _
    exact c.pure (fun _ => True) ()
  dsimp only
  try simp only [apply_ite, liftWGObserver_bind]
  split
  · apply PrefixEnsures.bind (ambient
      (fun v => True ∧ v.1.slots pid = some p.internalId)
      (AmbientM.invariant (α := Unit) "queued work without a pending flag"))
    intro _
    simpa only [liftWGObserver_bind, liftWGObserver_pure] using tail
  · simpa only [liftWGObserver_bind, liftWGObserver_pure] using tail

theorem runFlushedClearWorkPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductPeerRemovalContracts I)
    (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (runFlushedClearWorkPrefix pid)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold runFlushedClearWorkPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure]
  apply PrefixPreserves.bind (r.clearErase pid)
  intro _
  apply PrefixEnsures.bind (ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.hidden _)))
  intro _
  apply PrefixEnsures.bind (queuedExpiredZeroKeyMaterialPrefix_preserves_product c r.indexRemove r.keypairPut pid)
  intro _
  apply PrefixEnsures.bind (ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.hidden _)))
  intro _
  exact PrefixPreserves.pure c.safe ()

theorem drainHandshakeSendWqPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductPeerRemovalContracts I)
    (upTo : Option PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (drainHandshakeSendWqPrefix upTo)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold drainHandshakeSendWqPrefix
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite, removal_lift_forIn]
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [removal_lift_forIn] | rw [apply_ite])
    | (maintenance_head runFlushedSendWorkPrefix; exact runFlushedSendWorkPrefix_preserves_product c r _)
    | (maintenance_head runFlushedClearWorkPrefix; exact runFlushedClearWorkPrefix_preserves_product c r _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact ProductAmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head liftWGPrefix; exact ProductAmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem timersStopPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductPeerRemovalContracts I)
    (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (timersStopPrefix pid)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold timersStopPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite, removal_lift_forIn]
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [removal_lift_forIn] | rw [apply_ite])
    | (maintenance_head delTimerPrefix; exact ProductAmbientContracts.drop (delTimerPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head drainHandshakeSendWqPrefix; exact drainHandshakeSendWqPrefix_preserves_product c r _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact ProductAmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head liftWGPrefix; exact ProductAmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem peerRemoveAfterDeadPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductPeerRemovalContracts I)
    (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (peerRemoveAfterDeadPrefix pid)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold peerRemoveAfterDeadPrefix
  simp only [liftWGObserver_bind, apply_ite]
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [removal_lift_forIn] | rw [apply_ite])
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (ProductAmbientContracts.forget (c.getPeer (fun _ => True) _) (fun _ _ hi => hi.1)))
    | (maintenance_head keypairsClearPrefix; exact keypairsClearPrefix_preserves_product c r.keypairPut _)
    | (maintenance_head timersStopPrefix; exact timersStopPrefix_preserves_product c r _)
    | (maintenance_head drainHandshakeSendWqPrefix; exact drainHandshakeSendWqPrefix_preserves_product c r _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_lift_action_head modifyDev; exact r.decrement)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact ProductAmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head liftWGPrefix; exact ProductAmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem peerRemovePrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductPeerRemovalContracts I)
    (peer : Option PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (peerRemovePrefix peer)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold peerRemovePrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [removal_lift_forIn] | rw [apply_ite])
    | (maintenance_head peerMakeDeadPrefix; exact peerMakeDeadPrefix_preserves_product c r.allowedIps _)
    | (maintenance_head peerRemoveAfterDeadPrefix; exact peerRemoveAfterDeadPrefix_preserves_product c r _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact ProductAmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head liftWGPrefix; exact ProductAmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

theorem peerRemoveAllPrefix_preserves_product (c : ProductAmbientContracts I) (r : ProductPeerRemovalContracts I) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (peerRemoveAllPrefix)) := by
  have ambient {α : Type} (P : IdentityView → Prop) (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  change PrefixEnsures _ _ _ _
  unfold peerRemoveAllPrefix
  simp only [liftWGObserver_bind, liftWGObserver_pure, removal_lift_forIn]
  repeat' first
    | (first | rw [liftWGObserver_bind] | rw [liftWGObserver_pure] | rw [removal_lift_forIn] | rw [apply_ite])
    | (maintenance_head freeAllowedIpsPrefix; exact freeAllowedIpsPrefix_preserves_product c r.allowedIps.nodes)
    | (maintenance_head peerMakeDeadPrefix; exact peerMakeDeadPrefix_preserves_product c r.allowedIps _)
    | (maintenance_head peerRemoveAfterDeadPrefix; exact peerRemoveAfterDeadPrefix_preserves_product c r _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.branch _ _)))
    | (maintenance_lift_action_head peekUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.peekUnit _)))
    | (maintenance_lift_action_head resolveUnit; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.resolveUnit _ _ _)))
    | (maintenance_lift_action_head getAmbient; exact ProductAmbientContracts.drop (ambient (fun _ => True) (get : AmbientM Ambient)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.invariant _)))
    | (maintenance_lift_action_head unsupported; exact ProductAmbientContracts.drop (ambient (fun _ => True) (AmbientM.unsupported _)))
    | (maintenance_head liftWGPrefix; exact ProductAmbientContracts.drop (ambient (fun _ => True) (throw _)))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ c.safe; intro x b; change PrefixEnsures _ _ _ _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w))
    | maintenance_join_let
    | maintenance_join_use
    | consume_conditional
    | maintenance_reduce
    | (with_reducible split)
    | (maintenance_intro; try dsimp only)
    | contradiction

inductive PeerRemovalCall where
  | sendWork (pid : PeerId)
  | clearWork (pid : PeerId)
  | drain (upTo : Option PeerId)
  | stopTimers (pid : PeerId)
  | afterDead (pid : PeerId)
  | remove (peer : Option PeerId)
  | removeAll

namespace PeerRemovalCall

def original : PeerRemovalCall → WG.M Unit
  | .sendWork pid => runFlushedSendWork pid
  | .clearWork pid => runFlushedClearWork pid
  | .drain upTo => drainHandshakeSendWq upTo
  | .stopTimers pid => timersStop pid
  | .afterDead pid => peerRemoveAfterDead pid
  | .remove peer => peerRemove peer
  | .removeAll => peerRemoveAll

def observed : PeerRemovalCall → MixedM Unit
  | .sendWork pid => runFlushedSendWorkPrefix pid
  | .clearWork pid => runFlushedClearWorkPrefix pid
  | .drain upTo => drainHandshakeSendWqPrefix upTo
  | .stopTimers pid => timersStopPrefix pid
  | .afterDead pid => peerRemoveAfterDeadPrefix pid
  | .remove peer => peerRemovePrefix peer
  | .removeAll => peerRemoveAllPrefix

theorem erases (call : PeerRemovalCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | sendWork pid => exact runFlushedSendWorkPrefix_erases pid
  | clearWork pid => exact runFlushedClearWorkPrefix_erases pid
  | drain upTo => exact drainHandshakeSendWqPrefix_erases upTo
  | stopTimers pid => exact timersStopPrefix_erases pid
  | afterDead pid => exact peerRemoveAfterDeadPrefix_erases pid
  | remove peer => exact peerRemovePrefix_erases peer
  | removeAll => exact peerRemoveAllPrefix_erases

theorem preserves_ambient (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (call : PeerRemovalCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | sendWork pid => exact runFlushedSendWorkPrefix_preserves c r pid
  | clearWork pid => exact runFlushedClearWorkPrefix_preserves c r pid
  | drain upTo => exact drainHandshakeSendWqPrefix_preserves c r upTo
  | stopTimers pid => exact timersStopPrefix_preserves c r pid
  | afterDead pid => exact peerRemoveAfterDeadPrefix_preserves c r pid
  | remove peer => exact peerRemovePrefix_preserves c r peer
  | removeAll => exact peerRemoveAllPrefix_preserves c r

theorem preserves_ambient_product (c : ProductAmbientContracts I) (r : ProductPeerRemovalContracts I)
    (call : PeerRemovalCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | sendWork pid => exact runFlushedSendWorkPrefix_preserves_product c r pid
  | clearWork pid => exact runFlushedClearWorkPrefix_preserves_product c r pid
  | drain upTo => exact drainHandshakeSendWqPrefix_preserves_product c r upTo
  | stopTimers pid => exact timersStopPrefix_preserves_product c r pid
  | afterDead pid => exact peerRemoveAfterDeadPrefix_preserves_product c r pid
  | remove peer => exact peerRemovePrefix_preserves_product c r peer
  | removeAll => exact peerRemoveAllPrefix_preserves_product c r

theorem allocation (call : PeerRemovalCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationPeerRemoval

end PeerRemovalCall
end Leanux.Proofs.WG.Lifetimes
