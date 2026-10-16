import Leanux.Proofs.WG.Lifetimes.MaintenanceTimers

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Receive-side maintenance through queued handshake initiation. Queue updates
are explicit ambient contracts; no worker execution or time bound is asserted. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def sendQueuedHandshakeInitiationPrefix (pid : PeerId) (isRetry : Bool) : MixedM Unit := do
  if ← liftWGPrefix (branch .queuedNotRetry !isRetry) then
    modifyPeerKeysPrefix pid fun p => {p with timerHandshakeAttempts := 0}
  let p ← getPeerMixed pid
  if ← liftWGPrefix (branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT not) then return
  if ← liftWGPrefix (branch .queuedDead p.isDead) then return
  peerGetMixed pid
  if ← liftWGPrefix (branch .queuedAlreadyQueued (p.handshakePending && !(← liftWGPrefix (peekQueuedUnit .sendWorker pid)))) then
    peerPutMixed (some pid)
    return
  modifyPeerKeysPrefix pid fun p => {p with handshakePending := true}
  liftWGPrefix (recordQueued .sendWorker pid)
  liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})

theorem sendQueuedHandshakeInitiationPrefix_erases (pid : PeerId) (retry : Bool) :
    ErasesStatePrefix (sendQueuedHandshakeInitiationPrefix pid retry) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiationPrefix sendQueuedHandshakeInitiation
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro retryGuard
  split <;> first
    | (simp only [modifyPeerKeysPrefix, bind_assoc]
       apply erasesStatePrefix_bind (getPeerMixed_erases _)
       intro p
       apply erasesStatePrefix_bind (setPeerMixed_erases _ _)
       intro _)
    | skip
  all_goals
    apply erasesStatePrefix_bind (getPeerMixed_erases _)
    intro p
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro fresh
    split
    · exact erasesStatePrefix_pure _
    · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro dead
      split
      · exact erasesStatePrefix_pure _
      · apply erasesStatePrefix_bind (peerGetMixed_erases _)
        intro _
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro pendingWasCleared
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro queued
        split
        · exact erasesStatePrefix_bind (peerPutMixed_erases _) (fun _ => erasesStatePrefix_pure _)
        · try simp only [modifyPeerKeysPrefix, bind_assoc]
          exact erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ =>
            erasesStatePrefix_bind (setPeerMixed_erases _ _) (fun _ =>
              erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
                erasesStatePrefix_lift _)))

theorem sendQueuedHandshakeInitiationPrefix_preserves_ambient (c : AmbientContracts I)
    (hq : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
    (pid : PeerId) (retry : Bool) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (sendQueuedHandshakeInitiationPrefix pid retry) := by
  unfold sendQueuedHandshakeInitiationPrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro notRetry
  have tail : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (do
      let p ← getPeerMixed pid
      if ← liftWGPrefix (branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT not) then return
      if ← liftWGPrefix (branch .queuedDead p.isDead) then return
      peerGetMixed pid
      if ← liftWGPrefix (branch .queuedAlreadyQueued
          (p.handshakePending && !(← liftWGPrefix (peekQueuedUnit .sendWorker pid)))) then
        peerPutMixed (some pid)
        return
      modifyPeerKeysPrefix pid fun p => {p with handshakePending := true}
      liftWGPrefix (recordQueued .sendWorker pid)
      liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})) := by
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) pid))
    intro p
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _
      ((branchExpired_sameWGWorld _ _ _ _).factor wgStoreView)))
    intro fresh
    split
    · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro dead
      split
      · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
      · apply StatePrefixEnsures.bind (c.peerGet pid)
        intro _
        apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _
          (fun initial => hoare_liftAmbient (AmbientM.peekQueuedUnit .sendWorker pid)
            (fun w => wgStoreView w = initial))))
        intro pendingWasCleared
        apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        intro queued
        split
        · exact StatePrefixEnsures.bind (c.peerPut _) (fun _ =>
            StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
        · apply StatePrefixEnsures.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
            (fun p => {p with handshakePending := true}) (fun _ => rfl)))
          intro _
          apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _
            (fun initial => hoare_liftAmbient (AmbientM.recordQueued .sendWorker pid)
              (fun w => wgStoreView w = initial))))
          intro _
          exact hq pid
  split
  · exact StatePrefixEnsures.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
      (fun p => {p with timerHandshakeAttempts := 0}) (fun _ => rfl))) (fun _ => tail)
  · exact tail

/-- Actual short-circuit composition, used only where the original second
operand is an explicit delayed do block. -/
def andPrefix {m : Type → Type} [Monad m] (a b : m Bool) : m Bool := do
  if ← a then b else pure false

theorem andPrefix_erases {E S : Type} {a b : PrefixT E S Bool}
    {a' b' : StateT S (Except Stop) Bool}
    (ha : ErasesPrefix a a') (hb : ErasesPrefix b b') :
    ErasesPrefix (andPrefix a b) (andPrefix a' b') := by
  apply erasesPrefix_bind ha
  intro first
  split
  · exact hb
  · exact erasesPrefix_pure _

theorem andPrefix_preserves {S : Type} {I : List LifetimeEvent → S → Prop}
    {a b : PrefixT LifetimeEvent S Bool}
    (safe : ∀ h w, I h w → LifetimeEvent.Safe h)
    (ha : PrefixPreserves I LifetimeEvent.Safe a) (hb : PrefixPreserves I LifetimeEvent.Safe b) :
    PrefixPreserves I LifetimeEvent.Safe (andPrefix a b) := by
  apply PrefixPreserves.bind ha
  intro first
  split
  · exact hb
  · exact PrefixPreserves.pure safe _

theorem andPrefix_erases_state {E Outer Inner : Type}
    {a b : StatePrefixT E Outer Inner Bool}
    {a' b' : StateT Outer (StateT Inner (Except Stop)) Bool}
    (ha : ErasesStatePrefix a a') (hb : ErasesStatePrefix b b') :
    ErasesStatePrefix (andPrefix a b) (andPrefix a' b') := by
  apply erasesStatePrefix_bind ha
  intro first
  split
  · exact hb
  · exact erasesStatePrefix_pure _

theorem andPrefix_preserves_state {Outer Inner : Type}
    {I : List LifetimeEvent → Outer → Inner → Prop}
    {a b : StatePrefixT LifetimeEvent Outer Inner Bool}
    (safe : ∀ h w ambient, I h w ambient → LifetimeEvent.Safe h)
    (ha : StatePrefixPreserves I LifetimeEvent.Safe a)
    (hb : StatePrefixPreserves I LifetimeEvent.Safe b) :
    StatePrefixPreserves I LifetimeEvent.Safe (andPrefix a b) := by
  apply StatePrefixEnsures.bind ha
  intro first
  split
  · exact hb
  · exact StatePrefixEnsures.pure _ safe (fun _ _ _ hi => hi)

theorem liftWGObserver_andPrefix (a b : MixedM Bool) :
    liftWGObserver (andPrefix a b) = andPrefix (liftWGObserver a) (liftWGObserver b) := by
  simp only [andPrefix, liftWGObserver_bind, apply_ite, liftWGObserver_pure]

def keepKeyFreshRxPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftWGPrefix (branch .rxFreshSentLastminute (← getPeerMixed pid).sentLastminuteHandshake) then return
  let current := (← getPeerMixed pid).keypairCurrent
  let send ← andPrefix (liftWGPrefix (branch .rxFreshKeypair current.isSome)) do
    let some id := current | liftWGPrefix (invariant "unreachable")
    let k ← getKeypairPrefix id
    andPrefix (liftWGPrefix (branch .rxFreshValid k.sending.isValid)) do
      andPrefix (liftWGPrefix (branch .rxFreshInitiator k.iAmTheInitiator)) do
        liftWGPrefix (branchExpired .rxFreshExpired k.sending.birthdate (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT))
  if ← liftWGPrefix (branch .rxFreshSend send) then
    modifyPeerKeysPrefix pid fun p => {p with sentLastminuteHandshake := true}
    sendQueuedHandshakeInitiationPrefix pid false

theorem keepKeyFreshRxPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (keepKeyFreshRxPrefix pid) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRxPrefix keepKeyFreshRx
  apply erasesStatePrefix_bind (getPeerMixed_erases _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro sent
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (getPeerMixed_erases _)
    intro p
    apply erasesStatePrefix_bind
    · apply andPrefix_erases_state (erasesStatePrefix_lift _)
      cases he : p.keypairCurrent with
      | none => exact erasesStatePrefix_lift _
      | some id =>
        apply erasesStatePrefix_bind (getKeypairPrefix_erases _)
        intro k
        exact andPrefix_erases_state (erasesStatePrefix_lift _)
          (andPrefix_erases_state (erasesStatePrefix_lift _)
            (erasesStatePrefix_lift _))
    · intro send
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro yes
      split
      · simp only [modifyPeerKeysPrefix, bind_assoc]
        exact erasesStatePrefix_bind (getPeerMixed_erases _) (fun _ =>
          erasesStatePrefix_bind (setPeerMixed_erases _ _) (fun _ => sendQueuedHandshakeInitiationPrefix_erases _ _))
      · exact erasesStatePrefix_pure _

theorem keepKeyFreshRxPrefix_preserves_ambient (c : AmbientContracts I)
    (hq : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
    (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keepKeyFreshRxPrefix pid) := by
  unfold keepKeyFreshRxPrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
  intro p
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro sent
  split
  · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
  · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    intro p
    apply StatePrefixEnsures.bind
    · apply andPrefix_preserves_state (fun h w _ hi => c.safe h w hi)
        (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      cases he : p.keypairCurrent with
      | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
      | some id =>
        apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getKeypair_frame (fun _ => True) id))
        intro k
        apply andPrefix_preserves_state (fun h w _ hi => c.safe h w hi)
          (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        apply andPrefix_preserves_state (fun h w _ hi => c.safe h w hi)
          (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        exact AmbientContracts.drop (c.store (fun _ => True) _
          ((branchExpired_sameWGWorld _ _ _).factor wgStoreView))
    · intro send
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro yes
      split
      · exact StatePrefixEnsures.bind
          (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
            (fun p => {p with sentLastminuteHandshake := true}) (fun _ => rfl)))
          (fun _ => sendQueuedHandshakeInitiationPrefix_preserves_ambient c hq _ _)
      · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)

theorem sendWorkQueue_identity_metadata (pid : PeerId) :
    SameView (fun w => (identityView w, allocationMetadata w))
      (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata
  simp [Option.bind_map, Function.comp_def, deviceAllocationMetadata]
  rfl

theorem sendWorkQueue_allocation (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  have hf := (ProjectedAction.iff_run_ambient _ _ _).mp (sendWorkQueue_identity_metadata pid)
    w ambient x v ambient' hr
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem sendQueuedHandshakeInitiationPrefix_allocation (pid : PeerId) (retry : Bool) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (sendQueuedHandshakeInitiationPrefix pid retry) :=
  sendQueuedHandshakeInitiationPrefix_preserves_ambient allocationAmbient sendWorkQueue_allocation pid retry

theorem keepKeyFreshRxPrefix_allocation (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (keepKeyFreshRxPrefix pid) :=
  keepKeyFreshRxPrefix_preserves_ambient allocationAmbient sendWorkQueue_allocation pid

/-- Retain the original caller's arbitrary invariant over the actual product. -/
theorem sendQueuedHandshakeInitiationPrefix_preserves_product (c : ProductAmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))))
    (pid : PeerId) (retry : Bool) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (sendQueuedHandshakeInitiationPrefix pid retry)) := by
  have ambient {α : Type} (a : AmbientM α) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (MonadLift.monadLift a : WG.M α))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient a (fun w => wgStoreView w = initial)))
  simp only [sendQueuedHandshakeInitiationPrefix, liftWGObserver_bind, apply_ite, liftWGObserver_pure]
  apply PrefixPreserves.bind (ambient (AmbientM.branch .queuedNotRetry (!retry)))
  intro notRetry
  have tail : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (do
      let p ← getPeerMixed pid
      if ← liftWGPrefix (branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT not) then return
      if ← liftWGPrefix (branch .queuedDead p.isDead) then return
      peerGetMixed pid
      if ← liftWGPrefix (branch .queuedAlreadyQueued
          (p.handshakePending && !(← liftWGPrefix (peekQueuedUnit .sendWorker pid)))) then
        peerPutMixed (some pid)
        return
      modifyPeerKeysPrefix pid fun p => {p with handshakePending := true}
      liftWGPrefix (recordQueued .sendWorker pid)
      liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))) := by
    simp only [liftWGObserver_bind, apply_ite, liftWGObserver_pure]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) pid))
    intro p
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      ((branchExpired_sameWGWorld _ _ _ _).factor wgStoreView)))
    intro fresh
    split
    · exact PrefixPreserves.pure c.safe ()
    · apply PrefixPreserves.bind (ambient (AmbientM.branch .queuedDead p.isDead))
      intro dead
      split
      · exact PrefixPreserves.pure c.safe ()
      · apply PrefixPreserves.bind (c.peerGet pid)
        intro _
        apply PrefixPreserves.bind (ambient (AmbientM.peekQueuedUnit .sendWorker pid))
        intro pendingWasCleared
        apply PrefixPreserves.bind (ambient (AmbientM.branch .queuedAlreadyQueued
          (p.handshakePending && !pendingWasCleared)))
        intro queued
        split
        · exact PrefixPreserves.bind (c.peerPut _) (fun _ => PrefixPreserves.pure c.safe ())
        · apply PrefixPreserves.bind (ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
            (fun p => {p with handshakePending := true}) (fun _ => rfl)))
          intro _
          exact PrefixPreserves.bind (ambient (AmbientM.recordQueued .sendWorker pid)) (fun _ => hq pid)
  split
  · simpa only [liftWGObserver_bind, apply_ite, liftWGObserver_pure] using
      PrefixPreserves.bind (ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
        (fun p => {p with timerHandshakeAttempts := 0}) (fun _ => rfl))) (fun _ => tail)
  · simpa only [liftWGObserver_bind, apply_ite, liftWGObserver_pure] using tail

theorem keepKeyFreshRxPrefix_preserves_product (c : ProductAmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))))
    (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keepKeyFreshRxPrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (MonadLift.monadLift a : WG.M α))) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient a (fun w => wgStoreView w = initial)))
  simp only [keepKeyFreshRxPrefix, liftWGObserver_bind, apply_ite, liftWGObserver_pure,
    liftWGObserver_andPrefix]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
  intro p
  apply PrefixPreserves.bind (ambient (AmbientM.branch .rxFreshSentLastminute p.sentLastminuteHandshake))
  intro sent
  split
  · exact PrefixPreserves.pure c.safe ()
  · apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    intro p
    apply PrefixPreserves.bind
    · apply andPrefix_preserves c.safe (ambient (AmbientM.branch .rxFreshKeypair p.keypairCurrent.isSome))
      cases he : p.keypairCurrent with
      | none => exact ambient (AmbientM.invariant "unreachable")
      | some id =>
        simp only [liftWGObserver_bind, liftWGObserver_andPrefix]
        apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getKeypair_frame (fun _ => True) id))
        intro k
        apply andPrefix_preserves c.safe (ambient (AmbientM.branch .rxFreshValid k.sending.isValid))
        apply andPrefix_preserves c.safe (ambient (AmbientM.branch .rxFreshInitiator k.iAmTheInitiator))
        exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
          ((branchExpired_sameWGWorld _ _ _).factor wgStoreView))
    · intro send
      apply PrefixPreserves.bind (ambient (AmbientM.branch .rxFreshSend send))
      intro yes
      split
      · exact PrefixPreserves.bind
          (ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) pid
            (fun p => {p with sentLastminuteHandshake := true}) (fun _ => rfl)))
          (fun _ => sendQueuedHandshakeInitiationPrefix_preserves_product c hq _ _)
      · exact PrefixPreserves.pure c.safe ()

end Leanux.Proofs.WG.Lifetimes
