import Leanux.Proofs.WG.Lifetimes.MaintenanceTimers

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Receive-side maintenance through queued handshake initiation. Queue updates
are explicit ambient contracts; no worker execution or time bound is asserted. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def sendQueuedHandshakeInitiationPrefix (pid : PeerId) (isRetry : Bool) : MixedM Unit := do
  requireNotPendingMixed pid "queueing a handshake"
  if ← liftPrefix (branch .queuedNotRetry !isRetry) then
    modifyPeerKeysPrefix pid fun p => {p with timerHandshakeAttempts := 0}
  let p ← getPeerMixed pid
  if ← liftPrefix (branch .queuedNotExpired !(← liftPrefix (birthdateHasExpired p.lastSentHandshake REKEY_TIMEOUT))) then return
  if ← liftPrefix (branch .queuedDead p.isDead) then return
  peerGetMixed pid
  if ← liftPrefix (branch .queuedAlreadyQueued p.handshakePending) then
    peerPutMixed (some pid)
    return
  modifyPeerKeysPrefix pid fun p => {p with handshakePending := true}
  liftPrefix (recordQueued .sendWorker pid)
  liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
  liftPrefix (modify fun w => {w with queuedThisCall := pid :: w.queuedThisCall})

theorem sendQueuedHandshakeInitiationPrefix_erases (pid : PeerId) (retry : Bool) :
    ErasesPrefix (sendQueuedHandshakeInitiationPrefix pid retry) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiationPrefix sendQueuedHandshakeInitiation
  apply erasesPrefix_bind (requireNotPendingMixed_erases _ _)
  intro _
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro retryGuard
  split <;> first
    | (simp only [modifyPeerKeysPrefix, bind_assoc]
       apply erasesPrefix_bind (getPeerMixed_erases _)
       intro p
       apply erasesPrefix_bind (setPeerMixed_erases _ _)
       intro _)
    | skip
  all_goals
    apply erasesPrefix_bind (getPeerMixed_erases _)
    intro p
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro expiry
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro fresh
    split
    · exact erasesPrefix_pure _
    · apply erasesPrefix_bind (erasesPrefix_lift _)
      intro dead
      split
      · exact erasesPrefix_pure _
      · apply erasesPrefix_bind (peerGetMixed_erases _)
        intro _
        apply erasesPrefix_bind (erasesPrefix_lift _)
        intro queued
        split
        · exact erasesPrefix_bind (peerPutMixed_erases _) (fun _ => erasesPrefix_pure _)
        · try simp only [modifyPeerKeysPrefix, bind_assoc]
          exact erasesPrefix_bind (getPeerMixed_erases _) (fun _ =>
            erasesPrefix_bind (setPeerMixed_erases _ _) (fun _ =>
              erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
                erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _))))

theorem sendQueuedHandshakeInitiationPrefix_preserves_ambient (c : AmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
    (pid : PeerId) (retry : Bool) :
    PrefixPreserves I LifetimeEvent.Safe (sendQueuedHandshakeInitiationPrefix pid retry) := by
  unfold sendQueuedHandshakeInitiationPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (requireNotPendingMixed_spec c (fun _ => True) _ _))
  intro _
  apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro notRetry
  have tail : PrefixPreserves I LifetimeEvent.Safe (do
      let p ← getPeerMixed pid
      if ← liftPrefix (branch .queuedNotExpired !(← liftPrefix (birthdateHasExpired p.lastSentHandshake REKEY_TIMEOUT))) then return
      if ← liftPrefix (branch .queuedDead p.isDead) then return
      peerGetMixed pid
      if ← liftPrefix (branch .queuedAlreadyQueued p.handshakePending) then
        peerPutMixed (some pid)
        return
      modifyPeerKeysPrefix pid fun p => {p with handshakePending := true}
      liftPrefix (recordQueued .sendWorker pid)
      liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
      liftPrefix (modify fun w => {w with queuedThisCall := pid :: w.queuedThisCall})) := by
    apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) pid))
    intro p
    apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (Keypairs.birthdateHasExpired_sameKernel _ _)))
    intro expired
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro fresh
    split
    · exact PrefixPreserves.pure c.safe ()
    · apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro dead
      split
      · exact PrefixPreserves.pure c.safe ()
      · apply PrefixPreserves.bind (c.peerGet pid)
        intro _
        apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        intro queued
        split
        · exact PrefixPreserves.bind (c.peerPut _) (fun _ => PrefixPreserves.pure c.safe ())
        · apply PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
            (fun p => {p with handshakePending := true}) (fun _ => rfl)))
          intro _
          apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (recordQueued_sameKernel _ _)))
          intro _
          apply PrefixPreserves.bind (hq pid)
          intro _
          exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr; rfl))
  split
  · exact PrefixPreserves.bind (AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
      (fun p => {p with timerHandshakeAttempts := 0}) (fun _ => rfl))) (fun _ => tail)
  · exact tail

/-- Actual short-circuit composition, used only where the original second
operand is an explicit delayed do block. -/
def andPrefix (a b : MixedM Bool) : MixedM Bool := do if ← a then b else pure false

theorem andPrefix_erases (ha : ErasesPrefix a a') (hb : ErasesPrefix b b') :
    ErasesPrefix (andPrefix a b) (WG.andM a' b') := by
  apply erasesPrefix_bind ha
  intro first
  split
  · exact hb
  · exact erasesPrefix_pure _

theorem andPrefix_preserves (safe : ∀ h w, I h w → LifetimeEvent.Safe h)
    (ha : PrefixPreserves I LifetimeEvent.Safe a) (hb : PrefixPreserves I LifetimeEvent.Safe b) :
    PrefixPreserves I LifetimeEvent.Safe (andPrefix a b) := by
  apply PrefixPreserves.bind ha
  intro first
  split
  · exact hb
  · exact PrefixPreserves.pure safe _

def keepKeyFreshRxPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftPrefix (branch .rxFreshSentLastminute (← getPeerMixed pid).sentLastminuteHandshake) then return
  let current := (← getPeerMixed pid).keypairCurrent
  let send ← andPrefix (liftPrefix (branch .rxFreshKeypair current.isSome)) do
    let some id := current | liftPrefix (invariant "unreachable")
    let k ← getKeypairPrefix id
    andPrefix (liftPrefix (branch .rxFreshValid k.sending.isValid)) do
      andPrefix (liftPrefix (branch .rxFreshInitiator k.iAmTheInitiator)) do
        liftPrefix (branch .rxFreshExpired
          (← liftPrefix (birthdateHasExpired k.sending.birthdate (REJECT_AFTER_TIME - KEEPALIVE_TIMEOUT - REKEY_TIMEOUT))))
  if ← liftPrefix (branch .rxFreshSend send) then
    modifyPeerKeysPrefix pid fun p => {p with sentLastminuteHandshake := true}
    sendQueuedHandshakeInitiationPrefix pid false

theorem keepKeyFreshRxPrefix_erases (pid : PeerId) :
    ErasesPrefix (keepKeyFreshRxPrefix pid) (keepKeyFreshRx pid) := by
  unfold keepKeyFreshRxPrefix keepKeyFreshRx
  apply erasesPrefix_bind (getPeerMixed_erases _)
  intro p
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro sent
  split
  · exact erasesPrefix_pure _
  · apply erasesPrefix_bind (getPeerMixed_erases _)
    intro p
    apply erasesPrefix_bind
    · apply andPrefix_erases (erasesPrefix_lift _)
      cases he : p.keypairCurrent with
      | none => exact erasesPrefix_lift _
      | some id =>
        apply erasesPrefix_bind (getKeypairPrefix_erases _)
        intro k
        exact andPrefix_erases (erasesPrefix_lift _)
          (andPrefix_erases (erasesPrefix_lift _)
            (erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _)))
    · intro send
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro yes
      split
      · simp only [modifyPeerKeysPrefix, bind_assoc]
        exact erasesPrefix_bind (getPeerMixed_erases _) (fun _ =>
          erasesPrefix_bind (setPeerMixed_erases _ _) (fun _ => sendQueuedHandshakeInitiationPrefix_erases _ _))
      · exact erasesPrefix_pure _

theorem keepKeyFreshRxPrefix_preserves_ambient (c : AmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (keepKeyFreshRxPrefix pid) := by
  unfold keepKeyFreshRxPrefix
  repeat' first
    | exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | exact AmbientContracts.drop (c.getKeypair_frame (fun _ => True) _)
    | exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (Keypairs.birthdateHasExpired_sameKernel _ _))
    | exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) pid
        (fun p => {p with sentLastminuteHandshake := true}) (fun _ => rfl))
    | exact sendQueuedHandshakeInitiationPrefix_preserves_ambient c hq _ _
    | exact PrefixPreserves.pure c.safe _
    | apply andPrefix_preserves c.safe
    | apply PrefixPreserves.bind
    | split
    | (intro x; try dsimp only)

theorem sendWorkQueue_identity_metadata (pid : PeerId) :
    SameView (fun w => (identityView w, allocationMetadata w))
      (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}) := by
  intro w x v hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata
  simp [Option.bind_map, Function.comp_def, deviceAllocationMetadata]
  rfl

theorem sendWorkQueue_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have hf := sendWorkQueue_identity_metadata pid w x v hr
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem sendQueuedHandshakeInitiationPrefix_allocation (pid : PeerId) (retry : Bool) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (sendQueuedHandshakeInitiationPrefix pid retry) :=
  sendQueuedHandshakeInitiationPrefix_preserves_ambient allocationAmbient sendWorkQueue_allocation pid retry

theorem keepKeyFreshRxPrefix_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (keepKeyFreshRxPrefix pid) :=
  keepKeyFreshRxPrefix_preserves_ambient allocationAmbient sendWorkQueue_allocation pid

end Leanux.Proofs.WG.Lifetimes
