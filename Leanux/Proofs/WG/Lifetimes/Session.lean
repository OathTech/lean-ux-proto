import Leanux.Proofs.WG.Lifetimes.KeypairRotation
import Leanux.Proofs.Framing.WGHandshake

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Session creation observes each resolved peer/keypair access. Clock, KDF,
branch, and scalar index-table operations are the inspected access-free lifts.
Creation observations precede every initializer and remain on later failures. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def handshakeZeroPrefix (pid : PeerId) : MixedM Unit := do
  let z : List UInt8 := List.replicate 32 0
  let p ← getPeerMixed pid
  setPeerMixed pid {p with ephemeralPrivate := z, remoteEphemeral := z, hash := z, chainingKey := z, remoteIndex := 0, handshakeState := 0}

def deriveKeysPrefix (kp : KeypairId) (initiator : Bool) (chainingKey : List UInt8) : MixedM Unit := do
  let birthdate ← liftWGPrefix (hiddenClock64 .deriveKeysBirthdate)
  let outs ← liftWGPrefix (kdf true false chainingKey [])
  let sym (key : List UInt8) : SymmetricKey := {key, birthdate, isValid := true}
  let (first, second) := (sym (← liftWGPrefix (kdfOut outs 0)), sym (← liftWGPrefix (kdfOut outs 1)))
  let k ← getKeypairPrefix kp
  setKeypairPrefix kp (if initiator then {k with sending := first, receiving := second}
    else {k with receiving := first, sending := second})

theorem handshakeZeroPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (handshakeZeroPrefix pid) (handshakeZero pid) := by
  unfold handshakeZeroPrefix handshakeZero
  exact erasesStatePrefix_bind (getPeerMixed_erases pid) (fun p => setPeerMixed_erases pid _)

theorem deriveKeysPrefix_erases (kp : KeypairId) (initiator : Bool) (key : List UInt8) :
    ErasesStatePrefix (deriveKeysPrefix kp initiator key) (deriveKeys kp initiator key) := by
  unfold deriveKeysPrefix deriveKeys
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro birthdate
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro outs
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro first
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro second
  exact erasesStatePrefix_bind (getKeypairPrefix_erases kp) (fun _ => setKeypairPrefix_erases kp _)

theorem handshakeZeroPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (handshakeZeroPrefix pid) (fun _ => P) := by
  unfold handshakeZeroPrefix
  apply StatePrefixEnsures.bind (c.getPeer P pid)
  intro p
  exact c.setPeer P pid {p with ephemeralPrivate := List.replicate 32 0, remoteEphemeral := List.replicate 32 0, hash := List.replicate 32 0, chainingKey := List.replicate 32 0, remoteIndex := 0, handshakeState := 0}

theorem deriveKeysPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) (initiator : Bool) (key : List UInt8) :
    AmbientSpec I P (deriveKeysPrefix kp initiator key) (fun _ => P) := by
  unfold deriveKeysPrefix
  apply StatePrefixEnsures.bind (c.store P _ (fun initial =>
    hoare_liftAmbient (AmbientM.hiddenClock64 .deriveKeysBirthdate) (fun w => wgStoreView w = initial)))
  intro birthdate
  apply StatePrefixEnsures.bind (c.store P _ ((kdf_sameWGWorld true false key []).factor wgStoreView))
  intro outs
  apply StatePrefixEnsures.bind (c.store P _ ((kdfOut_sameWGWorld outs 0).factor wgStoreView))
  intro first
  apply StatePrefixEnsures.bind (c.store P _ ((kdfOut_sameWGWorld outs 1).factor wgStoreView))
  intro second
  apply StatePrefixEnsures.bind (c.getKeypair P kp)
  intro k
  cases initiator
  · exact c.setKeypair P kp {k with receiving := {key := first, birthdate, isValid := true}, sending := {key := second, birthdate, isValid := true}}
  · exact c.setKeypair P kp {k with sending := {key := first, birthdate, isValid := true}, receiving := {key := second, birthdate, isValid := true}}

/-- No store access occurs before derive_keys obtains its birthdate. -/
theorem deriveKeysPrefix_clock_failure (kp : KeypairId) (initiator : Bool) (key : List UInt8)
    (w : WGWorld) (ambient : Ambient) (h : List LifetimeEvent) (e : Stop)
    (he : ((hiddenClock64 .deriveKeysBirthdate : WG.M Int64).run w).run ambient = .error e) :
    runStatePrefix (deriveKeysPrefix kp initiator key) w ambient h = (.error e, h) := by
  simp only [deriveKeysPrefix, liftWGPrefix, runStatePrefix_bind, runStatePrefix_lift, he]

def sessionStateRejected (st : Nat) : AmbientM Bool := do
  if ← AmbientM.branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE) then
    AmbientM.branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)
  else pure false

/-- Index removal/replacement is observed without inventing object access;
the canonical index adapter supplies the allocation invariant's stability. -/
theorem indexReplaceHandshake_allocation (pid : PeerId) (kp : KeypairId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
      (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp))) := by
  apply StatePrefixEnsures.lift _ (fun h w _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  have hp : Hoare (liftIndex (indexReplaceHandshake pid kp)) (AllocationInv h)
      (fun _ => AllocationInv h) := by
    apply hoare_liftIndex
    intro g d table hg hd
    apply hg.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [hd]
    · simp [allocationMetadata, deviceAllocationMetadata, hd]
  exact (hoare_iff_run_ambient _ _ _).mp hp w ambient x v ambient' hi hr

def sessionKeypairPrefix (kp : KeypairId) (initiator : Bool) (remoteIndex : Nat) : MixedM Unit := do
  let k ← getKeypairPrefix kp
  setKeypairPrefix kp {k with iAmTheInitiator := initiator, remoteIndex}

theorem sessionKeypairPrefix_erases (kp : KeypairId) (initiator : Bool) (remoteIndex : Nat) :
    ErasesStatePrefix (sessionKeypairPrefix kp initiator remoteIndex)
      (do setKeypair kp {(← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex}) :=
  erasesStatePrefix_bind (getKeypairPrefix_erases kp) (fun _ => setKeypairPrefix_erases kp _)

theorem sessionKeypairPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) (initiator : Bool) (remoteIndex : Nat) :
    AmbientSpec I P (sessionKeypairPrefix kp initiator remoteIndex) (fun _ => P) := by
  apply StatePrefixEnsures.bind (c.getKeypair P kp)
  intro k
  exact c.setKeypair P kp {k with iAmTheInitiator := initiator, remoteIndex}

def beginSessionPrefix (pid : PeerId) : MixedM Bool := do
  let st := (← getPeerMixed pid).handshakeState
  if ← liftWGPrefix (MonadLift.monadLift (sessionStateRejected st) : WG.M Bool) then return false
  let created ← keypairCreatePrefix (← peerWordPrefix (.handshake pid))
  if ← liftWGPrefix (branch .sessionNoKeypair created.isNone) then return false
  let some kp := created | liftWGPrefix (invariant "unreachable")
  let p ← getPeerMixed pid
  let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
  sessionKeypairPrefix kp initiator p.remoteIndex
  if ← liftWGPrefix (branch .sessionInitiator initiator) then deriveKeysPrefix kp true p.chainingKey
  else deriveKeysPrefix kp false p.chainingKey
  handshakeZeroPrefix pid
  if ← liftWGPrefix (branch .sessionAlive !(← getPeerMixed pid).isDead) then
    addNewKeypairPrefix pid kp
    _ ← peerDerefPrefix (.handshake pid)
    if !(← liftWGPrefix (liftIndex (indexReplaceHandshake pid kp))) then
      liftWGPrefix (unsupported "begin_session: the handshake entry was unhashed")
    return true
  liftWGPrefix (unsupported "a dead peer finishing a session")

theorem beginSessionPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (beginSessionPrefix pid) (beginSession pid) := by
  have reject_eq (st : Nat) :
      (MonadLift.monadLift (sessionStateRejected st) : WG.M Bool) =
        WG.andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
          (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE)) := by
    change (monadLift (sessionStateRejected st) : WG.M Bool) = _
    simp only [sessionStateRejected, WG.andM, branch, monadLift_bind]
    congr 1
    funext first
    cases first <;> simp only [Bool.false_eq_true, ↓reduceIte, monadLift_pure]
  unfold beginSessionPrefix beginSession
  simp only [← reject_eq]
  apply erasesStatePrefix_bind (getPeerMixed_erases pid)
  intro old
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro rejected
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (peerWordPrefix_erases _)
    intro word
    apply erasesStatePrefix_bind (keypairCreatePrefix_erases word)
    intro created
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro missing
    split
    · exact erasesStatePrefix_pure _
    · cases created with
      | none => exact erasesStatePrefix_lift _
      | some kp =>
        apply erasesStatePrefix_bind (getPeerMixed_erases pid)
        intro p
        simp only [sessionKeypairPrefix, bind_assoc]
        apply erasesStatePrefix_bind (getKeypairPrefix_erases _)
        intro k
        apply erasesStatePrefix_bind (setKeypairPrefix_erases _ _)
        intro _
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro initiator
        split
        all_goals
          apply erasesStatePrefix_bind (deriveKeysPrefix_erases _ _ _)
          intro _
          apply erasesStatePrefix_bind (handshakeZeroPrefix_erases _)
          intro _
          apply erasesStatePrefix_bind (getPeerMixed_erases _)
          intro alive
          apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
          intro live
          split
        all_goals first
          | exact erasesStatePrefix_lift _
          | skip
        all_goals
          apply erasesStatePrefix_bind (addNewKeypairPrefix_erases _ _)
          intro _
          apply erasesStatePrefix_bind (peerDerefPrefix_erases _)
          intro _
          apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
          intro replaced
          split
        all_goals first
          | exact erasesStatePrefix_pure _
          | apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
            intro _
            exact erasesStatePrefix_pure _

theorem beginSessionPrefix_preserves_ambient (c : AmbientContracts I)
    (create : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairCreatePrefix pid))
    (put : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now))
    (replace : ∀ pid kp, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp))))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (beginSessionPrefix pid) := by
  unfold beginSessionPrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro old
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (fun initial =>
    hoare_liftAmbient (sessionStateRejected old.handshakeState) (fun w => wgStoreView w = initial))))
  intro rejected
  split
  · exact StatePrefixEnsures.pure false (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
  · apply StatePrefixEnsures.bind (AmbientContracts.drop (peerWordPrefix_spec c (fun _ => True) (.handshake pid)))
    intro word
    apply StatePrefixEnsures.bind (create word)
    intro created
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro missing
    split
    · exact StatePrefixEnsures.pure false (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    · cases created with
      | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
      | some kp =>
        apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
        intro p
        apply StatePrefixEnsures.bind (AmbientContracts.drop (sessionKeypairPrefix_spec_ambient c (fun _ => True) kp _ _))
        intro _
        have tail : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
            (do handshakeZeroPrefix pid
                if ← liftWGPrefix (branch .sessionAlive !(← getPeerMixed pid).isDead) then
                  addNewKeypairPrefix pid kp
                  _ ← peerDerefPrefix (.handshake pid)
                  if !(← liftWGPrefix (liftIndex (indexReplaceHandshake pid kp))) then
                    liftWGPrefix (unsupported "begin_session: the handshake entry was unhashed")
                  return true
                liftWGPrefix (unsupported "a dead peer finishing a session")) := by
          apply StatePrefixEnsures.bind (AmbientContracts.drop (handshakeZeroPrefix_spec_ambient c (fun _ => True) pid))
          intro _
          apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
          intro alive
          apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
          intro live
          split
          · apply StatePrefixEnsures.bind (addNewKeypairPrefix_preserves_ambient c put pid kp)
            intro _
            apply StatePrefixEnsures.bind (AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) (.handshake pid)))
            intro _
            apply StatePrefixEnsures.bind (replace pid kp)
            intro replaced
            split
            · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.unsupported (fun _ => True) _))
              intro _
              exact StatePrefixEnsures.pure true (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
            · exact StatePrefixEnsures.pure true (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
          · exact AmbientContracts.drop (c.unsupported (fun _ => True) _)
        apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        intro initiator
        split
        all_goals apply StatePrefixEnsures.bind (AmbientContracts.drop (deriveKeysPrefix_spec_ambient c (fun _ => True) kp _ p.chainingKey))
        all_goals intro _
        all_goals exact tail


/-- The original caller interface keeps invariants over the whole product. -/
theorem handshakeZeroPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (pid : PeerId) : ProductAmbientSpec I P (liftWGObserver (handshakeZeroPrefix pid)) (fun _ => P) := by
  simp only [handshakeZeroPrefix, liftWGObserver_bind]
  apply PrefixEnsures.bind (c.getPeer P pid)
  intro p
  exact c.setPeer P pid {p with ephemeralPrivate := List.replicate 32 0, remoteEphemeral := List.replicate 32 0, hash := List.replicate 32 0, chainingKey := List.replicate 32 0, remoteIndex := 0, handshakeState := 0}

theorem deriveKeysPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) (initiator : Bool) (key : List UInt8) :
    ProductAmbientSpec I P (liftWGObserver (deriveKeysPrefix kp initiator key)) (fun _ => P) := by
  simp only [deriveKeysPrefix, liftWGObserver_bind]
  apply PrefixEnsures.bind (c.nativeStore P _ (fun initial =>
    hoare_liftAmbient (AmbientM.hiddenClock64 .deriveKeysBirthdate) (fun w => wgStoreView w = initial)))
  intro birthdate
  apply PrefixEnsures.bind (c.nativeStore P _ ((kdf_sameWGWorld true false key []).factor wgStoreView))
  intro outs
  apply PrefixEnsures.bind (c.nativeStore P _ ((kdfOut_sameWGWorld outs 0).factor wgStoreView))
  intro first
  apply PrefixEnsures.bind (c.nativeStore P _ ((kdfOut_sameWGWorld outs 1).factor wgStoreView))
  intro second
  apply PrefixEnsures.bind (c.getKeypair P kp)
  intro k
  cases initiator
  · exact c.setKeypair P kp {k with receiving := {key := first, birthdate, isValid := true}, sending := {key := second, birthdate, isValid := true}}
  · exact c.setKeypair P kp {k with sending := {key := first, birthdate, isValid := true}, receiving := {key := second, birthdate, isValid := true}}

theorem sessionKeypairPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) (initiator : Bool) (remoteIndex : Nat) :
    ProductAmbientSpec I P (liftWGObserver (sessionKeypairPrefix kp initiator remoteIndex)) (fun _ => P) := by
  simp only [sessionKeypairPrefix, liftWGObserver_bind]
  apply PrefixEnsures.bind (c.getKeypair P kp)
  intro k
  exact c.setKeypair P kp {k with iAmTheInitiator := initiator, remoteIndex}

theorem beginSessionPrefix_preserves_product (c : ProductAmbientContracts I)
    (create : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairCreatePrefix pid)))
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (replace : ∀ pid kp, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp)))))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (beginSessionPrefix pid)) := by
  have ambient_spec {α : Type} (a : AmbientM α) :
      ProductAmbientSpec I (fun _ => True)
        (liftWGObserver (liftWGPrefix (MonadLift.monadLift a : WG.M α))) (fun _ _ => True) :=
    c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient a (fun w => wgStoreView w = initial))
  have word_spec : ProductAmbientSpec I (fun _ => True)
      (liftWGObserver (peerWordPrefix (.handshake pid))) (fun _ _ => True) := by
    simp only [peerWordPrefix, liftWGObserver_bind, liftWGObserver_pure]
    apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
    intro p
    exact ProductAmbientContracts.forget
      (c.pure (fun s => True ∧ s.1.slots pid = some p.internalId) p.handshakeEntryPeer)
      (fun _ _ hi => hi.1)
  simp only [beginSessionPrefix, liftWGObserver_bind]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro old
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (ambient_spec (sessionStateRejected old.handshakeState)))
  intro rejected
  split
  · simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe false
  · simp only [liftWGObserver_bind]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop word_spec)
    intro word
    apply PrefixPreserves.bind (create word)
    intro created
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (ambient_spec (AmbientM.branch _ _)))
    intro missing
    split
    · simpa only [liftWGObserver_pure] using PrefixPreserves.pure c.safe false
    · cases created with
      | none => exact ProductAmbientContracts.drop (ambient_spec (AmbientM.invariant _))
      | some kp =>
        simp only [liftWGObserver_bind]
        apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer (fun _ => True) pid))
        intro p
        apply PrefixPreserves.bind (ProductAmbientContracts.drop (sessionKeypairPrefix_spec_product c (fun _ => True) kp _ _))
        intro _
        have tail : PrefixPreserves I LifetimeEvent.Safe
            (liftWGObserver (do
              handshakeZeroPrefix pid
              if ← liftWGPrefix (branch .sessionAlive !(← getPeerMixed pid).isDead) then
                addNewKeypairPrefix pid kp
                _ ← peerDerefPrefix (.handshake pid)
                if !(← liftWGPrefix (liftIndex (indexReplaceHandshake pid kp))) then
                  liftWGPrefix (unsupported "begin_session: the handshake entry was unhashed")
                return true
              liftWGPrefix (unsupported "a dead peer finishing a session"))) := by
          simp only [liftWGObserver_bind]
          apply PrefixPreserves.bind (ProductAmbientContracts.drop (handshakeZeroPrefix_spec_product c (fun _ => True) pid))
          intro _
          apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer (fun _ => True) pid))
          intro alive
          apply PrefixPreserves.bind (ProductAmbientContracts.drop (ambient_spec (AmbientM.branch _ _)))
          intro live
          split
          · simp only [liftWGObserver_bind]
            apply PrefixPreserves.bind (addNewKeypairPrefix_preserves_product c put pid kp)
            intro _
            apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.peerDeref (fun _ => True) (.handshake pid)))
            intro _
            apply PrefixPreserves.bind (replace pid kp)
            intro replaced
            split
            · simp only [liftWGObserver_bind, liftWGObserver_pure]
              apply PrefixPreserves.bind (ProductAmbientContracts.drop (ambient_spec (AmbientM.unsupported _)))
              intro _
              exact PrefixPreserves.pure c.safe true
            · exact PrefixPreserves.pure c.safe true
          · exact ProductAmbientContracts.drop (ambient_spec (AmbientM.unsupported _))
        apply PrefixPreserves.bind (ProductAmbientContracts.drop (ambient_spec (AmbientM.branch _ _)))
        intro initiator
        split
        all_goals
          simp only [liftWGObserver_bind]
          apply PrefixPreserves.bind (ProductAmbientContracts.drop
            (deriveKeysPrefix_spec_product c (fun _ => True) kp _ p.chainingKey))
          intro _
          simpa only [liftWGObserver_bind] using tail

theorem beginSessionPrefix_allocation (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (beginSessionPrefix pid) :=
  beginSessionPrefix_preserves_ambient allocationAmbient keypairCreatePrefix_preserves
    keypairPutPrefix_allocation indexReplaceHandshake_allocation pid

end Leanux.Proofs.WG.Lifetimes
