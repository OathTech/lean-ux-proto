import Leanux.Proofs.WG.Lifetimes.KeypairRotation

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
  let birthdate ← liftPrefix (hiddenClock64 .deriveKeysBirthdate)
  let outs ← liftPrefix (kdf true false chainingKey [])
  let sym (key : List UInt8) : SymmetricKey := {key, birthdate, isValid := true}
  let (first, second) := (sym (← liftPrefix (kdfOut outs 0)), sym (← liftPrefix (kdfOut outs 1)))
  let k ← getKeypairPrefix kp
  setKeypairPrefix kp (if initiator then {k with sending := first, receiving := second}
    else {k with receiving := first, sending := second})

theorem handshakeZeroPrefix_erases (pid : PeerId) :
    ErasesPrefix (handshakeZeroPrefix pid) (handshakeZero pid) := by
  unfold handshakeZeroPrefix handshakeZero
  exact erasesPrefix_bind (getPeerMixed_erases pid) (fun p => setPeerMixed_erases pid _)

theorem deriveKeysPrefix_erases (kp : KeypairId) (initiator : Bool) (key : List UInt8) :
    ErasesPrefix (deriveKeysPrefix kp initiator key) (deriveKeys kp initiator key) := by
  unfold deriveKeysPrefix deriveKeys
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro birthdate
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro outs
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro first
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro second
  exact erasesPrefix_bind (getKeypairPrefix_erases kp) (fun _ => setKeypairPrefix_erases kp _)

theorem handshakeZeroPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (handshakeZeroPrefix pid) (fun _ => P) := by
  unfold handshakeZeroPrefix
  apply PrefixEnsures.bind (c.getPeer P pid)
  intro p
  exact c.setPeer P pid {p with ephemeralPrivate := List.replicate 32 0, remoteEphemeral := List.replicate 32 0, hash := List.replicate 32 0, chainingKey := List.replicate 32 0, remoteIndex := 0, handshakeState := 0}

theorem deriveKeysPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) (initiator : Bool) (key : List UInt8) :
    AmbientSpec I P (deriveKeysPrefix kp initiator key) (fun _ => P) := by
  unfold deriveKeysPrefix
  apply PrefixEnsures.bind (c.kernel P _ (hiddenClock64_sameKernel .deriveKeysBirthdate))
  intro birthdate
  apply PrefixEnsures.bind (c.kernel P _ (Keypairs.kdf_sameKernel true false key []))
  intro outs
  apply PrefixEnsures.bind (c.kernel P _ (Keypairs.kdfOut_sameKernel outs 0))
  intro first
  apply PrefixEnsures.bind (c.kernel P _ (Keypairs.kdfOut_sameKernel outs 1))
  intro second
  apply PrefixEnsures.bind (c.getKeypair P kp)
  intro k
  cases initiator
  · exact c.setKeypair P kp {k with receiving := {key := first, birthdate, isValid := true}, sending := {key := second, birthdate, isValid := true}}
  · exact c.setKeypair P kp {k with sending := {key := first, birthdate, isValid := true}, receiving := {key := second, birthdate, isValid := true}}

/-- No store access occurs before derive_keys obtains its birthdate. -/
theorem deriveKeysPrefix_clock_failure (kp : KeypairId) (initiator : Bool) (key : List UInt8)
    (w : World) (h : List LifetimeEvent) (e : Stop)
    (he : (hiddenClock64 .deriveKeysBirthdate).run w = .error e) :
    runPrefix (deriveKeysPrefix kp initiator key) w h = (.error e, h) := by
  simp only [deriveKeysPrefix, runPrefix_bind, runPrefix_lift, he]

def sessionStateRejected (st : Nat) : M Bool :=
  WG.andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
    (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE))

theorem sessionStateRejected_sameKernel (st : Nat) : SameKernel (sessionStateRejected st) := by
  unfold sessionStateRejected WG.andM
  apply sameKernel_bind (sameKernel_branch _ _)
  intro first
  split
  · exact sameKernel_branch _ _
  · exact sameKernel_pure _

/-- The only store reads are of the scalar index table, not its referenced
peer or keypair objects. The update changes no lifetime or allocator cursor. -/
theorem indexReplaceHandshake_identity_metadata (pid : PeerId) (kp : KeypairId) :
    SameView (fun w => (identityView w, allocationMetadata w)) (indexReplaceHandshake pid kp) := by
  apply SameView.of_wp
  intro s
  mvcgen [indexReplaceHandshake, indexHashed, getDev, getK, modifyDev, modifyK, branch, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata at *
  all_goals simp_all [deviceAllocationMetadata]

theorem indexReplaceHandshake_allocation (pid : PeerId) (kp : KeypairId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (liftPrefix (indexReplaceHandshake pid kp)) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have hf := indexReplaceHandshake_identity_metadata pid kp w x v hr
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

def sessionKeypairPrefix (kp : KeypairId) (initiator : Bool) (remoteIndex : Nat) : MixedM Unit := do
  let k ← getKeypairPrefix kp
  setKeypairPrefix kp {k with iAmTheInitiator := initiator, remoteIndex}

theorem sessionKeypairPrefix_erases (kp : KeypairId) (initiator : Bool) (remoteIndex : Nat) :
    ErasesPrefix (sessionKeypairPrefix kp initiator remoteIndex)
      (do setKeypair kp {(← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex}) :=
  erasesPrefix_bind (getKeypairPrefix_erases kp) (fun _ => setKeypairPrefix_erases kp _)

theorem sessionKeypairPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop)
    (kp : KeypairId) (initiator : Bool) (remoteIndex : Nat) :
    AmbientSpec I P (sessionKeypairPrefix kp initiator remoteIndex) (fun _ => P) := by
  apply PrefixEnsures.bind (c.getKeypair P kp)
  intro k
  exact c.setKeypair P kp {k with iAmTheInitiator := initiator, remoteIndex}

def beginSessionPrefix (pid : PeerId) : MixedM Bool := do
  let st := (← getPeerMixed pid).handshakeState
  if ← liftPrefix (sessionStateRejected st) then return false
  let created ← keypairCreatePrefix (← peerWordPrefix (.handshake pid))
  if ← liftPrefix (branch .sessionNoKeypair created.isNone) then return false
  let some kp := created | liftPrefix (invariant "unreachable")
  let p ← getPeerMixed pid
  let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
  sessionKeypairPrefix kp initiator p.remoteIndex
  if ← liftPrefix (branch .sessionInitiator initiator) then deriveKeysPrefix kp true p.chainingKey
  else deriveKeysPrefix kp false p.chainingKey
  handshakeZeroPrefix pid
  if ← liftPrefix (branch .sessionAlive !(← getPeerMixed pid).isDead) then
    addNewKeypairPrefix pid kp
    _ ← peerDerefPrefix (.handshake pid)
    if !(← liftPrefix (indexReplaceHandshake pid kp)) then
      liftPrefix (unsupported "begin_session: the handshake entry was unhashed")
    return true
  liftPrefix (unsupported "a dead peer finishing a session")

theorem beginSessionPrefix_erases (pid : PeerId) :
    ErasesPrefix (beginSessionPrefix pid) (beginSession pid) := by
  unfold beginSessionPrefix beginSession sessionStateRejected
  simp only [sessionKeypairPrefix, bind_assoc]
  repeat' first
    | exact getPeerMixed_erases _
    | exact keypairCreatePrefix_erases _
    | exact peerWordPrefix_erases _
    | exact peerDerefPrefix_erases _
    | exact getKeypairPrefix_erases _
    | exact setKeypairPrefix_erases _ _
    | exact sessionKeypairPrefix_erases _ _ _
    | exact deriveKeysPrefix_erases _ _ _
    | exact handshakeZeroPrefix_erases _
    | exact addNewKeypairPrefix_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | intro x; try dsimp only
    | split
    | rfl
  all_goals simp_all

theorem beginSessionPrefix_preserves_ambient (c : AmbientContracts I)
    (create : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (keypairCreatePrefix pid))
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now))
    (replace : ∀ pid kp, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (indexReplaceHandshake pid kp)))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (beginSessionPrefix pid) := by
  unfold beginSessionPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
  intro old
  apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (sessionStateRejected_sameKernel _)))
  intro rejected
  split
  · exact PrefixPreserves.pure c.safe false
  · apply PrefixPreserves.bind (AmbientContracts.drop (peerWordPrefix_spec c (fun _ => True) (.handshake pid)))
    intro word
    apply PrefixPreserves.bind (create word)
    intro created
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro missing
    split
    · exact PrefixPreserves.pure c.safe false
    · cases created with
      | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
      | some kp =>
        apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
        intro p
        apply PrefixPreserves.bind (AmbientContracts.drop (sessionKeypairPrefix_spec_ambient c (fun _ => True) kp _ _))
        intro _
        have tail : PrefixPreserves I LifetimeEvent.Safe
            (do handshakeZeroPrefix pid
                if ← liftPrefix (branch .sessionAlive !(← getPeerMixed pid).isDead) then
                  addNewKeypairPrefix pid kp
                  _ ← peerDerefPrefix (.handshake pid)
                  if !(← liftPrefix (indexReplaceHandshake pid kp)) then
                    liftPrefix (unsupported "begin_session: the handshake entry was unhashed")
                  return true
                liftPrefix (unsupported "a dead peer finishing a session")) := by
          apply PrefixPreserves.bind (AmbientContracts.drop (handshakeZeroPrefix_spec_ambient c (fun _ => True) pid))
          intro _
          apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer (fun _ => True) pid))
          intro alive
          apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
          intro live
          split
          · apply PrefixPreserves.bind (addNewKeypairPrefix_preserves_ambient c put pid kp)
            intro _
            apply PrefixPreserves.bind (AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) (.handshake pid)))
            intro _
            apply PrefixPreserves.bind (replace pid kp)
            intro replaced
            split
            · apply PrefixPreserves.bind (AmbientContracts.drop (c.unsupported (fun _ => True) _))
              intro _
              exact PrefixPreserves.pure c.safe true
            · exact PrefixPreserves.pure c.safe true
          · exact AmbientContracts.drop (c.unsupported (fun _ => True) _)
        apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        intro initiator
        split
        all_goals apply PrefixPreserves.bind (AmbientContracts.drop (deriveKeysPrefix_spec_ambient c (fun _ => True) kp _ p.chainingKey))
        all_goals intro _
        all_goals exact tail

theorem beginSessionPrefix_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (beginSessionPrefix pid) :=
  beginSessionPrefix_preserves_ambient allocationAmbient keypairCreatePrefix_preserves
    keypairPutPrefix_allocation indexReplaceHandshake_allocation pid

end Leanux.Proofs.WG.Lifetimes
