import Leanux.Proofs.WG.Noise.SessionModel
import Leanux.Proofs.WG.Noise.SessionFrames
import Leanux.Proofs.WG.Index.SessionOwners
import Leanux.Proofs.WG.Index.Table

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.WG.Config Std.Do

theorem sessionKdf_pair (ck : List UInt8) :
    kdfOutputs ck [] 2 = [sessionFirst ck, sessionSecond ck] := by
  simp [kdfOutputs, sessionFirst, sessionSecond, List.range']

theorem sessionKdf_returns (ck : List UInt8) (P : Kernel → Prop) :
    ⦃fun w => ⌜P w.k⌝⦄ kdf true false ck []
      ⦃⇓ outs w => ⌜outs = [sessionFirst ck, sessionSecond ck] ∧ P w.k⌝⦄ := by
  mvcgen [kdf, WG.orM, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [sessionKdf_pair]

theorem deriveKeys_effect (kp : KeypairId) (initiator : Bool) (ck : List UInt8)
    (d : Device) (k : Keypair) (counter : Nat) (resident : d.keypairs[kp]? = some k) :
    Ensures (deriveKeys kp initiator ck)
      (fun w => w.k.wg = some d ∧ w.k.keypairCounter = counter)
      (fun _ w => ∃ birth, w.k.wg = some { d with
        keypairs := d.keypairs.insert kp (sessionDerivedKey k initiator ck birth) } ∧ w.k.keypairCounter = counter) := by
  have hh := hiddenClock64_kernel_spec (fun k => k.wg = some d ∧ k.keypairCounter = counter)
  have hk := sessionKdf_returns ck (fun k => k.wg = some d ∧ k.keypairCounter = counter)
  rw [ensures_iff]
  mvcgen [deriveKeys, kdfOut, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK, invariant, hh, hk]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [sessionDerivedKey]
  all_goals grind


/-- The original publication suffix after rotation, including both stopping guards. -/
def sessionPublish (pid : PeerId) (kp : KeypairId) : M Bool := do
  _ ← IndexOwner.peerDeref (.handshake pid)
  if !(← indexReplaceHandshake pid kp) then unsupported "begin_session: the handshake entry was unhashed"
  return true

def sessionFinish (pid : PeerId) (kp : KeypairId) : M Bool := do
  handshakeZero pid
  if ← branch .sessionAlive !(← getPeer pid).isDead then
    addNewKeypair pid kp
    sessionPublish pid kp
  else unsupported "a dead peer finishing a session"

theorem sessionAfterAllocation_finish (pid : PeerId) (st : Nat) (kp : KeypairId) :
    Index.sessionAfterAllocation pid st kp = (do
      let p ← getPeer pid
      let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
      setKeypair kp { (← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex := p.remoteIndex }
      if ← branch .sessionInitiator initiator then deriveKeys kp true p.chainingKey
      else deriveKeys kp false p.chainingKey
      sessionFinish pid kp) := rfl

theorem handshakeZero_device_counter (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p) :
    ⦃fun w => ⌜w.k.wg = some d ∧ w.k.keypairCounter = counter⌝⦄ handshakeZero pid
      ⦃⇓? _ w => ⌜w.k.wg = some { d with peers := d.peers.insert pid (sessionZeroPeer p) } ∧
        w.k.keypairCounter = counter⌝⦄ := by
  mvcgen [handshakeZero, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [sessionZeroPeer]

theorem rotation_device_counter (pid : PeerId) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (counter : Nat)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[kp]? = some k) :
    Ensures (addNewKeypair pid kp) (fun w => w.k.wg = some d ∧ w.k.keypairCounter = counter)
      (fun _ w => ∃ final, w.k.wg = some final ∧ w.k.keypairCounter = counter ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator kp) final ∧
        final.peers[pid]? = some (rotationPeer (rotationPlan p k.iAmTheInitiator kp) p)) := by
  intro w result final pre run
  obtain ⟨out, device, effect⟩ := addNewKeypair_effect pid kp d p k resident key w result final pre.1 run
  exact ⟨out, device, (ensures_iff _ _ _).mpr (addNewKeypair_counter pid kp counter) w result final pre.2 run,
    effect, rotationRun_peer effect p resident⟩

theorem sessionPublish_effect (pid : PeerId) (kp : KeypairId) (d : Device)
    (p : Peer) (counter : Nat) (resident : d.peers[pid]? = some p) :
    Ensures (sessionPublish pid kp) (fun w => w.k.wg = some d ∧ w.k.keypairCounter = counter)
      (fun ok w => ok = true ∧ p.handshakeEntryPeer ≠ none ∧
        d.indexTable.any (·.owner == .handshake pid) = true ∧
        w.k.wg = some { d with indexTable := Index.replaceOwner pid kp d.indexTable } ∧
        w.k.keypairCounter = counter) := by
  rw [ensures_iff]
  mvcgen [sessionPublish, IndexOwner.peerDeref, IndexOwner.peerWord, indexReplaceHandshake,
    indexHashed, getPeer, getDev, getK, branch, invariant, unsupported, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Index.replaceOwner]

theorem sessionFinish_effect (pid : PeerId) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (counter : Nat)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[kp]? = some k) :
    Ensures (sessionFinish pid kp) (fun w => w.k.wg = some d ∧ w.k.keypairCounter = counter)
      (fun ok w => ok = true ∧ p.isDead = false ∧ p.handshakeEntryPeer ≠ none ∧
        w.k.keypairCounter = counter ∧ ∃ rotated,
        RotationRun pid { d with peers := d.peers.insert pid (sessionZeroPeer p) }
          (rotationPlan (sessionZeroPeer p) k.iAmTheInitiator kp) rotated ∧
        rotated.indexTable.any (·.owner == .handshake pid) = true ∧
        w.k.wg = some { rotated with indexTable := Index.replaceOwner pid kp rotated.indexTable }) := by
  let zeroed := { d with peers := d.peers.insert pid (sessionZeroPeer p) }
  have hz := handshakeZero_device_counter pid d p counter resident
  have ha := (ensures_iff _ _ _).mp (rotation_device_counter pid kp zeroed
    (sessionZeroPeer p) k counter (by simp [zeroed]) key)
  have hp := fun (rotated : Device) (found : rotated.peers[pid]? =
      some (rotationPeer (rotationPlan (sessionZeroPeer p) k.iAmTheInitiator kp) (sessionZeroPeer p))) =>
    (ensures_iff _ _ _).mp (sessionPublish_effect pid kp rotated _ counter found)
  rw [ensures_iff]
  mvcgen [sessionFinish, getPeer, getDev, getK, branch, invariant, unsupported, hz, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all only [Std.TreeMap.getElem?_insert_self, Option.some.injEq]
  all_goals try simp_all [zeroed, sessionZeroPeer]
  subst_vars
  intro s out hd hc steps found
  have hpub := hp out found
  mvcgen [hpub]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all only [rotationPeer_word]
  all_goals grind


def sessionPrepare (pid : PeerId) (st : Nat) (kp : KeypairId) : M Unit := do
  let p ← getPeer pid
  let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
  setKeypair kp { (← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex := p.remoteIndex }
  if ← branch .sessionInitiator initiator then deriveKeys kp true p.chainingKey
  else deriveKeys kp false p.chainingKey

theorem sessionAfterAllocation_prepare (pid : PeerId) (st : Nat) (kp : KeypairId) :
    Index.sessionAfterAllocation pid st kp =
      (sessionPrepare pid st kp >>= fun _ => sessionFinish pid kp) := by
  rw [sessionAfterAllocation_finish]
  have distribute {α β : Type} (q : Prop) [Decidable q] (a b : M α) (f : α → M β) :
      ((if q then a else b) >>= f) = (if q then a >>= f else b >>= f) := by
    split <;> rfl
  simp only [sessionPrepare, bind_assoc, distribute]

theorem sessionPrepare_effect (pid : PeerId) (st : Nat) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (counter : Nat)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[kp]? = some k) :
    Ensures (sessionPrepare pid st kp) (fun w => w.k.wg = some d ∧ w.k.keypairCounter = counter)
      (fun _ w => ∃ birth, w.k.wg = some (sessionDerivedDevice d kp p k st birth) ∧
        w.k.keypairCounter = counter) := by
  let assigned := { d with keypairs := d.keypairs.insert kp (sessionAssignedKey k p st) }
  have hd := (ensures_iff _ _ _).mp (deriveKeys_effect kp (st == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey
    assigned (sessionAssignedKey k p st) counter (by simp [assigned]))
  rw [ensures_iff]
  cases mode : (st == HANDSHAKE_CONSUMED_RESPONSE) <;>
    simp only [sessionPrepare, sessionAssignedKey, mode] at hd ⊢
  all_goals mvcgen [getPeer, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, invariant, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [sessionDerivedDevice, sessionAssignedKey, assigned]
  all_goals subst_vars
  all_goals mvcgen [hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [sessionDerivedDevice, sessionAssignedKey]
  all_goals have mode' : (st == HANDSHAKE_CONSUMED_RESPONSE) = false := by simpa using mode
  all_goals simp_all only [mode']
  all_goals grind

theorem sessionAfterAllocation_effect (pid : PeerId) (st : Nat) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (counter : Nat)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[kp]? = some k) :
    Ensures (Index.sessionAfterAllocation pid st kp)
      (fun w => w.k.wg = some d ∧ w.k.keypairCounter = counter)
      (fun ok w => ok = true ∧ p.isDead = false ∧ p.handshakeEntryPeer ≠ none ∧
        w.k.keypairCounter = counter ∧ ∃ birth rotated,
        RotationRun pid
          { (sessionDerivedDevice d kp p k st birth) with peers := d.peers.insert pid (sessionZeroPeer p) }
          (rotationPlan (sessionZeroPeer p) (st == HANDSHAKE_CONSUMED_RESPONSE) kp) rotated ∧
        rotated.indexTable.any (·.owner == .handshake pid) = true ∧
        w.k.wg = some { rotated with indexTable := Index.replaceOwner pid kp rotated.indexTable }) := by
  rw [sessionAfterAllocation_prepare]
  refine ensures_bind _ _ (sessionPrepare_effect pid st kp d p k counter resident key) ?_
  intro u w ok final pre run
  obtain ⟨birth, device, count⟩ := pre
  let dk := sessionDerivedKey (sessionAssignedKey k p st) (st == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth
  have hk : (sessionDerivedDevice d kp p k st birth).keypairs[kp]? = some dk := by
    simp [sessionDerivedDevice, dk]
  have hr : dk.iAmTheInitiator = (st == HANDSHAKE_CONSUMED_RESPONSE) := by
    simp [dk, sessionDerivedKey, sessionAssignedKey]
    split <;> rfl
  obtain ⟨yes, alive, word, counter', rotated, steps, hashed, out⟩ :=
    sessionFinish_effect pid kp (sessionDerivedDevice d kp p k st birth) p dk counter resident hk
      w ok final ⟨device, count⟩ run
  exact ⟨yes, alive, word, counter', birth, rotated, by simpa only [hr, sessionDerivedDevice] using steps, hashed, out⟩


theorem sessionAfterCreate_effect (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨ p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (created : Option KeypairId) :
    Ensures (Index.sessionAfterCreate pid p.handshakeState created)
      (fun w => match created with
        | none => w.k.wg = some d ∧ w.k.keypairCounter = counter
        | some kp => kp = d.nextKeypairId ∧
          w.k.wg = some (Index.createdDevice d counter p.handshakeEntryPeer) ∧ w.k.keypairCounter = counter + 1)
      (fun ok w => ∃ final, w.k.wg = some final ∧ SessionEffect pid d p counter ok final w.k.keypairCounter) := by
  cases created with
  | none =>
    rw [ensures_iff]
    mvcgen [Index.sessionAfterCreate, branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [SessionEffect]
  | some kp =>
    intro w ok final pre run
    obtain ⟨rfl, device, count⟩ := pre
    have hallocated : Ensures (Index.sessionAfterAllocation pid p.handshakeState d.nextKeypairId)
        (fun w => w.k.wg = some (Index.createdDevice d counter p.handshakeEntryPeer) ∧ w.k.keypairCounter = counter + 1)
        (fun ok w => ∃ final, w.k.wg = some final ∧ SessionEffect pid d p counter ok final w.k.keypairCounter) := by
      intro start result finish pre exec
      obtain ⟨rfl, alive, word, count', birth, rotated, steps, hashed, out⟩ :=
        sessionAfterAllocation_effect pid p.handshakeState d.nextKeypairId
          (Index.createdDevice d counter p.handshakeEntryPeer) p
          { internalId := counter + 1, peer := p.handshakeEntryPeer } (counter + 1)
          resident (by simp [Index.createdDevice]) start result finish pre exec
      refine ⟨_, out, accepted, alive, word, count', birth, rotated, ?_, hashed, rfl⟩
      simpa only [sessionPrepared, sessionDerivedDevice, Index.createdDevice] using steps
    have hs := (ensures_iff _ _ _).mp hallocated
    have wrapper : Ensures (Index.sessionAfterCreate pid p.handshakeState (some d.nextKeypairId))
        (fun w => w.k.wg = some (Index.createdDevice d counter p.handshakeEntryPeer) ∧ w.k.keypairCounter = counter + 1)
        (fun ok w => ∃ final, w.k.wg = some final ∧ SessionEffect pid d p counter ok final w.k.keypairCounter) := by
      rw [ensures_iff]
      mvcgen [Index.sessionAfterCreate, branch, invariant, hs]
    exact wrapper w ok final ⟨device, count⟩ run

/-- Exact accessor-source support: identify the returned resident peer, as well
as preserving its enclosing Device and counter (cf. Noise.AccessSource). -/
theorem sessionPeer_read (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p) :
    ⦃fun w => ⌜w.k.wg = some d ∧ w.k.keypairCounter = counter⌝⦄ getPeer pid
      ⦃⇓? result w => ⌜result = p ∧ w.k.wg = some d ∧ w.k.keypairCounter = counter⌝⦄ := by
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

/-- Full normal-return effect of the original entry point. No freshness or
operational execution witness is assumed. -/
theorem beginSession_effect (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p) :
    Ensures (beginSession pid) (fun w => w.k.wg = some d ∧ w.k.keypairCounter = counter)
      (fun ok w => ∃ final, w.k.wg = some final ∧ SessionEffect pid d p counter ok final w.k.keypairCounter) := by
  have hg := sessionPeer_read pid d p counter resident
  have hc := (ensures_iff _ _ _).mp (Index.keypairCreate_exact p.handshakeEntryPeer d counter)
  have hs := fun accepted created => (ensures_iff _ _ _).mp
    (sessionAfterCreate_effect pid d p counter resident accepted created)
  rw [Index.beginSession_owner_source, ensures_iff]
  mvcgen [IndexOwner.peerWord, WG.andM, branch, invariant, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all only [Option.some.injEq]
  all_goals subst_vars
  all_goals try simp_all [SessionEffect]
  all_goals mvcgen [hc, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

end Leanux.Proofs.WG.Noise
