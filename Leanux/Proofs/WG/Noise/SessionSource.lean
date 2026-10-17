import Leanux.Proofs.WG.Noise.SessionModel
import Leanux.Proofs.WG.Noise.SessionFrames
import Leanux.Proofs.WG.Index.SessionOperations
import Leanux.Proofs.WG.Index.Table

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.WG.Config Std.Do

theorem sessionKdf_pair (ck : List UInt8) :
    kdfOutputs ck [] 2 = [sessionFirst ck, sessionSecond ck] := by
  simp [kdfOutputs, sessionFirst, sessionSecond, List.range']

theorem sessionKdf_returns (ck : List UInt8) (P : WGWorld → Prop) :
    ⦃fun w => ⌜P w⌝⦄ kdf true false ck []
      ⦃⇓ outs w => ⌜outs = [sessionFirst ck, sessionSecond ck] ∧ P w⌝⦄ := by
  apply (returns_iff _ _ _).mp
  intro g ambient pre
  let mark (a : Ambient) (decision : Decision) (outcome : Bool) : Ambient :=
    {a with steps := a.steps.push {decision, outcome, netRx := a.netRxSection}}
  let after := mark (mark (mark (mark (mark ambient .kdfNoFirstDst false)
    .kdfNoFirstLen false) .kdfNoSecondDst false) .kdfNoSecondLen false) .kdfNoThirdDst true
  refine ⟨[sessionFirst ck, sessionSecond ck], g, after, ?_, rfl, pre⟩
  simp [kdf, WG.orM, branch, AmbientM.branch, sessionKdf_pair, after, mark]
  rfl

theorem deriveKeys_effect (kp : KeypairId) (initiator : Bool) (ck : List UInt8)
    (d : Device) (k : Keypair) (counter : Nat) (resident : d.keypairs[kp]? = some k) :
    Ensures (deriveKeys kp initiator ck)
      (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun _ w => ∃ birth, w.dev = some { d with
        keypairs := d.keypairs.insert kp (sessionDerivedKey k initiator ck birth) } ∧ w.keypairCounter = counter) := by
  unfold deriveKeys
  refine ensures_bind (Q := fun _ g => g.dev = some d ∧ g.keypairCounter = counter) _ _ ?_ ?_
  · exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
      (AmbientM.hiddenClock64 .deriveKeysBirthdate) _)
  · intro birth g ambient result final after pre run
    cases initiator <;>
      simp [kdf, WG.orM, branch, AmbientM.branch, sessionKdf_pair, kdfOut,
        getKeypair, getDev, pre.1, resident, setKeypair, modifyDev] at run
    all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    all_goals exact ⟨birth, rfl, pre.2⟩

/-- The original publication suffix after rotation, including both stopping guards. -/
def sessionPublish (pid : PeerId) (kp : KeypairId) : WG.M Bool := do
  _ ← IndexOwner.peerDeref (.handshake pid)
  if !(← indexReplaceHandshake pid kp) then unsupported "begin_session: the handshake entry was unhashed"
  return true

def sessionFinish (pid : PeerId) (kp : KeypairId) : WG.M Bool := do
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
    ⦃fun w => ⌜w.dev = some d ∧ w.keypairCounter = counter⌝⦄ handshakeZero pid
      ⦃⇓? _ w => ⌜w.dev = some { d with peers := d.peers.insert pid (sessionZeroPeer p) } ∧
        w.keypairCounter = counter⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  simp [handshakeZero, getPeer, getDev, pre.1, resident, setPeer, modifyDev] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨rfl, pre.2⟩

theorem rotation_device_counter (pid : PeerId) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (counter : Nat)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[kp]? = some k) :
    Ensures (addNewKeypair pid kp) (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun _ w => ∃ final, w.dev = some final ∧ w.keypairCounter = counter ∧
        RotationRun pid d (rotationPlan p k.iAmTheInitiator kp) final ∧
        final.peers[pid]? = some (rotationPeer (rotationPlan p k.iAmTheInitiator kp) p)) := by
  intro w ambient result final after pre run
  obtain ⟨out, device, effect⟩ :=
    addNewKeypair_effect pid kp d p k resident key w ambient result final after pre.1 run
  exact ⟨out, device, (ensures_iff _ _ _).mpr (addNewKeypair_counter pid kp counter)
    w ambient result final after pre.2 run, effect, rotationRun_peer effect p resident⟩

theorem sessionPublish_effect (pid : PeerId) (kp : KeypairId) (d : Device)
    (p : Peer) (counter : Nat) (resident : d.peers[pid]? = some p) :
    Ensures (sessionPublish pid kp) (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun ok w => ok = true ∧ p.handshakeEntryPeer ≠ none ∧
        d.indexTable.any (·.owner == .handshake pid) = true ∧
        w.dev = some { d with indexTable := Index.replaceOwner pid kp d.indexTable } ∧
        w.keypairCounter = counter) := by
  intro g ambient result final after pre run
  have lifted : (monadLift (indexReplaceHandshake pid kp) : WG.M Bool) =
      liftIndex (indexReplaceHandshake pid kp) := rfl
  simp only [sessionPublish, lifted] at run
  cases word : p.handshakeEntryPeer with
  | none =>
    simp [IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev,
      pre.1, resident, word, unsupported, AmbientM.unsupported] at run
    cases run
  | some owner =>
    cases hashed : d.indexTable.any (·.owner == .handshake pid) with
    | false =>
      simp [IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev, pre.1, resident,
        word, indexReplaceHandshake, indexHashed, liftIndex, branch, AmbientM.branch,
        modifyDev, hashed, unsupported, AmbientM.unsupported, -List.any_eq_false] at run
      cases run
    | true =>
      simp [IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev, pre.1, resident,
        word, indexReplaceHandshake, indexHashed, liftIndex, branch, AmbientM.branch,
        modifyDev, hashed, -List.any_eq_false] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, by simp, rfl, by simp [Index.replaceOwner], pre.2⟩

theorem sessionFinish_effect (pid : PeerId) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (counter : Nat)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[kp]? = some k) :
    Ensures (sessionFinish pid kp) (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun ok w => ok = true ∧ p.isDead = false ∧ p.handshakeEntryPeer ≠ none ∧
        w.keypairCounter = counter ∧ ∃ rotated,
        RotationRun pid { d with peers := d.peers.insert pid (sessionZeroPeer p) }
          (rotationPlan (sessionZeroPeer p) k.iAmTheInitiator kp) rotated ∧
        rotated.indexTable.any (·.owner == .handshake pid) = true ∧
        w.dev = some { rotated with indexTable := Index.replaceOwner pid kp rotated.indexTable }) := by
  intro g ambient result final after pre run
  let zeroed := {d with peers := d.peers.insert pid (sessionZeroPeer p)}
  let start := {g with dev := some zeroed}
  let marked := {ambient with steps := ambient.steps.push {
    decision := .sessionAlive, outcome := !p.isDead, netRx := ambient.netRxSection}}
  have source : ((sessionFinish pid kp).run g).run ambient =
      (((if !p.isDead then do addNewKeypair pid kp; sessionPublish pid kp
          else unsupported "a dead peer finishing a session") : WG.M Bool).run start).run marked := by
    simp [sessionFinish, handshakeZero, getPeer, getDev, pre.1, resident,
      setPeer, modifyDev, branch, AmbientM.branch, start, zeroed, sessionZeroPeer, marked]
  rw [source] at run
  cases alive : p.isDead with
  | true =>
    simp [alive, unsupported, AmbientM.unsupported] at run
    cases run
  | false =>
    simp only [alive, Bool.not_false, ite_true] at run
    have effect : Ensures (do addNewKeypair pid kp; sessionPublish pid kp)
        (fun w => w.dev = some zeroed ∧ w.keypairCounter = counter)
        (fun ok w => ok = true ∧ p.handshakeEntryPeer ≠ none ∧ w.keypairCounter = counter ∧
          ∃ rotated, RotationRun pid zeroed (rotationPlan (sessionZeroPeer p) k.iAmTheInitiator kp) rotated ∧
            rotated.indexTable.any (·.owner == .handshake pid) = true ∧
            w.dev = some {rotated with indexTable := Index.replaceOwner pid kp rotated.indexTable}) := by
      refine ensures_bind _ _ (rotation_device_counter pid kp zeroed (sessionZeroPeer p)
        k counter (by simp [zeroed]) key) ?_
      intro u w a ok finish b h exec
      obtain ⟨rotated, device, count, steps, found⟩ := h
      obtain ⟨yes, word, hashed, out, counted⟩ :=
        sessionPublish_effect pid kp rotated _ counter found w a ok finish b ⟨device, count⟩ exec
      exact ⟨yes, by simpa [rotationPeer_word, sessionZeroPeer] using word,
        counted, rotated, steps, hashed, out⟩
    obtain ⟨yes, word, count, rotated, steps, hashed, out⟩ :=
      effect start marked result final after ⟨rfl, pre.2⟩ run
    exact ⟨yes, rfl, word, count, rotated, steps, hashed, out⟩

def sessionPrepare (pid : PeerId) (st : Nat) (kp : KeypairId) : WG.M Unit := do
  let p ← getPeer pid
  let initiator := st == HANDSHAKE_CONSUMED_RESPONSE
  setKeypair kp { (← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex := p.remoteIndex }
  if ← branch .sessionInitiator initiator then deriveKeys kp true p.chainingKey
  else deriveKeys kp false p.chainingKey

theorem sessionAfterAllocation_prepare (pid : PeerId) (st : Nat) (kp : KeypairId) :
    Index.sessionAfterAllocation pid st kp =
      (sessionPrepare pid st kp >>= fun _ => sessionFinish pid kp) := by
  rw [sessionAfterAllocation_finish]
  have distribute {α β : Type} (q : Prop) [Decidable q] (a b : WG.M α) (f : α → WG.M β) :
      ((if q then a else b) >>= f) = (if q then a >>= f else b >>= f) := by
    split <;> rfl
  simp only [sessionPrepare, bind_assoc, distribute]

theorem sessionPrepare_effect (pid : PeerId) (st : Nat) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (counter : Nat)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[kp]? = some k) :
    Ensures (sessionPrepare pid st kp) (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun _ w => ∃ birth, w.dev = some (sessionDerivedDevice d kp p k st birth) ∧
        w.keypairCounter = counter) := by
  intro g ambient result final after pre run
  let assigned := {d with keypairs := d.keypairs.insert kp (sessionAssignedKey k p st)}
  let start := {g with dev := some assigned}
  let marked := {ambient with steps := ambient.steps.push {
    decision := .sessionInitiator, outcome := st == HANDSHAKE_CONSUMED_RESPONSE,
    netRx := ambient.netRxSection}}
  have source : ((sessionPrepare pid st kp).run g).run ambient =
      ((deriveKeys kp (st == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey).run start).run marked := by
    cases mode : st == HANDSHAKE_CONSUMED_RESPONSE <;>
      simp [sessionPrepare, getPeer, getKeypair, getDev, pre.1, resident, key,
        setKeypair, modifyDev, branch, AmbientM.branch, mode, start, assigned, sessionAssignedKey, marked]
    all_goals rfl
  rw [source] at run
  obtain ⟨birth, device, count⟩ :=
    deriveKeys_effect kp (st == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey assigned
      (sessionAssignedKey k p st) counter (by simp [assigned])
      start marked result final after ⟨rfl, pre.2⟩ run
  exact ⟨birth, by simpa [sessionDerivedDevice, assigned] using device, count⟩

theorem sessionAfterAllocation_effect (pid : PeerId) (st : Nat) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (counter : Nat)
    (resident : d.peers[pid]? = some p) (key : d.keypairs[kp]? = some k) :
    Ensures (Index.sessionAfterAllocation pid st kp)
      (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun ok w => ok = true ∧ p.isDead = false ∧ p.handshakeEntryPeer ≠ none ∧
        w.keypairCounter = counter ∧ ∃ birth rotated,
        RotationRun pid
          { (sessionDerivedDevice d kp p k st birth) with peers := d.peers.insert pid (sessionZeroPeer p) }
          (rotationPlan (sessionZeroPeer p) (st == HANDSHAKE_CONSUMED_RESPONSE) kp) rotated ∧
        rotated.indexTable.any (·.owner == .handshake pid) = true ∧
        w.dev = some { rotated with indexTable := Index.replaceOwner pid kp rotated.indexTable }) := by
  rw [sessionAfterAllocation_prepare]
  refine ensures_bind _ _ (sessionPrepare_effect pid st kp d p k counter resident key) ?_
  intro u w ambient ok final after pre run
  obtain ⟨birth, device, count⟩ := pre
  let dk := sessionDerivedKey (sessionAssignedKey k p st) (st == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth
  have hk : (sessionDerivedDevice d kp p k st birth).keypairs[kp]? = some dk := by
    simp [sessionDerivedDevice, dk]
  have hr : dk.iAmTheInitiator = (st == HANDSHAKE_CONSUMED_RESPONSE) := by
    simp [dk, sessionDerivedKey, sessionAssignedKey]
    split <;> rfl
  obtain ⟨yes, alive, word, counter', rotated, steps, hashed, out⟩ :=
    sessionFinish_effect pid kp (sessionDerivedDevice d kp p k st birth) p dk counter resident hk
      w ambient ok final after ⟨device, count⟩ run
  exact ⟨yes, alive, word, counter', birth, rotated,
    by simpa only [hr, sessionDerivedDevice] using steps, hashed, out⟩

theorem sessionAfterCreate_effect (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨ p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (created : Option KeypairId) :
    Ensures (Index.sessionAfterCreate pid p.handshakeState created)
      (fun w => match created with
        | none => w.dev = some d ∧ w.keypairCounter = counter
        | some kp => kp = d.nextKeypairId ∧
          w.dev = some (Index.createdDevice d counter p.handshakeEntryPeer) ∧ w.keypairCounter = counter + 1)
      (fun ok w => ∃ final, w.dev = some final ∧ SessionEffect pid d p counter ok final w.keypairCounter) := by
  cases created with
  | none =>
    intro g ambient result final after pre run
    simp [Index.sessionAfterCreate, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨d, pre.1, rfl, pre.2⟩
  | some kp =>
    intro g ambient result final after pre run
    obtain ⟨rfl, device, count⟩ := pre
    let marked := {ambient with steps := ambient.steps.push {
      decision := .sessionNoKeypair, outcome := false, netRx := ambient.netRxSection}}
    have source : ((Index.sessionAfterCreate pid p.handshakeState (some d.nextKeypairId)).run g).run ambient =
        ((Index.sessionAfterAllocation pid p.handshakeState d.nextKeypairId).run g).run marked := by
      simp [Index.sessionAfterCreate, branch, AmbientM.branch, marked]
    rw [source] at run
    obtain ⟨rfl, alive, word, count', birth, rotated, steps, hashed, out⟩ :=
      sessionAfterAllocation_effect pid p.handshakeState d.nextKeypairId
        (Index.createdDevice d counter p.handshakeEntryPeer) p
        {internalId := counter + 1, peer := p.handshakeEntryPeer} (counter + 1)
        resident (by simp [Index.createdDevice]) g marked result final after ⟨device, count⟩ run
    refine ⟨_, out, accepted, alive, word, count', birth, rotated, ?_, hashed, rfl⟩
    simpa only [sessionPrepared, sessionDerivedDevice, Index.createdDevice] using steps

/-- Exact accessor-source support: identify the returned resident peer, as well
as preserving its enclosing Device and counter (cf. Noise.AccessSource). -/
theorem sessionPeer_read (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p) :
    ⦃fun w => ⌜w.dev = some d ∧ w.keypairCounter = counter⌝⦄ getPeer pid
      ⦃⇓? result w => ⌜result = p ∧ w.dev = some d ∧ w.keypairCounter = counter⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  simp [getPeer, getDev, pre.1, resident] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact ⟨rfl, pre⟩

/-- Full normal-return effect of the original entry point. No freshness or
operational execution witness is assumed. -/
theorem beginSession_effect (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p) :
    Ensures (beginSession pid) (fun w => w.dev = some d ∧ w.keypairCounter = counter)
      (fun ok w => ∃ final, w.dev = some final ∧ SessionEffect pid d p counter ok final w.keypairCounter) := by
  intro g ambient result final after pre run
  let first := {ambient with steps := ambient.steps.push {
    decision := .sessionNotCreatedResponse, outcome := p.handshakeState != HANDSHAKE_CREATED_RESPONSE,
    netRx := ambient.netRxSection}}
  let marked := if p.handshakeState != HANDSHAKE_CREATED_RESPONSE then
    {first with steps := first.steps.push {
      decision := .sessionNotConsumedResponse, outcome := p.handshakeState != HANDSHAKE_CONSUMED_RESPONSE,
      netRx := first.netRxSection}} else first
  by_cases created : p.handshakeState = HANDSHAKE_CREATED_RESPONSE
  · have source : ((beginSession pid).run g).run ambient =
        (((do let key ← keypairCreate p.handshakeEntryPeer
              Index.sessionAfterCreate pid p.handshakeState key) : WG.M Bool).run g).run marked := by
      rw [Index.beginSession_owner_source]
      simp [getPeer, getDev, pre.1, resident, WG.andM, branch, AmbientM.branch,
        IndexOwner.peerWord, created, marked, first]
    rw [source] at run
    exact ensures_bind _ _ (Index.keypairCreate_exact p.handshakeEntryPeer d counter)
      (fun key => sessionAfterCreate_effect pid d p counter resident (Or.inl created) key)
      g marked result final after pre run
  · by_cases consumed : p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE
    · have source : ((beginSession pid).run g).run ambient =
          (((do let key ← keypairCreate p.handshakeEntryPeer
                Index.sessionAfterCreate pid p.handshakeState key) : WG.M Bool).run g).run marked := by
        rw [Index.beginSession_owner_source]
        simp [getPeer, getDev, pre.1, resident, WG.andM, branch, AmbientM.branch,
          IndexOwner.peerWord, consumed, marked, first, HANDSHAKE_CREATED_RESPONSE,
          HANDSHAKE_CONSUMED_RESPONSE]
      rw [source] at run
      exact ensures_bind _ _ (Index.keypairCreate_exact p.handshakeEntryPeer d counter)
        (fun key => sessionAfterCreate_effect pid d p counter resident (Or.inr consumed) key)
        g marked result final after pre run
    · rw [Index.beginSession_owner_source] at run
      simp [getPeer, getDev, pre.1, resident, WG.andM, branch, AmbientM.branch,
        created, consumed] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨d, pre.1, rfl, pre.2⟩

end Leanux.Proofs.WG.Noise
