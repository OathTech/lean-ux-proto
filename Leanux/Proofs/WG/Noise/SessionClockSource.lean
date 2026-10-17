import Leanux.Proofs.WG.Noise.SessionClockModel
import Leanux.Proofs.WG.Noise.SessionSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

def sessionClockAssign (pid : PeerId) (state : Nat) (kp : KeypairId) : WG.M SessionClockInput := do
  let p ← getPeer pid
  let initiator := state == HANDSHAKE_CONSUMED_RESPONSE
  setKeypair kp { (← getKeypair kp) with iAmTheInitiator := initiator, remoteIndex := p.remoteIndex }
  let role ← branch .sessionInitiator initiator
  return ⟨kp, role, p.chainingKey⟩

def sessionClockAfterCreate (pid : PeerId) (state : Nat) (created : Option KeypairId) :
    WG.M (Option SessionClockInput) := do
  if ← branch .sessionNoKeypair created.isNone then return none
  let some kp := created | invariant "unreachable"
  return some (← sessionClockAssign pid state kp)

/-- The actual admission/allocation/assignment prefix; no clock is consumed here. -/
def sessionClockPrefix (pid : PeerId) : WG.M (Option SessionClockInput) := do
  let state := (← getPeer pid).handshakeState
  if ← WG.andM (branch .sessionNotCreatedResponse (state != HANDSHAKE_CREATED_RESPONSE))
      (branch .sessionNotConsumedResponse (state != HANDSHAKE_CONSUMED_RESPONSE)) then return none
  let created ← keypairCreate (← IndexOwner.peerWord (.handshake pid))
  sessionClockAfterCreate pid state created

def deriveKeysAfterClock (kp : KeypairId) (initiator : Bool) (ck : List UInt8) (birth : Int64) : WG.M Unit := do
  let outs ← kdf true false ck []
  let sym (key : List UInt8) : SymmetricKey := {key, birthdate := birth, isValid := true}
  let first := sym (← kdfOut outs 0)
  let second := sym (← kdfOut outs 1)
  let k ← getKeypair kp
  setKeypair kp (if initiator then {k with sending := first, receiving := second}
    else {k with receiving := first, sending := second})

def sessionClockSuffix (pid : PeerId) : Option SessionClockInput → WG.M Bool
  | none => pure false
  | some input => do
    deriveKeys input.keypair input.initiator input.chainingKey
    sessionFinish pid input.keypair

theorem beginSession_clock_factor (pid : PeerId) :
    beginSession pid = (sessionClockPrefix pid >>= sessionClockSuffix pid) := by
  rw [Index.beginSession_owner_source]
  simp only [sessionClockPrefix, bind_assoc]
  congr 1
  funext p
  congr 1
  funext rejected
  cases rejected <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
  · congr 1
    funext word
    congr 1
    funext created
    simp only [Index.sessionAfterCreate, sessionClockAfterCreate, bind_assoc]
    congr 1
    funext failed
    cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind]
    · cases created with
      | none => rfl
      | some kp =>
        simp only [bind_assoc, pure_bind]
        change Index.sessionAfterAllocation pid p.handshakeState kp =
          (sessionClockAssign pid p.handshakeState kp >>= fun input => sessionClockSuffix pid (some input))
        rw [sessionAfterAllocation_finish]
        simp only [sessionClockAssign, bind_assoc, pure_bind]
        congr 1
        funext current
        congr 1
        funext key
        congr 1
        funext u
        congr 1
        funext initiator
        cases initiator <;> rfl
    · rfl
  · rfl

theorem deriveKeys_clock_factor (kp : KeypairId) (initiator : Bool) (ck : List UInt8) :
    deriveKeys kp initiator ck = (do
      let birth ← hiddenClock64 .deriveKeysBirthdate
      deriveKeysAfterClock kp initiator ck birth) := rfl

def SessionClockPrefixEffect (d : Device) (p : Peer) (counter : Nat)
    (input : Option SessionClockInput) (g : WGWorld) : Prop :=
  match input with
  | none => g.dev = some d ∧ g.keypairCounter = counter
  | some input =>
    (p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨ p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE) ∧
    input = ⟨d.nextKeypairId, p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE, p.chainingKey⟩ ∧
    g.dev = some (sessionClockAssigned d p counter) ∧ g.keypairCounter = counter + 1

theorem sessionClockPrefix_effect (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p) :
    Ensures (sessionClockPrefix pid) (fun g => g.dev = some d ∧ g.keypairCounter = counter)
      (SessionClockPrefixEffect d p counter) := by
  have afterCreate (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE) (created : Option KeypairId) :
      Ensures (sessionClockAfterCreate pid p.handshakeState created)
        (fun g => match created with
          | none => g.dev = some d ∧ g.keypairCounter = counter
          | some kp => kp = d.nextKeypairId ∧
            g.dev = some (Index.createdDevice d counter p.handshakeEntryPeer) ∧
            g.keypairCounter = counter + 1)
        (SessionClockPrefixEffect d p counter) := by
    cases created with
    | none =>
      intro g ambient result final after pre run
      simp [sessionClockAfterCreate, branch, AmbientM.branch] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre
    | some kp =>
      intro g ambient result final after pre run
      obtain ⟨rfl, device, count⟩ := pre
      simp [sessionClockAfterCreate, sessionClockAssign, getPeer, getKeypair, getDev,
        device, Index.createdDevice, resident, branch, AmbientM.branch, setKeypair,
        modifyDev] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨accepted, rfl, rfl, count⟩
  intro g ambient result final after pre run
  let first := {ambient with steps := ambient.steps.push {
    decision := .sessionNotCreatedResponse, outcome := p.handshakeState != HANDSHAKE_CREATED_RESPONSE,
    netRx := ambient.netRxSection}}
  let marked := if p.handshakeState != HANDSHAKE_CREATED_RESPONSE then
    {first with steps := first.steps.push {
      decision := .sessionNotConsumedResponse, outcome := p.handshakeState != HANDSHAKE_CONSUMED_RESPONSE,
      netRx := first.netRxSection}} else first
  have acceptedRun (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE) :
      ((sessionClockPrefix pid).run g).run ambient =
        (((do let key ← keypairCreate p.handshakeEntryPeer
              sessionClockAfterCreate pid p.handshakeState key) : WG.M _).run g).run marked := by
    rcases accepted with created | consumed
    · simp [sessionClockPrefix, getPeer, getDev, pre.1, resident, WG.andM,
        branch, AmbientM.branch, IndexOwner.peerWord, created, marked, first]
    · simp [sessionClockPrefix, getPeer, getDev, pre.1, resident, WG.andM,
        branch, AmbientM.branch, IndexOwner.peerWord, consumed, marked, first,
        HANDSHAKE_CREATED_RESPONSE, HANDSHAKE_CONSUMED_RESPONSE]
  by_cases created : p.handshakeState = HANDSHAKE_CREATED_RESPONSE
  · rw [acceptedRun (Or.inl created)] at run
    exact ensures_bind _ _ (Index.keypairCreate_exact p.handshakeEntryPeer d counter)
      (afterCreate (Or.inl created)) g marked result final after pre run
  · by_cases consumed : p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE
    · rw [acceptedRun (Or.inr consumed)] at run
      exact ensures_bind _ _ (Index.keypairCreate_exact p.handshakeEntryPeer d counter)
        (afterCreate (Or.inr consumed)) g marked result final after pre run
    · simp [sessionClockPrefix, getPeer, getDev, pre.1, resident, WG.andM,
        branch, AmbientM.branch, created, consumed] at run
      rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
      exact pre

theorem deriveKeysAfterClock_effect (kp : KeypairId) (initiator : Bool) (ck : List UInt8)
    (birth : Int64) (d : Device) (k : Keypair) (counter : Nat)
    (resident : d.keypairs[kp]? = some k) :
    Ensures (deriveKeysAfterClock kp initiator ck birth)
      (fun g => g.dev = some d ∧ g.keypairCounter = counter)
      (fun _ g => g.dev = some {d with keypairs := (d.keypairs.insert kp
          (sessionDerivedKey k initiator ck birth))} ∧ g.keypairCounter = counter) := by
  intro g ambient result final after pre run
  cases initiator <;>
    simp [deriveKeysAfterClock, kdf, WG.orM, branch, AmbientM.branch, sessionKdf_pair,
      kdfOut, getKeypair, getDev, pre.1, resident, setKeypair, modifyDev] at run
  all_goals rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  all_goals exact ⟨rfl, pre.2⟩

/-- Normal whole-call return supplies the actual clock boundary. Neither a
successful allocation nor a successful intermediate clock run is assumed. -/
theorem beginSession_clock_run (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p) (g final : WGWorld) (ambient after : Ambient)
    (ok : Bool) (device : g.dev = some d) (count : g.keypairCounter = counter)
    (run : ((beginSession pid).run g).run ambient = .ok ((ok, final), after)) :
    if ok then ∃ before beforeAmbient birth afterClock clockAmbient out,
      ((sessionClockPrefix pid).run g).run ambient = .ok ((some
        ⟨d.nextKeypairId, p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE, p.chainingKey⟩,
          before), beforeAmbient) ∧
      ((hiddenClock64 .deriveKeysBirthdate : WG.M Int64).run before).run beforeAmbient =
        .ok ((birth, afterClock), clockAmbient) ∧
      before.dev = some (sessionClockAssigned d p counter) ∧ afterClock = before ∧
      final.dev = some out ∧ SessionBirthEffect pid d p counter birth out final.keypairCounter
    else ((sessionClockPrefix pid).run g).run ambient = .ok ((none, final), after) ∧
      final.dev = some d ∧ final.keypairCounter = counter := by
  rw [beginSession_clock_factor] at run
  change (((sessionClockPrefix pid).run g).run ambient >>= fun ((input, current), middle) =>
    ((sessionClockSuffix pid input).run current).run middle) = _ at run
  cases prefixRun : ((sessionClockPrefix pid).run g).run ambient with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨input, before⟩, beforeAmbient⟩ := pair
    have effect := sessionClockPrefix_effect pid d p counter resident
      g ambient input before beforeAmbient ⟨device, count⟩ prefixRun
    rw [prefixRun] at run
    cases input with
    | none =>
      change Except.ok ((false, before), beforeAmbient) = _ at run
      cases run
      exact ⟨rfl, effect⟩
    | some input =>
      obtain ⟨accepted, rfl, beforeDevice, beforeCount⟩ := effect
      simp only [sessionClockSuffix, deriveKeys_clock_factor, bind_assoc] at run
      change (((hiddenClock64 .deriveKeysBirthdate : WG.M Int64).run before).run beforeAmbient >>=
        fun ((birth, afterClock), clockAmbient) =>
          ((do deriveKeysAfterClock d.nextKeypairId
                 (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth
               sessionFinish pid d.nextKeypairId).run afterClock).run clockAmbient) = _ at run
      cases clockRun : ((hiddenClock64 .deriveKeysBirthdate : WG.M Int64).run before).run beforeAmbient with
      | error stop => rw [clockRun] at run; cases run
      | ok pair =>
        obtain ⟨⟨birth, afterClock⟩, clockAmbient⟩ := pair
        have same := (ensures_iff _ _ _).mpr
          (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .deriveKeysBirthdate)
            (fun g : WGWorld => g = before))
          before beforeAmbient birth afterClock clockAmbient rfl clockRun
        subst afterClock
        rw [clockRun] at run
        let key := sessionAssignedKey {internalId := counter + 1, peer := p.handshakeEntryPeer}
          p p.handshakeState
        let derived := {sessionClockAssigned d p counter with keypairs :=
          ((sessionClockAssigned d p counter).keypairs.insert d.nextKeypairId
            (sessionDerivedKey key (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth))}
        have keyResident : (sessionClockAssigned d p counter).keypairs[d.nextKeypairId]? = some key := by
          simp [sessionClockAssigned, key]
        change (((deriveKeysAfterClock d.nextKeypairId (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE)
          p.chainingKey birth).run before).run clockAmbient >>= fun ((_, current), middle) =>
            ((sessionFinish pid d.nextKeypairId).run current).run middle) = _ at run
        cases deriveRun : ((deriveKeysAfterClock d.nextKeypairId
            (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth).run before).run clockAmbient with
        | error stop => rw [deriveRun] at run; cases run
        | ok pair =>
          obtain ⟨⟨u, prepared⟩, preparedAmbient⟩ := pair
          cases u
          rw [deriveRun] at run
          obtain ⟨preparedDevice, preparedCount⟩ := deriveKeysAfterClock_effect d.nextKeypairId
            (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth
            (sessionClockAssigned d p counter) key (counter + 1) keyResident
            before clockAmbient () prepared preparedAmbient ⟨beforeDevice, beforeCount⟩ deriveRun
          have preparedPeer : derived.peers[pid]? = some p := resident
          have preparedKey : derived.keypairs[d.nextKeypairId]? =
              some (sessionDerivedKey key (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth) := by
            simp [derived]
          obtain ⟨yes, alive, word, counted, rotated, rotation, hashed, output⟩ :=
            sessionFinish_effect pid d.nextKeypairId derived p _ (counter + 1)
              preparedPeer preparedKey prepared preparedAmbient ok final after
              ⟨preparedDevice, preparedCount⟩ run
          subst ok
          refine ⟨before, beforeAmbient, birth, before, clockAmbient, _, rfl,
            clockRun, beforeDevice, rfl, output, accepted, alive, word, counted,
            rotated, ?_, hashed, rfl⟩
          have role : (sessionDerivedKey key (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE)
              p.chainingKey birth).iAmTheInitiator =
              (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) := by
            simp [sessionDerivedKey, key, sessionAssignedKey]
            split <;> rfl
          simpa only [role, derived, sessionClockAssigned, sessionPrepared,
            sessionDerivedDevice, key, Index.createdDevice] using rotation

/-- A probe of the actual prefix and clock from the same complete Product
entry as the original session call. Reads retain all fixture observations. -/
def sessionClockPath (pid : PeerId) : Leanux.M (Option SessionClockReceipt) := do
  let input ← liftWG (sessionClockPrefix pid)
  match input with
  | none => return none
  | some input =>
    let before ← Campaign2.Product.read
    let birth ← liftWG (hiddenClock64 .deriveKeysBirthdate : WG.M Int64)
    let after ← Campaign2.Product.read
    return some ⟨input, before, birth, after⟩

end Leanux.Proofs.WG.Noise
