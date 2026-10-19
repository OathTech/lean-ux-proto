import Leanux.Proofs.WG.Roaming.ResponseCryptoEffects
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Noise.Execution

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original response consumer after the captured read-lock values.
Only its successful return is decorated; all failed-consumption puts remain. -/
def responseConsumeTailWithDh (dh : Bool → List UInt8 → List UInt8 → List UInt8 → WG.M (Option (List UInt8 × List UInt8)))
    (msg : List UInt8) (input : ResponseInput) : WG.M (Option ResponseConsumed) := do
  let identity := input.identity
  let pid := input.pid
  let p := input.peer
  let state := p.handshakeState
  let fail : WG.M (Option ResponseConsumed) := do
    peerPut (some pid)
    return none
  let eph := (msg.drop 12).take 32
  let (ck, h) ← messageEphemeral true eph p.chainingKey p.hash
  let ee ← dh false ck p.ephemeralPrivate eph
  if ← branch .crespEeFailed ee.isNone then return ← fail
  let some (ck, _) := ee | invariant "unreachable"
  let se ← dh false ck identity.staticPrivate eph
  if ← branch .crespSeFailed se.isNone then return ← fail
  let some (ck, _) := se | invariant "unreachable"
  let outs ← kdf true true ck p.presharedKey
  let (ck, tempHash, key) := (← kdfOut outs 0, ← kdfOut outs 1, ← kdfOut outs 2)
  let h := noiseHash (h ++ tempHash)
  let dec ← messageDecrypt ((msg.drop 44).take 16) key h
  if ← branch .crespDecryptFailed dec.isNone then return ← fail
  let some (_, h) := dec | invariant "unreachable"
  let checked ← getPeer pid
  if ← branch .crespStateChanged (checked.handshakeState != state) then return ← fail
  setPeer pid { (← getPeer pid) with remoteEphemeral := eph, hash := h, chainingKey := ck, remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE }
  return some ⟨input, checked, ← Campaign2.read⟩

/-- Original response tail retained as the actual DH specialization. -/
def responseConsumeTail (msg : List UInt8) (input : ResponseInput) : WG.M (Option ResponseConsumed) :=
  responseConsumeTailWithDh mixDh msg input

theorem responseConsumeTailWithDh_original (msg : List UInt8) (input : ResponseInput) :
    responseConsumeTailWithDh mixDh msg input = responseConsumeTail msg input := rfl

/-- Captures the actual lookup owner independently of its referenced peer. -/
def responseConsumeWithTail
    (tail : List UInt8 → ResponseInput → WG.M (Option ResponseConsumed))
    (msg : List UInt8) : WG.M (Option ResponseConsumed) := do
  let identity := (← getDev).staticIdentity
  if ← branch .crespNoIdentity !identity.hasIdentity then return none
  let entry ← indexLookup [.handshake] (u32le msg 8)
  if ← branch .crespNoHandshake entry.isNone then return none
  let some (IndexOwner.handshake owner, pid) := entry |
    invariant "a keypair entry under the handshake mask"
  let p ← getPeer pid
  if ← branch .crespNotCreatedInitiation (p.handshakeState != HANDSHAKE_CREATED_INITIATION) then
    peerPut (some pid)
    return none
  tail msg ⟨identity, owner, pid, p⟩

/-- Original lookup/guard observer with its original tail. -/
def responseConsume (msg : List UInt8) : WG.M (Option ResponseConsumed) :=
  responseConsumeWithTail responseConsumeTail msg

theorem responseConsumeWithTail_original (msg : List UInt8) :
    responseConsumeWithTail responseConsumeTail msg = responseConsume msg := rfl

def responsePeer (out : Option ResponseConsumed) : Option PeerId :=
  out.map fun cut => cut.input.pid

/-- Exact erasure of the successful transcript, including every failing branch. -/
theorem responseConsume_erase (msg : List UInt8) :
    (do let out ← responseConsume msg; pure (responsePeer out)) = consumeResponse msg := by
  simp only [responseConsume, responseConsumeWithTail, responseConsumeTail, responseConsumeTailWithDh, consumeResponse, bind_assoc]
  congr 1
  funext d
  congr 1
  funext noIdentity
  cases noIdentity <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc, responsePeer, Option.map_none]
  all_goals try rfl
  congr 1
  funext entry
  congr 1
  funext missing
  cases missing <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, Option.map_none]
  all_goals try rfl
  cases entry with
  | none => rfl
  | some pair =>
    rcases pair with ⟨owner, pid⟩
    cases owner with
    | keypair id => rfl
    | handshake owner =>
      simp only [bind_assoc]
      congr 1
      funext p
      congr 1
      funext wrong
      cases wrong <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc, Option.map_none]
      all_goals try rfl
      congr 1
      funext ephemeral
      rcases ephemeral with ⟨ck, hash⟩
      congr 1
      funext ee
      congr 1
      funext failed
      cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
      all_goals try rfl
      cases ee with
      | none => rfl
      | some pair =>
        rcases pair with ⟨ck, unused⟩
        simp only [bind_assoc]
        congr 1
        funext se
        congr 1
        funext failed
        cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
        all_goals try rfl
        cases se with
        | none => rfl
        | some pair =>
          rcases pair with ⟨ck, unused⟩
          simp only [bind_assoc]
          congr 1
          funext outs
          congr 1
          funext ck
          congr 1
          funext tempHash
          congr 1
          funext key
          congr 1
          funext dec
          congr 1
          funext failed
          cases failed <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
          all_goals try rfl
          cases dec with
          | none => rfl
          | some pair =>
            rcases pair with ⟨plain, hash⟩
            simp only [bind_assoc]
            congr 1
            funext checked
            congr 1
            funext changed
            cases changed <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
            all_goals try rfl



theorem responseConsumeTail_facts (msg : List UInt8) (input : ResponseInput)
    (identity : input.identity.hasIdentity = true)
    (state : input.peer.handshakeState = HANDSHAKE_CREATED_INITIATION) :
    Campaign2.Ensures (responseConsumeTail msg input) (fun _ => True)
      (fun result observed => ∀ cut, result = some cut → cut.input = input ∧
        cut.committed = observed ∧ ResponseConsumedFacts msg cut) := by
  intro g ambient result final after _ run cut returned
  subst result
  have fail (start : WGWorld) (before : Ambient) (done : WGWorld) (last : Ambient)
      (value : ResponseConsumed) :
      ((do peerPut (some input.pid); pure (none : Option ResponseConsumed) : WG.M _).run start).run before ≠
        .ok ((some value, done), last) := by
    intro execution
    change (((peerPut (some input.pid)).run start).run before >>= fun ((_, current), next) =>
      Except.ok ((none, current), next)) = _ at execution
    cases put : ((peerPut (some input.pid)).run start).run before with
    | error err => rw [put] at execution; cases execution
    | ok pair => rw [put] at execution; cases execution
  cases ee : (curve25519 input.peer.ephemeralPrivate (responseEphemeral msg)).2 <;>
    cases se : (curve25519 input.identity.staticPrivate (responseEphemeral msg)).2 <;>
    cases decrypted : aeadDecrypt (responseKey msg input.identity input.peer) noiseNonce
      ((msg.drop 44).take 16) (responseAad msg input.identity input.peer)
  all_goals
    simp only [responseEphemeral, responseEeChain, responseSeChain, responseAad, responseKey] at ee se decrypted
    simp [responseConsumeTail, responseConsumeTailWithDh, messageEphemeral, mixDh, messageDecrypt, kdf, responseKdf_one,
      responseKdf_three, kdfOut, WG.orM, branch, AmbientM.branch, ee, se, decrypted] at run
  all_goals first
    | exact False.elim (fail _ _ _ _ _ run)
    | skip
  all_goals
    cases device : g.dev with
    | none =>
      simp [getPeer, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident : d.peers[input.pid]? with
      | none =>
        simp [getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases changed : p.handshakeState = input.peer.handshakeState
        · simp [getPeer, getDev, device, resident, changed,
            setPeer, modifyDev] at run
          rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
          refine ⟨rfl, rfl, ?_⟩
          have empty := responseDecrypt_empty msg
            (responseKey msg input.identity input.peer)
            (responseAad msg input.identity input.peer) _ (by
              simpa [responseKey, responseAad, responseSeChain, responseEeChain, responseEphemeral] using decrypted)
          subst_vars
          simp [ResponseConsumedFacts, ResponseCrypto, identity, state, changed,
            Campaign2.snapshot, Campaign2.core,
            responseKey, responseAad, responseSeChain, responseEeChain, responseEphemeral,
            ee, se, decrypted]
        · simp [getPeer, getDev, device, resident, changed] at run
          exact False.elim (fail _ _ _ _ _ run)

end Leanux.Proofs.WG.Roaming
