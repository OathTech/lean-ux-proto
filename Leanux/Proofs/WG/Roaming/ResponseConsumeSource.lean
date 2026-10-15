import Leanux.Proofs.WG.Roaming.ResponseCryptoSource
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.Proofs.WG.Roaming.PublicationFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- The original response consumer after the captured read-lock values.
Only its successful return is decorated; all failed-consumption puts remain. -/
def responseConsumeTail (msg : List UInt8) (input : ResponseInput) : M (Option ResponseConsumed) := do
  let identity := input.identity
  let pid := input.pid
  let p := input.peer
  let state := p.handshakeState
  let fail : M (Option ResponseConsumed) := do
    peerPut (some pid)
    return none
  let eph := (msg.drop 12).take 32
  let (ck, h) ← messageEphemeral true eph p.chainingKey p.hash
  let ee ← mixDh false ck p.ephemeralPrivate eph
  if ← branch .crespEeFailed ee.isNone then return ← fail
  let some (ck, _) := ee | invariant "unreachable"
  let se ← mixDh false ck identity.staticPrivate eph
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

/-- Captures the actual lookup owner independently of its referenced peer. -/
def responseConsume (msg : List UInt8) : M (Option ResponseConsumed) := do
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
  responseConsumeTail msg ⟨identity, owner, pid, p⟩

def responsePeer (out : Option ResponseConsumed) : Option PeerId :=
  out.map fun cut => cut.input.pid

/-- Exact erasure of the successful transcript, including every failing branch. -/
theorem responseConsume_erase (msg : List UInt8) :
    (do let out ← responseConsume msg; pure (responsePeer out)) = consumeResponse msg := by
  simp only [responseConsume, responseConsumeTail, consumeResponse, bind_assoc, pure_bind]
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
  cases missing <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc, responsePeer, Option.map_none]
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
      cases wrong <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc, responsePeer, Option.map_none]
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
        simp only [bind_assoc, pure_bind]
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
          simp only [bind_assoc, pure_bind]
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
            simp only [bind_assoc, pure_bind]
            congr 1
            funext checked
            congr 1
            funext changed
            cases changed <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind, bind_assoc]
            all_goals try rfl

theorem responseConsumeTail_facts (msg : List UInt8) (input : ResponseInput)
    (identity : input.identity.hasIdentity = true)
    (state : input.peer.handshakeState = HANDSHAKE_CREATED_INITIATION) :
    Ensures (responseConsumeTail msg input) (fun _ => True)
      (fun result w => ∀ cut, result = some cut → cut.input = input ∧
        cut.committed = Campaign2.snapshot w ∧ ResponseConsumedFacts msg cut) := by
  rw [ensures_iff]
  have he := responseEphemeral_returns ((msg.drop 12).take 32) input.peer.chainingKey input.peer.hash (fun _ => True)
  have hd := fun ck priv pub => responseDh_returns ck priv pub (fun _ => True)
  have hk := fun ck data => responseKdf_three_returns ck data (fun _ => True)
  have hm := fun sealed key hash => responseDecrypt_returns sealed key hash (fun _ => True)
  have hp : ⦃fun _ => ⌜True⌝⦄ peerPut (some input.pid) ⦃⇓? _ _ => ⌜True⌝⦄ := by
    apply (ensures_iff _ _ _).mp
    intro w x final pre run
    trivial
  mvcgen [responseConsumeTail, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    branch, invariant, kdfOut, Campaign2.read, he, hd, hk, hm, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [ResponseConsumedFacts, ResponseCrypto, responseEphemeral,
    responseEeChain, responseSeChain, responseAad, responseKey,
    Campaign2.snapshot, Campaign2.core, Std.TreeMap.getElem?_insert]
  all_goals grind [responseDecrypt_empty]

end Leanux.Proofs.WG.Roaming
