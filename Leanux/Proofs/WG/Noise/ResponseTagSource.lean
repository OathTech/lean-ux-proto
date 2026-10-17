import Leanux.Proofs.WG.Noise.ResponseTagFrames
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.Roaming.ResponseConsumeSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

/-- Exact all-peer tag effects of the actual response consumer, including
normal rejection cleanup. The initial tag map is a data observation. -/
theorem consumeResponse_tagMap (msg : List UInt8) (entry : Option Device) :
    Ensures (consumeResponse msg) (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun result g => ∀target, responseTagMap g.dev target =
        if result = some target then some HANDSHAKE_CONSUMED_RESPONSE else responseTagMap entry target) := by
  let safe : WGWorld → Prop := fun g => responseTagMap g.dev = responseTagMap entry
  let effect : Option PeerId → WGWorld → Prop := fun result g => ∀target,
    responseTagMap g.dev target =
      if result = some target then some HANDSHAKE_CONSUMED_RESPONSE else responseTagMap entry target
  let R : Option Roaming.ResponseConsumed → WGWorld → Prop :=
    fun out => effect (Roaming.responsePeer out)
  change Ensures (consumeResponse msg) safe effect
  have hstop {α : Type} (P : WGWorld → Prop) (message : String) (Q : α → WGWorld → Prop) :
      Ensures (invariant message : WG.M α) P Q := by
    intro g a r final after pre run; cases run
  have hbranch (P : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hread (P : WGWorld → Prop) (pid : PeerId) :
      Ensures (getPeer pid) P (fun _ => P) := by
    intro g a r final after pre run
    exact (((ensures_iff _ _ _).mpr (getPeer_spec pid P)) g a r final after pre run).1
  have hdev : Ensures getDev safe (fun _ => safe) := by
    intro g a r final after pre run
    cases device : g.dev with
    | none => simp [getDev, device, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, device] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hsnapshot (P : WGWorld → Prop) : Ensures Campaign2.read P (fun _ => P) := by
    intro g a r final after pre run; cases run; exact pre
  have hnone : Ensures (pure (none : Option Roaming.ResponseConsumed) : WG.M _) safe R := by
    intro g a r final after pre run
    cases run
    intro target
    simpa [R,effect,Roaming.responsePeer] using congrFun pre target
  have hfail (pid : PeerId) :
      Ensures (do peerPut (some pid); pure (none : Option Roaming.ResponseConsumed))
        (ResponseTagHeld entry pid) R :=
    ensures_bind _ _ (peerPut_spec_responseTagMap_variant entry pid) (fun _ => hnone)
  have hcommit (pid : PeerId) (f : Peer → Peer)
      (tag : ∀p, (f p).handshakeState = HANDSHAKE_CONSUMED_RESPONSE) :
      Ensures (modifyPeer pid f) (ResponseTagHeld entry pid)
        (fun _ => effect (some pid)) := by
    intro g ambient result final after pre run
    obtain ⟨same,d,p,device,resident,_⟩ := pre
    change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
    simp [getPeer, getDev, device, resident, setPeer, modifyDev] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    intro target
    by_cases equal : pid = target
    · subst target
      simp [responseTagMap,tag]
    · have prior := congrFun same target
      simpa [effect,responseTagMap,device,Std.TreeMap.getElem?_insert,equal] using prior
  have htail (input : Roaming.ResponseInput) :
      Ensures (Roaming.responseConsumeTail msg input) (ResponseTagHeld entry input.pid) R := by
    let P := ResponseTagHeld entry input.pid
    have hephemeral (copy : Bool) (e ck hash : List UInt8) :
        Ensures (messageEphemeral copy e ck hash) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (messageEphemeral_wg_spec P copy e ck hash)
    have hdh (key : Bool) (ck priv pub : List UInt8) :
        Ensures (mixDh key ck priv pub) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (mixDh_wg_spec P key ck priv pub)
    have hkdf (second third : Bool) (ck data : List UInt8) :
        Ensures (kdf second third ck data) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (kdf_wg_spec P second third ck data)
    have hout (outs : List (List UInt8)) (i : Nat) :
        Ensures (kdfOut outs i) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs i)
    have hdecrypt (sealed key hash : List UInt8) :
        Ensures (messageDecrypt sealed key hash) P (fun _ => P) :=
      (ensures_iff _ _ _).mpr (messageDecrypt_wg_spec P sealed key hash)
    unfold Roaming.responseConsumeTail
    refine ensures_bind _ _ (hephemeral true _ _ _) ?_
    rintro ⟨ck,hash⟩
    refine ensures_bind _ _ (hdh false _ _ _) ?_
    intro ee
    refine ensures_bind _ _ (hbranch P _ _) ?_
    intro failed
    cases failed with
    | true => exact hfail input.pid
    | false =>
      cases ee with
      | none => exact hstop P _ R
      | some pair =>
        obtain ⟨ck,unused⟩ := pair
        refine ensures_bind _ _ (hdh false _ _ _) ?_
        intro se
        refine ensures_bind _ _ (hbranch P _ _) ?_
        intro failed
        cases failed with
        | true => exact hfail input.pid
        | false =>
          cases se with
          | none => exact hstop P _ R
          | some pair =>
            obtain ⟨ck,unused⟩ := pair
            refine ensures_bind _ _ (hkdf true true _ _) ?_
            intro outs
            refine ensures_bind _ _ (hout outs 0) ?_
            intro ck
            refine ensures_bind _ _ (hout outs 1) ?_
            intro tempHash
            refine ensures_bind _ _ (hout outs 2) ?_
            intro key
            refine ensures_bind _ _ (hdecrypt _ _ _) ?_
            intro decrypted
            refine ensures_bind _ _ (hbranch P _ _) ?_
            intro failed
            cases failed with
            | true => exact hfail input.pid
            | false =>
              cases decrypted with
              | none => exact hstop P _ R
              | some pair =>
                obtain ⟨unused,hash⟩ := pair
                refine ensures_bind _ _ (hread P input.pid) ?_
                intro checked
                refine ensures_bind _ _ (hbranch P _ _) ?_
                intro changed
                cases changed with
                | true => exact hfail input.pid
                | false =>
                  rw [← bind_assoc]
                  refine ensures_bind _ _
                    (hcommit input.pid
                      (fun p => {p with remoteEphemeral := (msg.drop 12).take 32, hash := hash, chainingKey := ck, remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE})
                      (fun _ => rfl)) ?_
                  intro _
                  refine ensures_bind _ _ (hsnapshot (effect (some input.pid))) ?_
                  intro observed g a r final after pre run
                  cases run
                  exact pre
  have hchecked (identity : StaticIdentity) (owner pid : PeerId) :
      Ensures (do
        let p ← getPeer pid
        if ← branch .crespNotCreatedInitiation (p.handshakeState != HANDSHAKE_CREATED_INITIATION) then
          peerPut (some pid)
          return none
        Roaming.responseConsumeTail msg ⟨identity,owner,pid,p⟩)
        (ResponseTagHeld entry pid) R := by
    refine ensures_bind _ _ (hread _ pid) ?_
    intro p
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro wrong
    cases wrong with
    | true => exact hfail pid
    | false => exact htail ⟨identity,owner,pid,p⟩
  have hlookup : Ensures (indexLookup [.handshake] (u32le msg 8)) safe
      (fun result g => safe g ∧ ∀owner pid, result = some (owner,pid) →
        ∃d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount) :=
    indexLookup_spec_responseTagMap_variant [.handshake] (u32le msg 8) entry
  have hconsume : Ensures (Roaming.responseConsume msg) safe R := by
    unfold Roaming.responseConsume
    refine ensures_bind _ _ hdev ?_
    intro d
    refine ensures_bind _ _ (hbranch safe _ _) ?_
    intro absent
    cases absent with
    | true => exact hnone
    | false =>
      refine ensures_bind _ _ hlookup ?_
      intro entry
      refine ensures_bind _ _ (hbranch _ _ _) ?_
      intro missing
      cases missing with
      | true =>
        intro g a r final after pre run
        exact hnone g a r final after pre.1 run
      | false =>
        cases entry with
        | none => exact hstop _ _ R
        | some pair =>
          obtain ⟨owner,pid⟩ := pair
          cases owner with
          | keypair id => exact hstop _ _ R
          | handshake own =>
            intro g a r final after pre run
            exact hchecked d.staticIdentity own pid g a r final after
              ⟨pre.1,pre.2 (.handshake own) pid rfl⟩ run
  rw [← Roaming.responseConsume_erase]
  refine ensures_bind _ _ hconsume ?_
  intro out g ambient result final after pre run
  cases run
  exact pre




end Leanux.Proofs.WG.Noise
