import Leanux.Proofs.WG.Noise.CreationTagFrames
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.Config.BranchSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem createInitiation_tagMap (pid : PeerId) (entry : Option Device) :
    Ensures (createInitiation pid)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun result g => (∀target, responseTagMap g.dev target =
        if result.isSome then
          if pid = target then some HANDSHAKE_CREATED_INITIATION else responseTagMap entry target
        else responseTagMap entry target)) := by
  let P : WGWorld → Prop := fun g => responseTagMap g.dev = responseTagMap entry
  let R : Option (List UInt8) → WGWorld → Prop := fun result g =>
    (∀target, responseTagMap g.dev target =
      if result.isSome then
        if pid = target then some HANDSHAKE_CREATED_INITIATION else responseTagMap entry target
      else responseTagMap entry target)
  change Ensures _ P R
  have hpure : Ensures (pure none : WG.M (Option (List UInt8))) P R := by
    intro g ambient x g' ambient' hp hr
    cases hr
    intro target
    exact congrFun hp target
  have hstop {α : Type} (what : String) (Q : α → WGWorld → Prop) :
      Ensures (invariant what : WG.M α) P Q := by
    intro g ambient x g' ambient' hp hr
    simp [invariant, AmbientM.invariant] at hr
    cases hr
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient x g' ambient' hp hr
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P)
      g ambient x g' ambient' hp hr).1
  have hdev : Ensures getDev P (fun _ => P) := by
    intro g ambient x g' ambient' hp hr
    cases hd : g.dev with
    | none =>
      simp [getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      simp [getDev, hd] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact hp
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hhidden (site : HiddenSite) :
      Ensures (hidden site : WG.M (List UInt8)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden site) P)
  have hwrite (f : Peer → Peer)
      (same : ∀p, (f p).handshakeState = p.handshakeState) :
      Ensures (do setPeer pid (f (← getPeer pid))) P (fun _ => P) := by
    intro g ambient result final after pre run
    have effect := modifyPeer_spec_creationTagMap_variant entry pid f id
      (fun p => congrArg some (same p)) g ambient result final after pre run
    funext target
    simpa only [id_eq,ite_self] using effect target
  have hcommit (tag : Nat) :
      Ensures (modifyPeer pid (fun p => {p with handshakeState := tag})) P
        (fun _ g => ∀target, responseTagMap g.dev target =
          if pid = target then some tag else responseTagMap entry target) :=
    modifyPeer_spec_creationTagMap_variant entry pid _ (fun _ => some tag) (fun _ => rfl)
  have hchain (ck hash : List UInt8) :
      Ensures ((noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash)
        P (fun _ => P) :=
    hwrite (fun p => {p with chainingKey := ck, hash}) (fun _ => rfl)
  have hderef : Ensures (IndexOwner.peerDeref (.handshake pid)) P (fun _ => P) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · refine ensures_bind (Q := fun _ => P) _ _ hread ?_
      intro p g ambient x g' ambient' hp hr
      cases hr
      exact hp
    · intro word
      cases word with
      | none =>
        exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") P)
      | some target =>
        intro g ambient x g' ambient' hp hr
        cases hr
        exact hp
  have hindex : Ensures (liftIndex (indexInsert (.handshake pid))) P (fun _ => P) := by
    refine (ensures_iff _ _ _).mpr (hoare_liftIndex_variant _ P ?_)
    intro g d table hp hd
    funext target
    simpa [P, responseTagMap, hd] using congrFun hp target
  unfold createInitiation
  refine ensures_bind _ _ hdev ?_
  intro d
  refine ensures_bind _ _ (hbranch _ _) ?_
  intro noIdentity
  cases noIdentity with
  | true => exact hpure
  | false =>
    refine ensures_bind _ _ hread ?_
    intro p
    refine ensures_bind _ _ (hchain _ _) ?_
    intro _
    refine ensures_bind _ _ (hhidden _) ?_
    intro secret
    rw [← bind_assoc]
    refine ensures_bind _ _ (hwrite (fun p => {p with ephemeralPrivate := clamp secret})
      (fun _ => rfl)) ?_
    intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (generatePublic_wg_spec P _)) ?_
    intro generated
    rcases generated with ⟨pub, ok⟩
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro noEphemeral
    cases noEphemeral with
    | true => exact hpure
    | false =>
      cases pub with
      | none => exact hstop _ R
      | some e =>
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (messageEphemeral_wg_spec P _ _ _ _)) ?_
        intro ephemeral
        rcases ephemeral with ⟨ck, hash⟩
        refine ensures_bind _ _ (hchain _ _) ?_
        intro _
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixDh_wg_spec P _ _ _ _)) ?_
        intro es
        refine ensures_bind _ _ (hbranch _ _) ?_
        intro esFailed
        cases esFailed with
        | true => exact hpure
        | false =>
          cases es with
          | none => exact hstop _ R
          | some es =>
            rcases es with ⟨ck, key⟩
            refine ensures_bind _ _ (hchain _ _) ?_
            intro _
            refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixPrecomputedDh_wg_spec P _ _)) ?_
            intro ss
            refine ensures_bind _ _ (hbranch _ _) ?_
            intro ssFailed
            cases ssFailed with
            | true => exact hpure
            | false =>
              cases ss with
              | none => exact hstop _ R
              | some ss =>
                rcases ss with ⟨ck, key⟩
                refine ensures_bind _ _ (hhidden _) ?_
                intro now
                refine ensures_bind _ _ (hchain _ _) ?_
                intro _
                refine ensures_bind _ _ hderef ?_
                intro _
                refine ensures_bind _ _ hindex ?_
                intro index
                rw [← bind_assoc]
                refine ensures_bind _ _ (hcommit HANDSHAKE_CREATED_INITIATION) ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact hp

theorem createResponse_tagMap (pid : PeerId) (entry : Option Device) :
    Ensures (createResponse pid)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun result g => (∀target, responseTagMap g.dev target =
        if result.isSome then
          if pid = target then some HANDSHAKE_CREATED_RESPONSE else responseTagMap entry target
        else responseTagMap entry target) ∧
        (result.isSome → responseTagMap entry pid = some HANDSHAKE_CONSUMED_INITIATION)) := by
  let P : WGWorld → Prop := fun g => responseTagMap g.dev = responseTagMap entry
  let R : Option (List UInt8) → WGWorld → Prop := fun result g =>
    (∀target, responseTagMap g.dev target =
      if result.isSome then
        if pid = target then some HANDSHAKE_CREATED_RESPONSE else responseTagMap entry target
      else responseTagMap entry target) ∧
        (result.isSome → responseTagMap entry pid = some HANDSHAKE_CONSUMED_INITIATION)
  change Ensures _ P R
  have hpure : Ensures (pure none : WG.M (Option (List UInt8))) P R := by
    intro g ambient x g' ambient' hp hr
    cases hr
    exact ⟨fun target => congrFun hp target, by simp⟩
  have hstop {α : Type} (what : String) (Q : α → WGWorld → Prop) :
      Ensures (invariant what : WG.M α) P Q := by
    intro g ambient x g' ambient' hp hr
    simp [invariant, AmbientM.invariant] at hr
    cases hr
  have hread : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient x g' ambient' hp hr
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P)
      g ambient x g' ambient' hp hr).1
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hhidden (site : HiddenSite) :
      Ensures (hidden site : WG.M (List UInt8)) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden site) P)
  have hwrite (f : Peer → Peer)
      (same : ∀p, (f p).handshakeState = p.handshakeState) :
      Ensures (do setPeer pid (f (← getPeer pid))) P (fun _ => P) := by
    intro g ambient result final after pre run
    have effect := modifyPeer_spec_creationTagMap_variant entry pid f id
      (fun p => congrArg some (same p)) g ambient result final after pre run
    funext target
    simpa only [id_eq,ite_self] using effect target
  have hcommit (tag : Nat) :
      Ensures (modifyPeer pid (fun p => {p with handshakeState := tag})) P
        (fun _ g => ∀target, responseTagMap g.dev target =
          if pid = target then some tag else responseTagMap entry target) :=
    modifyPeer_spec_creationTagMap_variant entry pid _ (fun _ => some tag) (fun _ => rfl)
  have hchain (ck hash : List UInt8) :
      Ensures ((noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash)
        P (fun _ => P) :=
    hwrite (fun p => {p with chainingKey := ck, hash}) (fun _ => rfl)
  have hderef : Ensures (IndexOwner.peerDeref (.handshake pid)) P (fun _ => P) := by
    unfold IndexOwner.peerDeref IndexOwner.peerWord
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · refine ensures_bind (Q := fun _ => P) _ _ hread ?_
      intro p g ambient x g' ambient' hp hr
      cases hr
      exact hp
    · intro word
      cases word with
      | none =>
        exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
          (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") P)
      | some target =>
        intro g ambient x g' ambient' hp hr
        cases hr
        exact hp
  have hindex : Ensures (liftIndex (indexInsert (.handshake pid))) P (fun _ => P) := by
    refine (ensures_iff _ _ _).mpr (hoare_liftIndex_variant _ P ?_)
    intro g d table hp hd
    funext target
    simpa [P, responseTagMap, hd] using congrFun hp target

  have hreadFirst (f : Peer → WG.M (Option (List UInt8)))
      (hf : ∀ p, responseTagMap entry pid = some p.handshakeState → Ensures (f p) P R) :
      Ensures (getPeer pid >>= f) P R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient x g' ambient' hp hr
    have entryTag : responseTagMap entry pid = some p.handshakeState := by
      rw [← hp.1]
      change (peerAt g pid).map Peer.handshakeState = some p.handshakeState
      rw [hp.2]
      rfl
    exact hf p entryTag g ambient x g' ambient' hp.1 hr
  have hbranchFirst (site : Decision) (value : Bool)
      (f : Bool → WG.M (Option (List UInt8))) (hf : Ensures (f value) P R) :
      Ensures ((branch site value : WG.M Bool) >>= f) P R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
      (Leanux.Proofs.WG.Config.branch_state_spec P site value)) ?_
    intro b g ambient x g' ambient' hp hr
    rcases hp with ⟨rfl, hp⟩
    exact hf g ambient x g' ambient' hp hr
  unfold createResponse
  refine hreadFirst _ ?_
  intro p entryTag
  refine hbranchFirst _ _ _ ?_
  by_cases consumed : p.handshakeState = HANDSHAKE_CONSUMED_INITIATION
  · simp only [consumed, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine ensures_bind _ _ (hhidden _) ?_
    intro secret
    rw [← bind_assoc]
    refine ensures_bind _ _ (hwrite (fun p => {p with ephemeralPrivate := clamp secret})
      (fun _ => rfl)) ?_
    intro _
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (generatePublic_wg_spec P _)) ?_
    intro generated
    rcases generated with ⟨pub, ok⟩
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro noEphemeral
    cases noEphemeral with
    | true => exact hpure
    | false =>
      cases pub with
      | none => exact hstop _ R
      | some e =>
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (messageEphemeral_wg_spec P _ _ _ _)) ?_
        intro ephemeral
        rcases ephemeral with ⟨ck, hash⟩
        refine ensures_bind _ _ (hchain _ _) ?_
        intro _
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixDh_wg_spec P _ _ _ _)) ?_
        intro ee
        refine ensures_bind _ _ (hbranch _ _) ?_
        intro eeFailed
        cases eeFailed with
        | true => exact hpure
        | false =>
          cases ee with
          | none => exact hstop _ R
          | some ee =>
            rcases ee with ⟨ck, key⟩
            refine ensures_bind _ _ (hchain _ _) ?_
            intro _
            refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (mixDh_wg_spec P _ _ _ _)) ?_
            intro se
            refine ensures_bind _ _ (hbranch _ _) ?_
            intro seFailed
            cases seFailed with
            | true => exact hpure
            | false =>
              cases se with
              | none => exact hstop _ R
              | some se =>
                rcases se with ⟨ck, key⟩
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdf_wg_spec P _ _ _ _)) ?_
                intro outs
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 0)) ?_
                intro ck
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 1)) ?_
                intro tempHash
                refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (kdfOut_wg_spec P outs 2)) ?_
                intro key
                refine ensures_bind _ _ (hchain _ _) ?_
                intro _
                refine ensures_bind _ _ hderef ?_
                intro _
                refine ensures_bind _ _ hindex ?_
                intro index
                rw [← bind_assoc]
                refine ensures_bind _ _ (hcommit HANDSHAKE_CREATED_RESPONSE) ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact ⟨hp, fun _ => entryTag.trans (congrArg some consumed)⟩
  · simp only [bne, beq_eq_false_iff_ne.mpr consumed, Bool.not_false, ↓reduceIte]
    exact hpure

end Leanux.Proofs.WG.Noise
