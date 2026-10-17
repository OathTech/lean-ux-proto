import Leanux.Proofs.WG.Index.IndexOperationFrames
import Leanux.Proofs.WG.Index.Release
import Leanux.Proofs.WG.Index.ReleaseEffects
import Leanux.Proofs.WG.Noise.SessionSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem keypairPut_indices_spec (id : Option KeypairId) (now : Bool) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ keypairPut id now ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, unique⟩ := pre
  cases id with
  | none =>
    simp [keypairPut, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨d, device, unique⟩
  | some id =>
    cases resident : d.keypairs[id]? with
    | none =>
      simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev, device,
        resident, invariant, AmbientM.invariant] at run
      cases run
    | some k =>
      have removeForm : indexRemove (.keypair id) = (do
        _ ← branch .idxRemoveHashed ((← get).any (·.owner == .keypair id))
        modify fun table => table.filter fun e => !(e.owner == .keypair id) : IndexM Unit) := rfl
      have lifted : (monadLift (indexRemove (.keypair id)) : WG.M Unit) =
          liftIndex (indexRemove (.keypair id)) := rfl
      by_cases live : 0 < k.refcount
      · by_cases word : k.peer ≠ none
        · obtain ⟨value, next, nextAmbient, exactRun, finalDevice⟩ :=
            keypairPut_exact id now d k resident live word g ambient device
          rw [run] at exactRun
          cases exactRun
          exact ⟨_, finalDevice, released_indices d id k now unique⟩
        · have peer : k.peer = none := by simpa using word
          cases now with
          | true =>
            simp [keypairPut, branch, AmbientM.branch, getKeypair, getDev, device,
              resident, IndexOwner.peerDeref, IndexOwner.peerWord, peer,
              unsupported, AmbientM.unsupported] at run
            cases run
          | false =>
            cases count : k.refcount with
            | zero => omega
            | succ n =>
              cases n with
              | zero =>
                simp only [keypairPut, lifted] at run
                simp [branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, getKeypair,
                  getDev, device, resident, IndexOwner.peerDeref, IndexOwner.peerWord,
                  peer, setKeypair, modifyDev, refcountDecAndTest, count,
                  unsupported, AmbientM.unsupported] at run
                cases run
              | succ n =>
                simp [keypairPut, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
                  getKeypair, getDev, device, resident, setKeypair, modifyDev,
                  refcountDecAndTest, count] at run
                rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
                exact ⟨_, rfl, unique⟩
      · have zero : k.refcount = 0 := by omega
        simp only [keypairPut, lifted] at run
        cases now <;> cases peer : k.peer
        all_goals
          simp [branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
            getKeypair, getDev, device, resident, IndexOwner.peerDeref,
            IndexOwner.peerWord, peer, setKeypair, modifyDev, refcountDecAndTest,
            zero, removeForm, liftIndex, invariant, AmbientM.invariant,
            unsupported, AmbientM.unsupported] at run
        all_goals cases run

theorem addNewKeypair_indices_spec (pid : PeerId) (kp : KeypairId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ addNewKeypair pid kp ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let Q : WGWorld → Prop := IndicesSafe
  have hrotation (actions : List RotationAction) : Ensures (rotationExecute pid actions) Q (fun _ => Q) := by
    induction actions with
    | nil =>
      intro g ambient result final after pre run
      cases run
      exact pre
    | cons action rest ih =>
      cases action with
      | write change =>
        change Ensures ((getPeer pid >>= fun p => setPeer pid (change.apply p)) >>=
          fun _ => rotationExecute pid rest) _ _
        refine ensures_bind (Q := fun _ => Q) _ _ ?_ (fun _ => ih)
        refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid Q)) ?_
        intro p g ambient result final after pre run
        exact (ensures_iff _ _ _).mpr (setPeer_indices_spec pid (change.apply p))
          g ambient result final after pre.1 run
      | put key =>
        exact ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairPut_indices_spec key true))
          (fun _ => ih)
  have hread : Ensures (getKeypair kp) Q (fun _ => Q) := by
    intro g ambient k final after pre run
    cases device : g.dev with
    | none =>
      simp [getKeypair, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases key : d.keypairs[kp]? with
      | none =>
        simp [getKeypair, getDev, device, key, invariant, AmbientM.invariant] at run
        cases run
      | some k =>
        simp [getKeypair, getDev, device, key] at run
        rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
        exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) Q (fun _ => Q) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) Q)
  rw [addNewKeypair_rotation_source]
  unfold rotationSource
  refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
  · intro g ambient p final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid Q)
      g ambient p final after pre run).1
  · intro p
    refine ensures_bind _ _ hread ?_
    intro k
    refine ensures_bind _ _ (hbranch _ _) ?_
    intro initiator
    cases initiator with
    | false => exact hrotation _
    | true =>
      refine ensures_bind _ _ (hbranch _ _) ?_
      intro hasNext
      cases hasNext <;> exact hrotation _



theorem beginSession_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ beginSession pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  obtain ⟨d, device, unique⟩ := pre
  cases resident : d.peers[pid]? with
  | none =>
    simp [beginSession, getPeer, getDev, device, resident, invariant, AmbientM.invariant] at run
    cases run
  | some p =>
    obtain ⟨out, device', effect⟩ :=
      beginSession_effect pid d p g.keypairCounter resident g ambient result final after
        ⟨device, rfl⟩ run
    refine ⟨out, device', ?_⟩
    cases result with
    | false =>
      obtain ⟨rfl, _⟩ := effect
      exact unique
    | true =>
      obtain ⟨_, _, _, _, birth, rotated, steps, _, rfl⟩ := effect
      have rotation {start finish : Device} {actions : List RotationAction}
          (steps : RotationRun pid start actions finish) :
          UniqueIndices start.indexTable → UniqueIndices finish.indexTable := by
        induction steps with
        | nil => exact id
        | write d final change p rest resident tail ih => exact ih
        | put d middle final key rest release tail ih =>
          intro h
          apply ih
          cases release with
          | null => exact h
          | present d id k resident live word => exact released_indices d id k true h
      apply replace_indices
      exact rotation steps unique



theorem createInitiation_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ createInitiation pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let P : WGWorld → Prop := IndicesSafe
  let R : Option (List UInt8) → WGWorld → Prop := fun _ => P
  change Ensures _ P R
  have hpure : Ensures (pure none : WG.M (Option (List UInt8))) P R := by
    intro g ambient x g' ambient' hp hr
    cases hr
    exact hp
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
  have hwrite (f : Peer → Peer) :
      Ensures (do setPeer pid (f (← getPeer pid))) P (fun _ => P) := by
    refine ensures_bind _ _ hread ?_
    intro p
    exact (ensures_iff _ _ _).mpr (setPeer_indices_spec pid (f p))
  have hchain (ck hash : List UInt8) :
      Ensures ((noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash)
        P (fun _ => P) :=
    hwrite (fun p => {p with chainingKey := ck, hash})
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
  have hindex : Ensures (liftIndex (indexInsert (.handshake pid))) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (indexInsert_indices_spec (.handshake pid))
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
    refine ensures_bind _ _ (hwrite (fun p => {p with ephemeralPrivate := clamp secret})) ?_
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
                refine ensures_bind _ _ (hwrite
                  (fun p => {p with handshakeState := HANDSHAKE_CREATED_INITIATION})) ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact hp

theorem createResponse_indices_spec (pid : PeerId) :
    ⦃fun w => ⌜IndicesSafe w⌝⦄ createResponse pid ⦃⇓? _ w => ⌜IndicesSafe w⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  let P : WGWorld → Prop := IndicesSafe
  let R : Option (List UInt8) → WGWorld → Prop := fun _ => P
  change Ensures _ P R
  have hpure : Ensures (pure none : WG.M (Option (List UInt8))) P R := by
    intro g ambient x g' ambient' hp hr
    cases hr
    exact hp
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
  have hwrite (f : Peer → Peer) :
      Ensures (do setPeer pid (f (← getPeer pid))) P (fun _ => P) := by
    refine ensures_bind _ _ hread ?_
    intro p
    exact (ensures_iff _ _ _).mpr (setPeer_indices_spec pid (f p))
  have hchain (ck hash : List UInt8) :
      Ensures ((noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash)
        P (fun _ => P) :=
    hwrite (fun p => {p with chainingKey := ck, hash})
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
  have hindex : Ensures (liftIndex (indexInsert (.handshake pid))) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (indexInsert_indices_spec (.handshake pid))
  unfold createResponse
  refine ensures_bind _ _ hread ?_
  intro p
  refine ensures_bind _ _ (hbranch _ _) ?_
  intro notConsumed
  cases notConsumed with
  | true => exact hpure
  | false =>
    refine ensures_bind _ _ (hhidden _) ?_
    intro secret
    rw [← bind_assoc]
    refine ensures_bind _ _ (hwrite (fun p => {p with ephemeralPrivate := clamp secret})) ?_
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
                refine ensures_bind _ _ (hwrite
                  (fun p => {p with handshakeState := HANDSHAKE_CREATED_RESPONSE})) ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact hp

end Leanux.Proofs.WG.Index
