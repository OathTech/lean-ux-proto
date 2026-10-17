import Leanux.Proofs.WG.Noise.PeerFrames
import Leanux.Proofs.WG.Config.BranchSource
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do
theorem createResponse_tag (pid : PeerId) (old : Nat) :
    Ensures (createResponse pid)
      (fun g => tagAt g pid = some old)
      (fun result g => tagAt g pid = some
        (if result.isSome then HANDSHAKE_CREATED_RESPONSE else old) ∧
        (result.isSome → old = HANDSHAKE_CONSUMED_INITIATION)) := by
  let P : WGWorld → Prop := fun g => tagAt g pid = some old
  let R : Option (List UInt8) → WGWorld → Prop := fun result g =>
    tagAt g pid = some (if result.isSome then HANDSHAKE_CREATED_RESPONSE else old) ∧
      (result.isSome → old = HANDSHAKE_CONSUMED_INITIATION)
  change Ensures _ P R
  have hpure : Ensures (pure none : WG.M (Option (List UInt8))) P R := by
    intro g ambient x g' ambient' hp hr
    cases hr
    exact ⟨hp, by simp⟩
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
  have hwrite (f : Peer → Peer) (tag : Nat)
      (same : ∀ p, p.handshakeState = old → (f p).handshakeState = tag) :
      Ensures (do setPeer pid (f (← getPeer pid))) P
        (fun _ g => tagAt g pid = some tag) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient result g' ambient' hp hr
    have oldTag : p.handshakeState = old := by
      simpa [P, tagAt, hp.2] using hp.1
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid (f p)})}), ambient) = _ at hr
    cases hr
    cases hd : g.dev with
    | none => simp [peerAt, hd] at hp
    | some d => simp [tagAt, peerAt, same p oldTag]
  have hchain (ck hash : List UInt8) :
      Ensures ((noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain) pid ck hash)
        P (fun _ => P) :=
    hwrite (fun p => {p with chainingKey := ck, hash}) old (fun _ h => h)
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
    simpa [P, tagAt, peerAt, hd] using hp

  have hreadFirst (f : Peer → WG.M (Option (List UInt8)))
      (hf : ∀ p, p.handshakeState = old → Ensures (f p) P R) :
      Ensures (getPeer pid >>= f) P R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient x g' ambient' hp hr
    have oldTag : p.handshakeState = old := by
      simpa [P, tagAt, hp.2] using hp.1
    exact hf p oldTag g ambient x g' ambient' hp.1 hr
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
  intro p oldTag
  refine hbranchFirst _ _ _ ?_
  by_cases consumed : p.handshakeState = HANDSHAKE_CONSUMED_INITIATION
  · simp only [consumed, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    refine ensures_bind _ _ (hhidden _) ?_
    intro secret
    rw [← bind_assoc]
    refine ensures_bind _ _ (hwrite (fun p => {p with ephemeralPrivate := clamp secret})
      old (fun _ h => h)) ?_
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
                  (fun p => {p with handshakeState := HANDSHAKE_CREATED_RESPONSE})
                  HANDSHAKE_CREATED_RESPONSE (fun _ _ => rfl)) ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact ⟨hp, fun _ => oldTag.symm.trans consumed⟩
  · simp only [bne, beq_eq_false_iff_ne.mpr consumed, Bool.not_false, ↓reduceIte]
    exact hpure
end Leanux.Proofs.WG.Noise
