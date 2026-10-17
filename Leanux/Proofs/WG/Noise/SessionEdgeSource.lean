import Leanux.Proofs.WG.Noise.PeerFrames
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do
theorem beginSession_tag (pid : PeerId) (old : Nat) :
    Ensures (beginSession pid) (fun g => tagAt g pid = some old)
      (fun ok g => tagAt g pid = some (if ok then HANDSHAKE_ZEROED else old) ∧
        (ok = true → old = HANDSHAKE_CREATED_RESPONSE ∨ old = HANDSHAKE_CONSUMED_RESPONSE)) := by
  let Tag : Nat → WGWorld → Prop := fun tag g => tagAt g pid = some tag
  let P := Tag old
  let Z := Tag HANDSHAKE_ZEROED
  let R : Bool → WGWorld → Prop := fun ok g =>
    tagAt g pid = some (if ok then HANDSHAKE_ZEROED else old) ∧
      (ok = true → old = HANDSHAKE_CREATED_RESPONSE ∨ old = HANDSHAKE_CONSUMED_RESPONSE)
  change Ensures _ P R
  have hpure : Ensures (pure false : WG.M Bool) P R := by
    intro g ambient x g' ambient' hp hr
    cases hr
    exact ⟨hp, by simp⟩
  have hstop {α : Type} (what : String) (S : WGWorld → Prop) (Q : α → WGWorld → Prop) :
      Ensures (invariant what : WG.M α) S Q := by
    intro g ambient x g' ambient' hp hr
    simp [invariant, AmbientM.invariant] at hr
    cases hr
  have hread (tag : Nat) : Ensures (getPeer pid) (Tag tag) (fun _ => Tag tag) := by
    intro g ambient x g' ambient' hp hr
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (Tag tag))
      g ambient x g' ambient' hp hr).1
  have hbranch (tag : Nat) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) (Tag tag) (fun _ => Tag tag) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) (Tag tag))
  have hword (tag : Nat) :
      Ensures (IndexOwner.peerWord (.handshake pid)) (Tag tag) (fun _ => Tag tag) := by
    unfold IndexOwner.peerWord
    refine ensures_bind _ _ (hread tag) ?_
    intro p g ambient x g' ambient' hp hr
    cases hr
    exact hp
  have hderef (tag : Nat) :
      Ensures (IndexOwner.peerDeref (.handshake pid)) (Tag tag) (fun _ => Tag tag) := by
    unfold IndexOwner.peerDeref
    refine ensures_bind _ _ (hword tag) ?_
    intro word
    cases word with
    | none =>
      exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
        (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") (Tag tag))
    | some target =>
      intro g ambient x g' ambient' hp hr
      cases hr
      exact hp
  have hkeyread (kp : KeypairId) : Ensures (getKeypair kp) P (fun _ => P) := by
    intro g ambient k g' ambient' hp hr
    cases hd : g.dev with
    | none =>
      simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hk : d.keypairs[kp]? with
      | none =>
        simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
        cases hr
      | some k =>
        simp [getKeypair, getDev, hd, hk] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact hp
  have hkeyset (kp : KeypairId) (key : Keypair) :
      Ensures (setKeypair kp key) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (modifyDev_peers_spec
      (fun ps => (ps pid).map Peer.handshakeState = some old) _ (fun _ => rfl))
  have hzero : Ensures (handshakeZero pid) P (fun _ => Z) := by
    intro g ambient result g' ambient' hp hr
    cases found : peerAt g pid with
    | none => simp [P, Tag, tagAt, found] at hp
    | some p =>
      have after := handshakeZero_peer pid p g ambient result g' ambient' found hr
      simp [Z, Tag, tagAt, after, HANDSHAKE_ZEROED]
  have hindex (kp : KeypairId) :
      Ensures (liftIndex (indexReplaceHandshake pid kp)) Z (fun _ => Z) := by
    refine (ensures_iff _ _ _).mpr (hoare_liftIndex_variant _ Z ?_)
    intro g d table hp hd
    simpa [Z, Tag, tagAt, peerAt, hd] using hp
  have hreadFirst (f : Peer → WG.M Bool)
      (hf : ∀ p, p.handshakeState = old → Ensures (f p) P R) :
      Ensures (getPeer pid >>= f) P R := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient x g' ambient' hp hr
    have oldTag : p.handshakeState = old := by
      simpa [P, Tag, tagAt, hp.2] using hp.1
    exact hf p oldTag g ambient x g' ambient' hp.1 hr
  have hguard (st : Nat) (f : Bool → WG.M Bool)
      (hf : Ensures (f (st != HANDSHAKE_CREATED_RESPONSE && st != HANDSHAKE_CONSUMED_RESPONSE)) P R) :
      Ensures ((Leanux.WG.andM (branch .sessionNotCreatedResponse (st != HANDSHAKE_CREATED_RESPONSE))
        (branch .sessionNotConsumedResponse (st != HANDSHAKE_CONSUMED_RESPONSE))) >>= f) P R := by
    refine ensures_bind (Q := fun b g =>
      b = (st != HANDSHAKE_CREATED_RESPONSE && st != HANDSHAKE_CONSUMED_RESPONSE) ∧ P g) _ _ ?_ ?_
    · intro g ambient result g' ambient' hp hr
      by_cases a : st = HANDSHAKE_CREATED_RESPONSE <;>
        by_cases b : st = HANDSHAKE_CONSUMED_RESPONSE
      all_goals simp [Leanux.WG.andM, branch, AmbientM.branch, a, b] at hr
      all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals exact ⟨by simp [a, b], hp⟩
    · intro b g ambient x g' ambient' hp hr
      rcases hp with ⟨rfl, hp⟩
      exact hf g ambient x g' ambient' hp hr
  unfold beginSession
  refine hreadFirst _ ?_
  intro initial oldTag
  refine hguard _ _ ?_
  cases rejected : initial.handshakeState != HANDSHAKE_CREATED_RESPONSE &&
      initial.handshakeState != HANDSHAKE_CONSUMED_RESPONSE with
  | true => exact hpure
  | false =>
    have accepted : old = HANDSHAKE_CREATED_RESPONSE ∨ old = HANDSHAKE_CONSUMED_RESPONSE := by
      by_cases a : initial.handshakeState = HANDSHAKE_CREATED_RESPONSE
      · exact Or.inl (oldTag.symm.trans a)
      · have b : initial.handshakeState = HANDSHAKE_CONSUMED_RESPONSE := by
          simpa [a] using rejected
        exact Or.inr (oldTag.symm.trans b)
    refine ensures_bind _ _ (hword old) ?_
    intro word
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (keypairCreate_peers_spec
      (fun ps => (ps pid).map Peer.handshakeState = some old) word)) ?_
    intro created
    refine ensures_bind _ _ (hbranch old _ _) ?_
    intro noKeypair
    cases noKeypair with
    | true => exact hpure
    | false =>
      cases created with
      | none => exact hstop _ P R
      | some kp =>
        refine ensures_bind _ _ (hread old) ?_
        intro p
        refine ensures_bind _ _ (hkeyread kp) ?_
        intro key
        refine ensures_bind _ _ (hkeyset kp _) ?_
        intro _
        refine ensures_bind _ _ (hbranch old _ _) ?_
        intro initiator
        have tail : Ensures (do
            handshakeZero pid
            if ← branch .sessionAlive !(← getPeer pid).isDead then
              addNewKeypair pid kp
              _ ← IndexOwner.peerDeref (.handshake pid)
              if !(← indexReplaceHandshake pid kp) then
                unsupported "begin_session: the handshake entry was unhashed"
              return true
            unsupported "a dead peer finishing a session") P R := by
          refine ensures_bind _ _ hzero ?_
          intro _
          refine ensures_bind _ _ (hread HANDSHAKE_ZEROED) ?_
          intro zeroed
          refine ensures_bind _ _ (hbranch HANDSHAKE_ZEROED _ _) ?_
          intro alive
          cases alive with
          | false =>
            intro g ambient x g' ambient' hp hr
            simp [unsupported, AmbientM.unsupported] at hr
            cases hr
          | true =>
            refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
              (addNewKeypair_tag_spec pid kp HANDSHAKE_ZEROED)) ?_
            intro _
            refine ensures_bind _ _ (hderef HANDSHAKE_ZEROED) ?_
            intro _
            refine ensures_bind _ _ (hindex kp) ?_
            intro replaced
            cases replaced with
            | false =>
              intro g ambient x g' ambient' hp hr
              simp [unsupported, AmbientM.unsupported] at hr
              cases hr
            | true =>
              intro g ambient x g' ambient' hp hr
              cases hr
              exact ⟨hp, fun _ => accepted⟩
        cases initiator <;>
          exact ensures_bind _ _
            ((ensures_iff _ _ _).mpr (deriveKeys_peers_spec
              (fun ps => (ps pid).map Peer.handshakeState = some old) kp _ p.chainingKey))
            (fun _ => tail)
end Leanux.Proofs.WG.Noise
