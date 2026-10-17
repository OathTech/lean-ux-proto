import Leanux.Proofs.WG.Noise.PeerFrames

set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Std.Do

theorem expireCurrentPeerKeypairs_slots (pid : PeerId) (p : Peer) :
    Ensures (expireCurrentPeerKeypairs pid)
      (fun w => peerAt w pid = some p)
      (fun _ w => ∃ p', peerAt w pid = some p' ∧
        slots p' = slots p ∧ p'.handshakeState = 0) := by
  let Q : WGWorld → Prop := fun g => ∃ q, peerAt g pid = some q ∧
    slots q = slots p ∧ q.handshakeState = 0
  have hpure : Ensures (pure () : WG.M Unit) Q (fun _ => Q) := by
    intro g ambient result g' ambient' hp hr
    cases hr
    exact hp
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) Q (fun _ => Q) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) Q)
  have hstop : Ensures (invariant "unreachable" : WG.M Unit) Q (fun _ => Q) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.invariant "unreachable") Q)
  have hget : Ensures (getPeer pid) Q (fun _ => Q) := by
    intro g ambient q g' ambient' hp hr
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid Q) g ambient q g' ambient' hp hr).1
  have hmodify (f : Peer → Peer)
      (hf : ∀ q, slots (f q) = slots q ∧ (f q).handshakeState = q.handshakeState) :
      Ensures (modifyPeer pid f) Q (fun _ => Q) := by
    intro g ambient result g' ambient' hp hr
    obtain ⟨q, present, shape, tag⟩ := hp
    exact ⟨f q, (ensures_iff _ _ _).mpr (modifyPeer_exact_spec pid f q)
      g ambient result g' ambient' present hr, (hf q).1.trans shape, (hf q).2.trans tag⟩
  have hclear : Ensures (handshakeClear pid) (fun g => peerAt g pid = some p)
      (fun _ => Q) := by
    let P : WGWorld → Prop := fun g => peerAt g pid = some p
    unfold handshakeClear
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · unfold IndexOwner.peerDeref IndexOwner.peerWord
      refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
      · refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
        · intro g ambient q g' ambient' hp hr
          exact ((ensures_iff _ _ _).mpr (getPeer_exact_spec pid p)
            g ambient q g' ambient' hp hr).2
        · intro q g ambient word g' ambient' hp hr
          cases hr
          exact hp
      · intro word
        cases word with
        | none =>
          exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
            (AmbientM.unsupported "entry->peer is NULL: the C dereferences it") P)
        | some owner =>
          intro g ambient result g' ambient' hp hr
          cases hr
          exact hp
    · intro _
      refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
      · refine (ensures_iff _ _ _).mpr (hoare_liftIndex_variant _ P ?_)
        intro g d table hp hd
        simpa [P, peerAt, hd] using hp
      · intro _
        intro g ambient result g' ambient' hp hr
        exact ⟨_, handshakeZero_peer pid p g ambient result g' ambient' hp hr, rfl, rfl⟩
  have hreset : Ensures (resetLastSentHandshake pid) Q (fun _ => Q) := by
    unfold resetLastSentHandshake
    refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
    · exact (ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .resetLastSent) Q)
    · intro now
      exact hmodify _ (fun _ => ⟨rfl, rfl⟩)
  have hinvalidate (kp : KeypairId) : Ensures (do
      let key ← getKeypair kp
      setKeypair kp {key with sending := {key.sending with isValid := false}})
      Q (fun _ => Q) := by
    refine ensures_bind (Q := fun _ => Q) _ _ ?_ ?_
    · intro g ambient key g' ambient' hp hr
      cases hd : g.dev with
      | none =>
        simp [getKeypair, getDev, hd, invariant, AmbientM.invariant] at hr
        cases hr
      | some d =>
        cases hk : d.keypairs[kp]? with
        | none =>
          simp [getKeypair, getDev, hd, hk, invariant, AmbientM.invariant] at hr
          cases hr
        | some key =>
          simp [getKeypair, getDev, hd, hk] at hr
          rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
          exact hp
    · intro key
      exact (ensures_iff _ _ _).mpr
        (modifyDev_peers_spec
          (fun ps => ∃ q, ps pid = some q ∧ slots q = slots p ∧ q.handshakeState = 0)
          _ (fun _ => rfl))
  unfold expireCurrentPeerKeypairs
  simp only [requireNotPending, pure_bind]
  refine ensures_bind _ _ hclear ?_
  intro _
  refine ensures_bind (Q := fun _ => Q) _ _ hreset ?_
  intro _
  refine ensures_bind (Q := fun _ => Q) _ _ hget ?_
  intro peer
  have tail : Ensures (do
      if ← branch .expireCurrentKeypair peer.keypairCurrent.isSome then
        let some kp := peer.keypairCurrent | invariant "unreachable"
        let key ← getKeypair kp
        setKeypair kp {key with sending := {key.sending with isValid := false}})
      Q (fun _ => Q) := by
    refine ensures_bind (Q := fun _ => Q) _ _ (hbranch _ _) ?_
    intro doCurrent
    cases doCurrent with
    | false => exact hpure
    | true =>
      cases peer.keypairCurrent with
      | none => exact hstop
      | some kp => exact hinvalidate kp
  refine ensures_bind (Q := fun _ => Q) _ _ (hbranch _ _) ?_
  intro doNext
  cases doNext with
  | false => exact tail
  | true =>
    cases peer.keypairNext with
    | none =>
      refine ensures_bind (Q := fun _ => Q) _ _ hstop ?_
      intro _
      exact tail
    | some kp =>
      refine ensures_bind (Q := fun _ => Q) _ _ (hinvalidate kp) ?_
      intro _
      exact tail

end Leanux.Proofs.WG.Noise
