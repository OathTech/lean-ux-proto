import Leanux.Proofs.WG.TimerDiscipline.View
import Leanux.Proofs.WG.TimerDiscipline.InitiationArmSource
import Leanux.Proofs.WG.Noise.StateEdges

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def initiationAt (w : WGWorld) (pid : PeerId) : Option InitiationView :=
  (peerAt w pid).map initiationView

theorem createInitiation_view (pid : PeerId) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ createInitiation pid
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  let P : WGWorld → Prop := fun g => initiationAt g pid = some v
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  have hpure : Ensures (pure none : WG.M (Option (List UInt8))) P (fun _ => P) := by
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
      (same : ∀ p, initiationView (f p) = initiationView p) :
      Ensures (do setPeer pid (f (← getPeer pid))) P (fun _ => P) := by
    refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
    intro p g ambient result g' ambient' hp hr
    have oldView : initiationView p = v := by
      simpa [P, initiationAt, hp.2] using hp.1
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid (f p)})}), ambient) = _ at hr
    cases hr
    cases hd : g.dev with
    | none => simp [peerAt, hd] at hp
    | some d => simp [P, initiationAt, peerAt, same, oldView]
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
    simpa [P, initiationAt, peerAt, hd] using hp
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
      | none => exact hstop _ (fun _ => P)
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
          | none => exact hstop _ (fun _ => P)
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
              | none => exact hstop _ (fun _ => P)
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
                  (fun p => {p with handshakeState := HANDSHAKE_CREATED_INITIATION})
                  (fun _ => rfl)) ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact hp

theorem addMacToPacket_view (pid : PeerId) (msg : List UInt8) (v : InitiationView) :
    ⦃fun w => ⌜initiationAt w pid = some v⌝⦄ addMacToPacket pid msg
      ⦃⇓? _ w => ⌜initiationAt w pid = some v⌝⦄ := by
  let P : WGWorld → Prop := fun g => initiationAt g pid = some v
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient y g' ambient' hp hr
    cases hr
    exact hp
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have hcmp (site : Decision) (value : Bool) (lhs rhs : Int) :
      Ensures (branchCmp site value lhs rhs : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branchCmp site value lhs rhs) P)
  have hclock : Ensures (hiddenClock64 .birthdateExpired : WG.M Int64) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .birthdateExpired) P)
  have hexpired (birthday : Int64) :
      Ensures (branchExpired .addMacCookieFresh birthday COOKIE_FRESH_SECONDS (!·)) P (fun _ => P) := by
    unfold branchExpired birthdateTest
    rw [bind_assoc]
    refine ensures_bind _ _ hclock ?_
    intro now
    simp only [pure_bind]
    exact hcmp _ _ _ _
  apply (ensures_iff _ _ _).mp
  change Ensures _ P (fun _ => P)
  unfold addMacToPacket
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (getPeer_spec pid P)) ?_
  intro p
  refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
  · intro g ambient result g' ambient' hp hr
    have oldView : initiationView p = v := by
      simpa [P, initiationAt, hp.2] using hp.1
    change Except.ok (((), {g with dev := g.dev.map (fun d : Device =>
      {d with peers := d.peers.insert pid {p with
        lastMac1Sent := blake2s 16 p.cookieMac1Key (msg.take (msg.length - 32)),
        haveSentMac1 := true}})}), ambient) = _ at hr
    cases hr
    cases hd : g.dev with
    | none => simp [peerAt, hd] at hp
    | some d => simpa [P, initiationAt, peerAt, initiationView] using oldView
  · intro _
    refine ensures_bind (Q := fun _ => P) _ _ ?_ ?_
    · unfold Leanux.WG.andM
      refine ensures_bind _ _ (hbranch _ _) ?_
      intro valid
      cases valid with
      | false => exact hpure false
      | true => exact hexpired _
    · intro valid
      cases valid <;> exact hpure _

end Leanux.Proofs.WG.TimerDiscipline
