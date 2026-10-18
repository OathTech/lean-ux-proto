import Leanux.Proofs.WG.Index.CreatorCompatibleEffects
import Leanux.Proofs.WG.Index.OwnerCoherenceCreatorFrames
import Leanux.Proofs.WG.Noise.CryptoFrames
import Leanux.Proofs.WG.Keypairs.MaterialOrigin
import Leanux.Proofs.Framing.WP

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- The consecutive original dereference and insertion, with the same Ambient
and state flow. NULL refusal remains inside this actual publication cut. -/
def creatorPublish (pid : PeerId) : WG.M Nat := do
  let _ ← IndexOwner.peerDeref (.handshake pid)
  liftIndex (indexInsert (.handshake pid))

/-- One preservation traversal of the original creator. The four supplied
contracts concern its actual writes/publication, never substituted callbacks. -/
theorem createInitiation_preserves_source (pid : PeerId) (P : WGWorld → Prop)
    (hchain : ∀ ck hash : List UInt8,
      Ensures (modifyPeer pid fun p => {p with chainingKey := ck, hash}) P (fun _ => P))
    (hsecret : ∀ secret : List UInt8,
      Ensures (modifyPeer pid fun p => {p with ephemeralPrivate := clamp secret}) P (fun _ => P))
    (htag : Ensures (modifyPeer pid fun p =>
      {p with handshakeState := HANDSHAKE_CREATED_INITIATION}) P (fun _ => P))
    (hpublish : Ensures (creatorPublish pid) P (fun _ => P)) :
    Ensures (createInitiation pid) P (fun _ => P) := by
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
    refine ensures_bind _ _ (hsecret secret) ?_
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
                rw [← bind_assoc]
                refine ensures_bind _ _ hpublish ?_
                intro index
                rw [← bind_assoc]
                refine ensures_bind _ _ htag ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact hp

/-- Generic actual read/write transport used by each concrete creator write. -/
theorem modifyPeer_device_predicate (pid : PeerId) (D : Device → Prop) (f : Peer → Peer)
    (stable : ∀ d p, d.peers[pid]? = some p → D d →
      D {d with peers := d.peers.insert pid (f p)}) :
    Ensures (modifyPeer pid f) (fun g => ∀ d, g.dev = some d → D d)
      (fun _ g => ∀ d, g.dev = some d → D d) := by
  intro g ambient result out after pre run
  change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
  cases device : g.dev with
  | none =>
    simp [getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      simp [getPeer,getDev,device,resident,setPeer,modifyDev] at run
      rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      intro actual present
      cases present
      exact stable d p resident (pre d device)

/-- Successful dereference supplies the non-NULL word at the same publication
cut; local self compatibility then identifies the owner that is inserted. -/
theorem creatorPublish_handshakeCompatible (pid : PeerId) :
    Ensures (creatorPublish pid)
      (fun g => ∀ d, g.dev = some d → HandshakeCompatible pid d)
      (fun _ g => ∀ d, g.dev = some d → HandshakeCompatible pid d) := by
  intro g ambient index out after pre run
  unfold creatorPublish at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨target,middle,inputs,deref,insert⟩ := run
  cases device : g.dev with
  | none =>
    simp [IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at deref
    cases deref
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at deref
      cases deref
    | some p =>
      have compatible := pre d device
      have caller := compatible.2 p resident
      cases word : p.handshakeEntryPeer with
      | none =>
        simp [IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
          device,resident,word,unsupported,AmbientM.unsupported] at deref
        cases deref
      | some owner =>
        have self : owner = pid := by
          rcases caller.1 with absent | same
          · simp [word] at absent
          · simpa [word] using same
        subst owner
        simp [IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
          device,resident,word] at deref
        rcases deref with ⟨⟨rfl,rfl⟩,rfl⟩
        have publisher : OwnerCoherent d (.handshake pid) :=
          ⟨pid,p,by simp [ownerWord,resident,word],resident,caller.2,rfl⟩
        obtain ⟨present,safe⟩ := indexInsert_owner_coherence (.handshake pid) d
          compatible.1 publisher g ambient index out after device insert
        intro actual found
        change out.dev = _ at present
        rw [present] at found
        cases found
        exact ⟨safe,compatible.2⟩

/-- One preservation traversal of the actual response creator. Its contracts
are over the original chain, secret, tag and publication operations; early
refusals and later Stops are not assumed away. -/
theorem createResponse_preserves_source (pid : PeerId) (P : WGWorld → Prop)
    (hchain : ∀ ck hash : List UInt8,
      Ensures (modifyPeer pid fun p => {p with chainingKey := ck, hash}) P (fun _ => P))
    (hsecret : ∀ secret : List UInt8,
      Ensures (modifyPeer pid fun p => {p with ephemeralPrivate := clamp secret}) P (fun _ => P))
    (htag : Ensures (modifyPeer pid fun p =>
      {p with handshakeState := HANDSHAKE_CREATED_RESPONSE}) P (fun _ => P))
    (hpublish : Ensures (creatorPublish pid) P (fun _ => P)) :
    Ensures (createResponse pid) P (fun _ => P) := by
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
    refine ensures_bind _ _ (hsecret secret) ?_
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
                rw [← bind_assoc]
                refine ensures_bind _ _ hpublish ?_
                intro index
                rw [← bind_assoc]
                refine ensures_bind _ _ htag ?_
                intro _ g ambient x g' ambient' hp hr
                cases hr
                exact hp

end Leanux.Proofs.WG.Index
