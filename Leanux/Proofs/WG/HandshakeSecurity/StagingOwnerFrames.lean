import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialSelection

/-! Ownership at the native staging dereference. Current-slot compatibility
permits a cleared owner; only a successful native dereference supplies the
nonnull word. This evidence is historical and is not a retirement invariant. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder RxCredits

def OwnerSelected (pid : PeerId) (result : Option (Peer × Option KeypairId))
    (w : WGWorld) : Prop :=
  ∀ peer kid, result = some (peer,some kid) →
    Lower (kid + 1) w ∧ KeyCompatible pid kid w

def OwnerPick (pid : PeerId) (kid : KeypairId) (w : WGWorld) : Prop :=
  Pick kid w ∧ KeyCompatible pid kid w

theorem key_get_compatible (pid kid : Nat) (kp : Option KeypairId) :
    Preserves (KeyCompatible pid kid) (keypairGet kp) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b compatible run
  have same := (hoare_iff_run_ambient _ _ _).mp
    (Affiliation.keypairGet_affiliation kp (Affiliation.view w)) w a result v b rfl run
  rw [compatible_factor,same.1]
  exact compatible_factor.mp compatible

theorem selection_compatible (pid kid : Nat) :
    Preserves (KeyCompatible pid kid) (selectionPrefix pid) := by
  unfold selectionPrefix
  have read : Preserves (KeyCompatible pid kid) (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a peer v b before run
    obtain ⟨rfl,_,_,_,_⟩ := getPeer_normal pid w v peer a b run
    exact before
  apply preserves_bind read
  intro peer
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .stagedEmpty peer.staged.isEmpty) _)
  intro empty
  split
  · exact preserves_pure _
  · exact preserves_bind (setPeer_compatible pid kid pid _) (fun _ =>
      preserves_bind (key_get_compatible pid kid peer.keypairCurrent) (fun _ => preserves_pure _))

theorem selection_owner (pid : PeerId) :
    Hoare (selectionPrefix pid) CurrentSlots.Inv (OwnerSelected pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b slots run peer kid returned
  obtain ⟨device,hd,hp,hk⟩ := DriverCuts.selection_native pid
    ⟨result,w,v,a,b⟩ run peer kid returned
  change w.dev = some device at hd
  have compatible := (CurrentSlots.current slots).compatible pid device peer kid hd hp hk
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (selection_bound pid)
      w a result v b slots run peer kid returned,
    (hoare_iff_run_ambient _ _ _).mp (selection_compatible pid kid)
      w a result v b compatible run⟩

theorem owner_pick_read (pid kid : Nat) :
    Hoare (getKeypair kid) (fun w => Lower (kid + 1) w ∧ KeyCompatible pid kid w)
      (fun _ => OwnerPick pid kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a key v b before run
  have picked := (hoare_iff_run_ambient _ _ _).mp (key_pick kid) w a key v b before.1 run
  obtain ⟨rfl,_,_,_,_⟩ := KeyTimes.getKeypair_return kid w v key a b run
  exact ⟨picked,before.2⟩

theorem reserve_compatible (pid kid : Nat) :
    Preserves (KeyCompatible pid kid) (Nonce.reserveNative kid) := by
  change Hoare (Nonce.reserveNative kid) (KeyCompatible pid kid) (fun _ => KeyCompatible pid kid)
  simp only [Hoare,compatible_factor]
  unfold Nonce.reserveNative
  apply hoare_bind _ _ (Affiliation.getKeypair_spec (compatibleState pid kid) kid)
  intro key
  apply hoare_bind _ _
    (hoare_consequence
      (Affiliation.setKeypair_spec (compatibleState pid kid) kid
        {key with sendingCounter := key.sendingCounter + 1})
      (fun _ before => ⟨before.1,by simpa only [Affiliation.keyCell] using before.2⟩)
      (fun _ _ before => before))
  intro _
  exact preserves_pure _

theorem owner_pick_reservation (pid kid : Nat) :
    Preserves (OwnerPick pid kid) (Nonce.reserveNative kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (pick_reservation kid) w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp (reserve_compatible pid kid) w a result v b before.2 run⟩

/-- Successful native dereference resolves the selected peer and exposes a
nonnull owner word. A cleared owner cannot pass this source cut. -/
theorem dereference_owner (pid kid : Nat) :
    Hoare (IndexOwner.peerDeref (.keypair kid)) (KeyCompatible pid kid)
      (fun owner w => owner = pid ∧ keyWords w kid = some (some pid)) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a owner v b compatible run
  have same := compatible_peerDeref compatible a b run
  subst owner
  refine ⟨rfl,?_⟩
  cases hd : w.dev with
  | none =>
    simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases hk : d.keypairs[kid]? with
    | none =>
      simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,hd,hk,invariant,AmbientM.invariant] at run
      cases run
    | some key =>
      cases word : key.peer with
      | none =>
        simp [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,hd,hk,word,unsupported,AmbientM.unsupported] at run
        cases run
      | some actual =>
        have eq : actual = pid ∧ w = v ∧ a = b := by
          simpa [IndexOwner.peerDeref,IndexOwner.peerWord,getKeypair,getDev,hd,hk,word,and_assoc] using run
        rw [←eq.2.1]
        simp only [keyWords,hd,Option.bind_some,hk,Option.map_some,word,eq.1]

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
