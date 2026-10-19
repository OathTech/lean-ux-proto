import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionSelection
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialBoundsFrames

/-! Quiet native calls retain pending allocation identities. The ordinary
configured-peer and slot-bound components are reused by forgetting the
auxiliary resident-key inventory; no authorization history is imported. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins

theorem Carrier.bounds (confirmed : List Nat) {action : WG.M α}
    (bounds : Preserves ResidentMaterial.Bounds action)
    (pending : Preserves (Inv confirmed) action) : Preserves (Carrier confirmed) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  exact ⟨((hoare_iff_run_ambient _ _ _).mp bounds _ _ _ _ _ ⟨hi.1,hi.2.1⟩ run).1,
    ((hoare_iff_run_ambient _ _ _).mp bounds _ _ _ _ _ ⟨hi.1,hi.2.1⟩ run).2,
    (hoare_iff_run_ambient _ _ _).mp pending _ _ _ _ _ hi.2.2 run⟩

theorem Carrier.store (confirmed : List Nat) {action : WG.M α} (same : SameWGStore action) :
    Preserves (Carrier confirmed) action :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_store same)
    (frame_preserves (PendingPromotion.store same) confirmed)

theorem Carrier.peer_get (confirmed : List Nat) (pid : PeerId) :
    Preserves (Carrier confirmed) (peerGet pid) :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_peer_get pid)
    (frame_preserves (frame (CurrentSlots.peerGet_fields pid)
      (Keypairs.WGFrames.peerGet_sameSnapshot pid)) confirmed)

theorem Carrier.peer_put (confirmed : List Nat) (pid : Option PeerId) :
    Preserves (Carrier confirmed) (peerPut pid) :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_peer_put pid)
    (PendingPromotion.preserves (PendingPromotion.peer_put pid) confirmed)

theorem Carrier.key_put (confirmed : List Nat) (kid : Option KeypairId) (now : Bool) :
    Preserves (Carrier confirmed) (keypairPut kid now) :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_key_put kid now)
    (PendingPromotion.preserves (PendingPromotion.key_put kid now) confirmed)

theorem key_write (w : WGWorld) (d : Device) (kid : KeypairId) (old key : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[kid]? = some old)
    (same : key.internalId = old.internalId) :
    view {w with dev := some {d with keypairs := d.keypairs.insert kid key}} = view w := by
  have keys : keypairResidents {w with dev := some {d with keypairs := d.keypairs.insert kid key}} =
      keypairResidents w := by
    funext q
    by_cases equal : kid = q
    · subst q; simp [keypairResidents,device,resident,same]
    · simp [keypairResidents,device,Std.TreeMap.getElem?_insert,equal]
  apply Store.ext
  · rfl
  · funext pid
    simp only [view,keys,nextSlot,device,Option.bind_some]

theorem modify_key (kid : KeypairId) (f : Keypair → Keypair)
    (same : ∀ key, (f key).internalId = key.internalId) :
    SameView view (do let key ← getKeypair kid; setKeypair kid (f key)) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨key,u,c,read,write⟩ := run
  obtain ⟨sameWorld,sameAmbient,d,device,resident⟩ :=
    KeyTimes.getKeypair_return kid w u key a c read
  subst u c
  cases result
  have actual : v = {w with dev := some {d with keypairs := d.keypairs.insert kid (f key)}} ∧ b = a := by
    simpa [setKeypair,modifyDev,device] using write.symm
  rw [actual.1]
  exact key_write w d kid key (f key) device resident (same key)

theorem Carrier.reserve (confirmed : List Nat) (kid : KeypairId) :
    Preserves (Carrier confirmed) (TransmitSecurity.Nonce.reserveNative kid) := by
  apply Carrier.bounds confirmed
    (ResidentMaterial.bounds_forget (Responder.DriverCuts.carrier_reserve kid))
  have same := modify_key kid (fun key => {key with sendingCounter := key.sendingCounter + 1})
    (fun _ => rfl)
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  unfold TransmitSecurity.Nonce.reserveNative at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨key,u,c,read,rest⟩ := run
  rw [MaterialOrigin.bind_ok_ambient] at rest
  obtain ⟨ignored,v',b',write,finish⟩ := rest
  simp only [StateT.run_pure] at finish
  obtain ⟨⟨_,rfl⟩,rfl⟩ := finish
  have whole : (((do
      let key ← getKeypair kid
      setKeypair kid {key with sendingCounter := key.sendingCounter + 1}) : WG.M Unit).run w).run a =
      .ok ((ignored,v),b) := by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨key,u,c,read,write⟩
  exact (hoare_iff_run_ambient _ _ _).mp (frame_preserves same confirmed)
    _ _ _ _ _ hi whole

theorem skb (action : SkbM α) : SameView view (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d skbs hi device
  have same : view {w with dev := some {d with txSkbs := skbs.txSkbs,rxSkbs := skbs.rxSkbs,nextSkb := skbs.nextSkb}} = view w := by
    have keys : keypairResidents {w with dev := some {d with txSkbs := skbs.txSkbs,rxSkbs := skbs.rxSkbs,nextSkb := skbs.nextSkb}} = keypairResidents w := by
      funext kid
      simp only [keypairResidents,device,Option.bind_some]
    apply Store.ext
    · rfl
    · funext pid
      simp only [view,keys,nextSlot,device,Option.bind_some]
  exact same.trans hi

theorem Carrier.skb (confirmed : List Nat) (action : SkbM α) :
    Preserves (Carrier confirmed) (liftSkb action) :=
  Carrier.bounds confirmed (ResidentMaterial.bounds_skb action)
    (frame_preserves (PendingPromotion.skb action) confirmed)

theorem Carrier.allocate (confirmed : List Nat) (packets : List DataPacket) :
    Preserves (Carrier confirmed) (packets.mapM newTxSkb) := by
  induction packets with
  | nil => exact preserves_pure _
  | cons packet packets ih =>
    simp only [List.mapM_cons]
    exact preserves_bind (Carrier.skb confirmed (SkbStore.newTx packet)) (fun id =>
      preserves_bind ih (fun ids => preserves_pure (id :: ids)))

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
