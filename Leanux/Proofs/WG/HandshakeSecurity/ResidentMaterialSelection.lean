import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialJournal

/-! The staging bound is obtained at the actual current-slot read. It needs
only campaign 1's slot invariant; no responder-chronology premise is used. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

def Selected (result : Option (Peer × Option KeypairId)) (w : WGWorld) : Prop :=
  ∀ peer kid, result = some (peer,some kid) → Lower (kid + 1) w

def Pick (kid : KeypairId) (w : WGWorld) : Prop :=
  Lower (kid + 1) w ∧ ∃ core, pool w kid = some core

theorem lower_selection (pid : PeerId) : Preserves (Lower bound) (selectionPrefix pid) := by
  unfold selectionPrefix
  apply preserves_bind (lower_peer_read pid)
  intro peer
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .stagedEmpty peer.staged.isEmpty) _)
  intro empty
  split
  · exact preserves_pure _
  · exact preserves_bind (lower_metadata (setPeer_metadata _ _)) (fun _ =>
      preserves_bind (NativeFrames.lower_key_get peer.keypairCurrent) (fun _ => preserves_pure _))

theorem selection_bound (pid : PeerId) :
    Hoare (selectionPrefix pid) CurrentSlots.Inv Selected := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b slots run peer kid returned
  obtain ⟨device,hd,hp,hk⟩ := DriverCuts.selection_native pid
    ⟨result,w,v,a,b⟩ run peer kid returned
  change w.dev = some device at hd
  have bound := (CurrentSlots.current slots).below device pid peer kid hd hp hk
  have lower : Lower (kid + 1) w := by
    intro frontier found
    have same : frontier = device.nextKeypairId := by
      simpa only [cursor,hd,Option.map_some,Option.some.injEq] using found.symm
    rw [same]
    exact bound
  exact (hoare_iff_run_ambient _ _ _).mp (lower_selection pid) w a result v b lower run

theorem key_pick (kid : KeypairId) :
    Hoare (getKeypair kid) (Lower (kid + 1)) (fun _ => Pick kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a key v b lower run
  obtain ⟨rfl,rfl,d,device,resident⟩ := KeyTimes.getKeypair_return kid w v key a b run
  exact ⟨lower,keyCore key,by simp only [pool,device,Option.bind_some,resident,Option.map_some]⟩

theorem Pick.inputs (selected : Pick kid w)
    (homogeneous : ∀ packet ∈ packets, packet.keypair = kid) : Inputs packets w := by
  intro d device packet member
  have bound := selected.1 d.nextKeypairId (by simp only [cursor,device,Option.map_some])
  rw [homogeneous packet member]
  exact ⟨bound,selected.2⟩

theorem pick_frame {action : WG.M α} (cores : SameView pool action)
    (lower : Preserves (Lower (kid + 1)) action) : Preserves (Pick kid) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b selected run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp cores w a result v b run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp lower w a result v b selected.1 run,
    same ▸ selected.2⟩

theorem pick_reservation (kid : KeypairId) : Preserves (Pick kid) (Nonce.reserveNative kid) := by
  apply pick_frame (StagingMaterial.reserve_pool kid)
  unfold Nonce.reserveNative
  exact preserves_bind (lower_key_read kid) (fun _ =>
    preserves_bind (lower_metadata (setKeypair_metadata _ _)) (fun _ => preserves_pure _))

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
