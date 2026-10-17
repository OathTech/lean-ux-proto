import Leanux.Proofs.WG.Index.StagedSource
import Leanux.Proofs.WG.Index.PeerReleaseTableFrames
import Leanux.WG.Receive

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- Local table-invariant variant of WGMore.enqueuePerDeviceAndPeerRx_spec.
Normal receive enqueue paths preserve numeric and owner index uniqueness and the keypair allocation bound, including queue-full returns. -/
theorem enqueuePerDeviceAndPeerRx_spec_tables_variant (id : SkbId) :
    Campaign2.Ensures (enqueuePerDeviceAndPeerRx id) View.TablesSafe (fun _ => View.TablesSafe) := by
  change Ensures (enqueuePerDeviceAndPeerRx id) TablesSafeWG (fun _ => TablesSafeWG)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hpeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r final after pre run).1
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hmodify (f : Device → Device) (same : ∀ d, TimerDiscipline.tableCursor (f d) = TimerDiscipline.tableCursor d) :
      Ensures (modifyDev f) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run
    cases run
    exact tablesSafe_of_cursor g _ (by simp [Option.map_map, Function.comp_def, same]) pre
  have hcpu (last : Int) : Ensures (cpumaskNextOnlineFrom last) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold cpumaskNextOnlineFrom
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hbranch _ _) ?_
    intro wrap
    cases wrap <;> exact hpure _
  have hqueue : Ensures (queueDeviceWork .decryptWorker : WG.M Unit) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.queueDeviceWork .decryptWorker) TablesSafeWG)
  have hgetRx (id : SkbId) : Ensures (getRxSkb id) TablesSafeWG (fun _ => TablesSafeWG) :=
    liftSkb_tables (SkbStore.getRx id)
  have hsetRx (id : SkbId) (f : RxPacket → RxPacket) : Ensures (setRxSkb id f) TablesSafeWG (fun _ => TablesSafeWG) :=
    liftSkb_tables (SkbStore.setRx id f)
  unfold enqueuePerDeviceAndPeerRx
  repeat' first
    | with_reducible exact hpure _
    | with_reducible exact hbranch _ _
    | exact hpeer _
    | with_reducible exact hdev
    | with_reducible exact hcpu _
    | with_reducible exact hqueue
    | exact hgetRx _
    | exact hsetRx _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | with_reducible exact hmodify _ (fun _ => rfl)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | split
    | simp only [bind_assoc, pure_bind]

/-- Local table-invariant variant of WGMore.enqueuePerPeerRx_pure_spec.
Publishing a receive state with the actual empty callback preserves the
index invariant; no claim is made for arbitrary callbacks. -/
theorem enqueuePerPeerRx_pure_spec_tables_variant (id : SkbId) (state : PacketState) :
    Campaign2.Ensures (enqueuePerPeerRx (pure () : WG.M Unit) id state)
      View.TablesSafe (fun _ => View.TablesSafe) := by
  change Ensures (enqueuePerPeerRx (pure () : WG.M Unit) id state) TablesSafeWG (fun _ => TablesSafeWG)
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run; cases run; exact pre
  have hbranch (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) TablesSafeWG (fun _ => TablesSafeWG) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) TablesSafeWG)
  have hpeer (pid : PeerId) : Ensures (getPeer pid) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid TablesSafeWG) g a r final after pre run).1
  have hdev : Ensures getDev TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run
    cases hd : g.dev with
    | none => simp [getDev, hd, invariant, AmbientM.invariant] at run; cases run
    | some d => simp [getDev, hd] at run; rcases run with ⟨⟨rfl,rfl⟩,rfl⟩; exact pre
  have hstop {α : Type} (msg : String) : Ensures (invariant msg : WG.M α) TablesSafeWG (fun _ => TablesSafeWG) := by
    intro g a r final after pre run; cases run
  have hkey (id : KeypairId) : Ensures (getKeypair id) TablesSafeWG (fun _ => TablesSafeWG) := by
    unfold getKeypair
    refine ensures_bind _ _ hdev ?_
    intro d
    split
    · exact hpure _
    · exact hstop _
  have hword (id : KeypairId) : Ensures (IndexOwner.peerDeref (.keypair id)) TablesSafeWG (fun _ => TablesSafeWG) := by
    simp only [IndexOwner.peerDeref, IndexOwner.peerWord, bind_assoc, pure_bind]
    refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ (hkey id) ?_
    intro k
    cases k.peer with
    | none => exact (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.unsupported _) TablesSafeWG)
    | some pid => exact hpure _
  have hgetRx (id : SkbId) : Ensures (getRxSkb id) TablesSafeWG (fun _ => TablesSafeWG) :=
    liftSkb_tables (SkbStore.getRx id)
  have hsetRx (id : SkbId) (f : RxPacket → RxPacket) : Ensures (setRxSkb id f) TablesSafeWG (fun _ => TablesSafeWG) :=
    liftSkb_tables (SkbStore.setRx id f)
  unfold enqueuePerPeerRx
  repeat' first
    | with_reducible exact hpure _
    | exact hpeer _
    | exact hword _
    | with_reducible exact hstop _
    | exact hgetRx _
    | exact hsetRx _ _
    | with_reducible exact (ensures_iff _ _ _).mpr (peerGet_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (peerPut_tables _)
    | with_reducible exact (ensures_iff _ _ _).mpr (setPeer_tables _ _)
    | (with_reducible refine ensures_bind (Q := fun _ => TablesSafeWG) _ _ ?_ (fun _ => ?_))
    | split
    | simp only [bind_assoc, pure_bind]

end Leanux.Proofs.WG.Index
