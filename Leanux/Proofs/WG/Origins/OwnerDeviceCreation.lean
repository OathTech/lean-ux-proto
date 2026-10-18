import Leanux.Proofs.WG.Origins.OwnerDevice

/-! Device creation and deletion retain the carrier at normal endpoints.
Notifier callbacks remain arbitrary native actions with explicit contracts. -/
namespace Leanux.Proofs.WG.OwnerDeviceCreation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Queues.RxCredits OwnerBounds OwnerControls OwnerDevice

theorem wgDelete_preserves (onDown onUnregister : WG.M Unit)
    (down : Preserves Carrier onDown) (unregister : Preserves Carrier onUnregister) :
    Preserves Carrier (wgDelete onDown onUnregister) := by
  unfold wgDelete
  simp (config := {zeta := false}) only [getWG,monadLift_self,skipCut]
  repeat' first
    | exact down
    | exact unregister
    | (allocation_release_head wgDown; exact wgDown_preserves)
    | (allocation_release_head wgDestruct; exact wgDestruct_preserves)
    | (allocation_release_head mayHaveSlept; exact store _ mayHaveSlept_sameWGStore)
    | owner_control_step

theorem wgDelete_default_preserves : Preserves Carrier (wgDelete : WG.M Int) :=
  wgDelete_preserves _ _ (preserves_pure ()) (preserves_pure ())

theorem wgCreate_preserves : Preserves Carrier wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v finalAmbient hi hr
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w ambient result v finalAmbient rfl hr
  rcases endpoint with same | ⟨_,fresh⟩
  · have material := (ProjectedAction.iff_run_ambient _ _ _).mp
      Origins.Retaining.wgCreate_material w ambient result v finalAmbient hr
    apply OwnerCompletion.carrier_transport (allowed := NoPromotion) hi material
    · have fields := congrArg (fun s : WGStoreView => OwnerCompletion.geometry {dev := s.dev}) same
      simpa only [id_eq,OwnerCompletion.geometry,rxView,linkView,linkStore,wgStoreView,linkDevice,
        Option.map_map,Option.bind_map,Function.comp_def] using fields
    · apply keyEffect_of_view
      have keys := congrArg (fun s : WGStoreView => keyView {dev := s.dev}) same
      unfold keyView keyWords currentCells at keys ⊢
      simpa only [id_eq,linkView,linkStore,wgStoreView,linkDevice,
        Option.map_map,Option.bind_map,Function.comp_def] using keys
  · have empty (d : Device) (hd : v.dev = some d) :
        d.keypairs = {} ∧ d.rxSkbs = {} := by
      have fields := congrArg (fun s : WGStoreView => s.dev.map fun d => (d.keypairs,d.rxSkbs)) fresh
      simpa only [linkView,linkStore,wgStoreView,linkDevice,registeredLink,setupLink,hd,
        Option.map_some,Option.some.injEq,Prod.mk.injEq] using fields
    constructor
    · intro d hd slot key hk
      simp [(empty d hd).1] at hk
    · intro d id pkt hd hp
      simp [(empty d hd).2] at hp
    · intro d hd id pkt hp
      simp [(empty d hd).2] at hp

end Leanux.Proofs.WG.OwnerDeviceCreation
