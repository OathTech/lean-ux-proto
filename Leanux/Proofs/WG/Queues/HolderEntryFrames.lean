import Leanux.Proofs.WG.Queues.HolderEntry

/-! Quiet control fields of the outer account. The frame records all existing
account components; it does not replace a lifecycle operation's source proof. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderEntryFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def fields (w : WGWorld) :=
  (HolderEncrypt.fields w,BaseCoherence.view w,ConfiguredIdentity.view w,
    CurrentSlots.fields w,RxRing.nativeCell w)

theorem transport (hi : DeviceAuxEntry.Entry cs loans w) (same : fields v=fields w) :
    DeviceAuxEntry.Entry cs loans v := by
  refine ⟨⟨HolderEncrypt.boundary_fields hi.1.1 (congrArg Prod.fst same),
    BaseCoherence.transport hi.1.2.1 (congrArg (fun p=>p.2.1) same),?_⟩,
    HolderStopPhysical.optional_cell hi.2.1 (congrArg (fun p=>p.2.2.2.2) same),
    CurrentSlots.fields_transport hi.2.2 (congrArg (fun p=>p.2.2.2.1) same)⟩
  intro s hs
  exact hi.1.2.2 s ((congrArg (fun p=>p.2.2.1) same).symm.trans hs)

theorem store (hi : DeviceAuxEntry.Entry cs loans w) (same : wgStoreView v=wgStoreView w) :
    DeviceAuxEntry.Entry cs loans v := by
  apply transport hi
  exact congrArg (fun s : WGStoreView=>fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8}) same

theorem native {action : WG.M α} (same : SameView fields action) :
    Preserves (DeviceAuxEntry.Entry cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact transport hi ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem product {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact store hi (congrArg (fun p : ProductStore43=>p.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp same w result v run))

theorem scalar_fields (w : World) :
    fields { dev := (envScalarView w).2.2.2.dev, nlSock7 := (envScalarView w).2.2.2.nlSock7, nlSock8 := (envScalarView w).2.2.2.nlSock8 }=fields w.wg := by
  unfold fields CurrentSlots.fields HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  unfold BaseCoherence.view BaseCoherence.slots BaseCoherence.rows
  unfold ConfiguredIdentity.view ConfiguredIdentity.state
  simp only [envScalarView,envScalarStore,productStoreView,wgStoreView,envScalarDevice,
    Option.map_map,Option.map_bind,Option.bind_map,Function.comp_def,rxView]

/-- The environment MTU path changes only the already declared scalar mask. -/
theorem mtu (n : Nat) :
    Preserves (fun w : World=>DeviceAuxEntry.Entry cs loans w.wg) (Env.setMtu n) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  apply transport hi
  have same := (ProjectedAction.iff_run _ _ _).mp (setMtu_sameEnvScalar n) w result v run
  rw [←scalar_fields v,←scalar_fields w,same]

end Leanux.Proofs.WG.Queues.RxCredits.HolderEntryFrames
