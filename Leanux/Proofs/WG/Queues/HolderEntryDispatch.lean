import Leanux.Proofs.WG.Queues.HolderEntryControls
import Leanux.Proofs.WG.Queues.BaseCoherenceCalls
import Leanux.Proofs.WG.Origins.OwnerSyscalls

/-! The original transmit dispatcher retains the receive entry on every normal
status. Its newly acquired transmit holders stay charged; the owner invariant
comes from the same original journal, including reached stopped prefixes. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDispatch
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

theorem wg_store (hi : HolderEntry.Inv cs loans h w)
    (same : wgStoreView v.wg=wgStoreView w.wg) : HolderEntry.Inv cs loans h v := by
  have kept : HolderEntry.Inv cs loans h {w with wg:=v.wg} :=
    HolderEntry.store hi (by simp only [productStoreView,same])
  exact ⟨kept.1,OwnerControlCalls.store h w v same hi.2⟩

private def Core (cs : Ledger) (loans : Reservations) (w : WGWorld) : Prop :=
  Boundary cs loans w ∧ HolderDeviceCreate.OptionalPhysical w ∧ BaseCoherence.Inv w ∧ CurrentSlots.Inv w

private theorem core_store (hi : Core cs loans w) (same : wgStoreView v=wgStoreView w) : Core cs loans v := by
  have dev := congrArg WGStoreView.dev same
  exact ⟨HolderInitial.store hi.1 same,
    HolderStopPhysical.optional_cell hi.2.1 (congrArg (fun d : Option Device=>RxRing.nativeCell {dev:=d}) dev),
    BaseCoherence.transport hi.2.2.1 (congrArg (fun d : Option Device=>BaseCoherence.view {dev:=d}) dev),
    CurrentSlots.fields_transport hi.2.2.2 (congrArg (fun d : Option Device=>CurrentSlots.fields {dev:=d}) dev)⟩

private theorem xmit_core (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Preserves (Core cs loans) (wgXmit family addr packets mtu) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (HolderXmit.boundary family addr packets mtu) w a result v b hi.1 run,
    HolderStopPhysical.optional_cell hi.2.1
      ((ProjectedAction.iff_run_ambient _ _ _).mp (RxRing.wgXmit_cell family addr packets mtu) w a result v b run),
    BaseCoherence.transport hi.2.2.1
      ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.wgXmit_view family addr packets mtu) w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.wgXmit_preserves family addr packets mtu) w a result v b hi.2.2.2 run⟩

private theorem stored (action : Leanux.M α) (frame : SameProductStore action) :
    Preserves (fun w : World=>Core cs loans w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact core_store hi (congrArg (fun p : ProductStore43=>p.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w result v run))

private theorem native (action : WG.M α) (keeps : Preserves (Core cs loans) action) :
    Preserves (fun w : World=>Core cs loans w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact (hoare_iff_run_ambient _ _ _).mp keeps w.wg w.ambient result v.wg v.ambient hi
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
      action w v result run)

private theorem ambient (action : AmbientM α) :
    Preserves (fun w : World=>Core cs loans w.wg) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi=>hi)

private theorem fs (action : FS.M α) :
    Preserves (fun w : World=>Core cs loans w.wg) (liftFS action) :=
  productFS_spec action _ (fun _ _ _ _ hi=>hi)

private theorem routing (action : Net.M α) :
    Preserves (fun w : World=>Core cs loans w.wg) (monadLift action : Leanux.M α) :=
  stored _ (fun initial=>productRouting_spec action (fun s=>s=initial))

private theorem dispatch_core (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    Preserves (fun w : World=>Core cs loans w.wg) (dispatch (.wgXmit family addr payload opts)) := by
  unfold dispatch socketCallOn
  simp (config := {zeta := false}) only [unsupported,Env.fixtureSend,skipCut]
  repeat' first
    | (allocation_release_lift_from WG.M; exact native _ (xmit_core _ _ _ _))
    | (rx_retention_head Env.xmitMulticastLoop; exact stored _
        ((pinned_const _private.Leanux.Proofs.WG.Queues.BatchAccount.«0».Leanux.Proofs.WG.Queues.RxCredits.BatchAccount.multicast_store) _ _))
    | (rx_retention_head Env.xmitPackets; exact stored _ (xmitPackets_sameKernel _ _ _ _))
    | (rx_retention_head getWG; exact stored _ (fun initial=>productGetWG_spec (fun s=>s=initial)))
    | (allocation_release_lift_from Net.M; exact routing _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_lift_from FS.M; exact fs _)
    | rx_retention_step

/-- The exact source route, descriptor and packetization guards stay in the
dispatch. Negative normal returns retain the same receive ledger as success. -/
theorem xmit (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    PrefixPreserves (HolderEntry.Inv cs loans) OwnerChecks.Safe
      (RxHistory.syscallDispatch (.wgXmit family addr payload opts)) := by
  intro w h hi
  obtain ⟨suffix,hist,safe,post⟩ := OwnerSyscalls.dispatch (.wgXmit family addr payload opts) w h hi.2
  refine ⟨suffix,hist,safe,?_⟩
  cases run : (runPrefix (RxHistory.syscallDispatch (.wgXmit family addr payload opts)) w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at post
    have actual := ((RxHistory.syscallDispatch_erases (.wgXmit family addr payload opts)) w h).symm.trans run
    have kept := (hoare_iff_run _ _ _).mp (dispatch_core family addr payload opts) w out.1 out.2
      ⟨hi.1.1.1,hi.1.2.1,hi.1.1.2.1,hi.1.2.2⟩ actual
    exact ⟨⟨⟨kept.1,kept.2.2.1,HolderAuxiliary.owner_configured post⟩,kept.2.1,kept.2.2.2⟩,post⟩

end Leanux.Proofs.WG.Queues.RxCredits.HolderEntryDispatch
