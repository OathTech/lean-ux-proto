import Leanux.Proofs.WG.Queues.HolderInitial
import Leanux.Proofs.WG.Queues.HolderDeviceDelete
import Leanux.Proofs.WG.Queues.DeviceAuxEntry
import Leanux.Proofs.WG.Queues.DevicePhysical
import Leanux.Proofs.WG.Origins.OwnerControlCalls

/-! One outer boundary packages the existing funded account and structural
entry with the original owner journal. Physical absence is explicit; the
fixed-cut scheduler domain is recovered only at an actual present device. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderEntry
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

def Inv (cs : Ledger) (loans : Reservations) (h : List RxHistory.Event) (w : World) : Prop :=
  DeviceAuxEntry.Entry cs loans w.wg ∧ OwnerChecks.Inv h w

theorem initialized (net bare : Bool) (w : World)
    (same : wgStoreView w.wg=wgStoreView (Runner.initialWG net bare)) : Inv [] [] [] w := by
  obtain ⟨account,physical,owners,slots,base⟩ := HolderInitial.initial net bare w same
  exact ⟨⟨⟨account,base,HolderAuxiliary.owner_configured owners⟩,physical,slots⟩,owners⟩

theorem store (hi : Inv cs loans h w)
    (same : productStoreView v=productStoreView w) : Inv cs loans h v := by
  have wg := congrArg (fun p : ProductStore43=>p.2.2.2) same
  have dev : v.wg.dev=w.wg.dev := congrArg WGStoreView.dev wg
  have owner := OwnerWorkers.store h w v same hi.2
  refine ⟨⟨⟨HolderInitial.store hi.1.1.1 wg,?_,HolderAuxiliary.owner_configured owner⟩,?_,?_⟩,owner⟩
  · exact BaseCoherence.transport hi.1.1.2.1
      (congrArg (fun d : Option Device=>BaseCoherence.view {dev:=d}) dev)
  · simpa only [HolderDeviceCreate.OptionalPhysical,NativeRxInv,RxRing.nativeCell,dev] using hi.1.2.1
  · exact CurrentSlots.fields_transport hi.1.2.2
      (congrArg (fun d : Option Device=>CurrentSlots.fields {dev:=d}) dev)

/-- A real present-device guard chooses the existing physical branch. -/
theorem to_aux (hi : Inv cs loans h w) (present : w.wg.dev.isSome=true) :
    HolderAuxiliary.Inv cs loans h h w :=
  HolderInitial.at_cut hi.1.1.1 (HolderInitial.physical_present hi.1.2.1 present) hi.2 hi.1.2.2

/-- Recover the outer entry using precisely the reached removal suffix.
Base coherence is a separate source fact, not inferred from configured rows. -/
theorem of_aux (hi : HolderAuxiliary.Inv initial loans before h w)
    (base : BaseCoherence.Inv w.wg) :
    ∃ suffix, h=before++suffix ∧ Inv (remaining initial (NapiCarrier.removedPackets suffix)) loans h w := by
  obtain ⟨suffix,hist,account⟩ := hi.1.1
  exact ⟨suffix,hist,⟨⟨⟨account,base,HolderAuxiliary.owner_configured hi.2.1⟩,
    Or.inr hi.1.2,hi.2.2⟩,hi.2.1⟩⟩

/-- Configuration's physical and slot contracts concern the same native run. -/
theorem configuration (attrs : DeviceAttrs) :
    Preserves (DeviceAuxEntry.Entry cs loans) (wgSetDevice attrs) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have entry := (hoare_iff_run_ambient _ _ _).mp (DevicePhysical.device_entry attrs)
    w a result v b ⟨hi.1,hi.2.1⟩ run
  exact ⟨entry.1,entry.2,(hoare_iff_run_ambient _ _ _).mp
    (CurrentSlots.Device.device attrs) w a result v b hi.2.2 run⟩

/-- The normal state and safe stopped journal come from the same original
observer; only the normal branch has a returned state. -/
theorem native (action : PrefixM LifetimeEvent α) (original : WG.M α)
    (erase : ErasesPrefix action (liftWG original))
    (account : Preserves (DeviceAuxEntry.Entry cs loans) original)
    (owner : OwnerChecks.Preserves (RxHistory.mixed action)) :
    PrefixPreserves (Inv cs loans) OwnerChecks.Safe (RxHistory.mixed action) := by
  intro w h hi
  obtain ⟨suffix,hist,safe,post⟩ := owner w h hi.2
  refine ⟨suffix,hist,safe,?_⟩
  cases run : (runPrefix (RxHistory.mixed action) w h).1 with
  | error e => trivial
  | ok out =>
    rw [run] at post
    have source := ((RxHistory.mixed_erases erase) w h).symm.trans run
    have nativeRun := (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt)
      original w out.2 out.1 source
    exact ⟨(hoare_iff_run_ambient _ _ _).mp account
      w.wg w.ambient out.1 out.2.wg out.2.ambient hi.1 nativeRun,post⟩

theorem create : PrefixPreserves (Inv cs loans) OwnerChecks.Safe
    (RxHistory.mixed (liftWGObserver wgCreatePrefix)) :=
  native _ _ (liftWGObserver_erases wgCreatePrefix_erases) DeviceAuxEntry.create OwnerControlCalls.create

theorem configure (attrs : DeviceAttrs) : PrefixPreserves (Inv cs loans) OwnerChecks.Safe
    (RxHistory.mixed (liftWGObserver (wgSetDevicePrefix attrs))) :=
  native _ _ (liftWGObserver_erases (wgSetDevicePrefix_erases attrs))
    (configuration attrs) (JointOwnerDevice.wgSetDevice_checked attrs)

/-- Guarded deletion discharges the actual receive ledger and yields an
absent-device entry. The observer supplies only a journal on a stopped prefix. -/
theorem delete_normal (hi : Inv cs [] h w)
    (run : runPrefix (RxHistory.audit envWgDeleteAudit) w h=(.ok (result,v),k)) :
    cs=[] ∧ v.wg.dev=none ∧ Inv cs [] k v := by
  have actual := ((RxHistory.audit_erases envWgDeleteAudit_erases) w h).symm.trans (congrArg Prod.fst run)
  obtain ⟨empty,absent,account,physical⟩ := HolderDeviceDelete.delete_normal w v hi.1.1.1 hi.1.2.1 actual
  have owners := (OwnerControlCalls.delete w h hi.2).choose_spec.2.2
  rw [run] at owners
  refine ⟨empty,absent,⟨⟨⟨account,?_,HolderAuxiliary.owner_configured owners⟩,physical,?_⟩,owners⟩⟩
  · simp [BaseCoherence.Inv,BaseCoherence.slots,BaseCoherence.rows,absent]
  · apply (CurrentSlots.inv_iff v.wg).mpr
    intro d pid p kid hd
    simp [absent] at hd

theorem delete : PrefixPreserves (Inv cs []) OwnerChecks.Safe (RxHistory.audit envWgDeleteAudit) := by
  intro w h hi
  obtain ⟨suffix,hist,safe,_⟩ := OwnerControlCalls.delete w h hi.2
  refine ⟨suffix,hist,safe,?_⟩
  cases run : (runPrefix (RxHistory.audit envWgDeleteAudit) w h).1 with
  | error e => trivial
  | ok out => exact (delete_normal hi (Prod.ext run rfl)).2.2

end Leanux.Proofs.WG.Queues.RxCredits.HolderEntry
