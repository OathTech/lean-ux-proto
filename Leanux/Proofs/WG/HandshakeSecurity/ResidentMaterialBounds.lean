import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialStaging
import Leanux.Proofs.WG.TransmitSecurity.JournalProjection
import Leanux.Proofs.WG.TransmitSecurity.DriverStagingProjection

/-! The companion C1 carrier at actual driver cuts. Configured identity is
needed by native session creation, while current-slot bounds supply staging's
fresh-frontier exclusion. Neither component assumes responder chronology. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

def Bounds (w : WGWorld) : Prop := ConfiguredIdentity.Inv w ∧ CurrentSlots.Inv w

def Carrier (h : List Journal.Event) (w : WGWorld) : Prop := JournalInv h w ∧ Bounds w

abbrev CarrierSafe (g : WGPrefix Journal.Event α) :=
  StatePrefixPreserves (fun h w _ => Carrier h w) Safe g

theorem bounds_initial (net bare : Bool) : Bounds (Runner.initialWG net bare) :=
  ⟨ConfiguredMaintenance.configured_initial net bare _ rfl,CurrentSlots.initial net bare _ rfl⟩

theorem carrier_initial (net bare : Bool) : Carrier [] (Runner.initialWG net bare) :=
  ⟨initial_journal net bare,bounds_initial net bare⟩

theorem bounds_join {action : WG.M α}
    (configured : Preserves ConfiguredIdentity.Inv action) (slots : Preserves CurrentSlots.Inv action) :
    Preserves Bounds action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp configured w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp slots w a x v b hi.2 run⟩

theorem bounds_frame {action : WG.M α}
    (configured : SameView ConfiguredIdentity.view action) (slots : Preserves CurrentSlots.Inv action) :
    Preserves Bounds action := bounds_join (ConfiguredRemoval.frame configured) slots

theorem bounds_store {action : WG.M α} (same : SameWGStore action) : Preserves Bounds action :=
  bounds_frame (ConfiguredIdentity.sameWG (project := id) same) (CurrentSlots.store_preserves same)

theorem bounds_session (pid : PeerId) : Preserves Bounds (beginSession pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
      (ConfiguredRemoval.frame (ConfiguredMaintenance.beginSession_view pid)) w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.beginSession_preserves pid) w a x v b ⟨hi.2,hi.1⟩ run⟩

theorem bounds_staging (pid : PeerId) : Preserves Bounds (sendStagedPackets pid) :=
  bounds_join (ConfiguredTraffic.staged pid) (CurrentSlots.sendStagedPackets_preserves pid)

theorem staging_erases (pid : PeerId) :
    ErasesStatePrefix (Driver.stagingObserved Journal.hooks pid) (sendStagedPackets pid) := by
  intro w a h
  have projection := Driver.staging_projects Journal.hooks_projects pid
  rw [Driver.nonce_staging_specialization] at projection
  have same := congrArg Prod.fst (projection w a h)
  rw [Nonce.stagingObserved_erases pid] at same
  cases found : (runPrefix ((Driver.stagingObserved Journal.hooks pid).run w) a h).1 <;>
    simpa only [found,Except.map,id_eq,Prod.map_id,Prod.eta] using same.symm

/-- The same actual staging execution carries the C1 bounds and the packet
material journal. Its internal allocation input is derived, not assumed. -/
theorem staging_carrier (pid : PeerId) : CarrierSafe (Driver.stagingObserved Journal.hooks pid) := by
  intro w a h hi
  obtain ⟨suffix,eq,safe,post⟩ := staging pid w a h ⟨hi.1,hi.2.2⟩
  refine ⟨suffix,eq,safe,?_⟩
  cases result : (runPrefix ((Driver.stagingObserved Journal.hooks pid).run w) a h).1 with
  | error stop => trivial
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    simp only [result] at post
    have native : ((sendStagedPackets pid).run w).run a = .ok ((value,v),b) :=
      (staging_erases pid w a h).symm.trans result
    exact ⟨post,(hoare_iff_run_ambient _ _ _).mp (bounds_staging pid) w a value v b hi.2 native⟩

theorem carrier_lift (action : WG.M α) (material : ∀ h, Preserves (Inv h) action)
    (bounds : Preserves Bounds action) : CarrierSafe (liftWGPrefix action) :=
  state_extra action material bounds

theorem session_carrier (pid : PeerId) : CarrierSafe (Journal.session pid) := by
  apply state_quiet_extra (StateAppends.focus _ _ _)
    (fun w => focusPrefix_other _ _ _ (fun _ => rfl) ((DriverCuts.session pid).run w))
    (focusStatePrefix_erases _ _ (DriverCuts.session_erases pid))
  intro h
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (session pid) w a x v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp (bounds_session pid) w a x v b hi.2 run⟩

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
