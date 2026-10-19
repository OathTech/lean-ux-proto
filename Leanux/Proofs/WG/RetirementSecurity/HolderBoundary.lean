import Leanux.Proofs.WG.RetirementSecurity.KeySlotInitialized
import Leanux.Proofs.WG.RetirementSecurity.HolderConfigurationCommand
import Leanux.Proofs.WG.Queues.SlotDevice

/-! Native boundary transport combines the independently derived live-slot
carrier with peer funding and exact key credit. Slot protection is reconstructed
from those facts at each public boundary; it is not an incoming extra premise. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderBoundary
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open StackOwnership

def Entry (temporary : Credits.Ledger) (carriers : Ledger) (loans : Reservations)
    (w : WGWorld) : Prop :=
  HolderKeepalive.Ready temporary w ∧ DeviceAuxEntry.Entry carriers loans w ∧ KeySlotLiveness.Inv w

theorem configuration (before : Entry temporary carriers loans w) :
    HolderConfiguration.Entry temporary carriers loans w := by
  obtain ⟨holders,funded,stable⟩ := before.2.1.1.1
  exact ⟨before.1,⟨holders,funded,stable,
    KeySlotLiveness.references before.2.2 funded before.2.1.1.2.1 before.2.1.1.2.2⟩,
    before.2.1.1.2⟩

theorem initial (net bare : Bool) : Entry [] [] [] (Runner.initialWG net bare) := by
  have peer := HolderEntry.initialized net bare ({wg:=Runner.initialWG net bare,ambient:={env:=Runner.harnessEnv,timing:=Env.timing},fs:={},tasks:=Runner.initialTasks 0} : World) rfl
  exact ⟨⟨initial_holder_account net bare,⟨[],allocation_initial net bare _ rfl⟩,peer.1.2.2⟩,
    peer.1,KeySlotLiveness.initial net bare⟩

theorem of_owner (keys : HolderAccount temporary w.wg) (owner : HolderEntry.Inv carriers loans h w)
    (live : KeySlotLiveness.Inv w.wg) : Entry temporary carriers loans w.wg :=
  ⟨⟨keys,⟨_,owner.2.allocation⟩,owner.1.2.2⟩,owner.1,live⟩

/-- The whole actual peer command retains all input support needed by the next
command, with slot references derived afresh from actual output liveness. -/
theorem command (attrs : PeerAttrs) : Preserves (Entry temporary carriers loans) (WG.setPeerCmd attrs) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have keys := (hoare_iff_run_ambient _ _ _).mp (HolderConfiguration.command attrs)
    w a result v b (configuration before) run
  have allocation := Allocated.native (ConfigurationCall.erases (.peer attrs))
    (ConfigurationCall.allocation (.peer attrs)) before.1.2.1 a b run
  have peer := (hoare_iff_run_ambient _ _ _).mp (DeviceBoundary.command attrs)
    w a result v b before.2.1.1 run
  have slots := (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.Configuration.command attrs)
    w a result v b before.2.1.2.2 run
  have live := (hoare_iff_run_ambient _ _ _).mp (KeySlotLiveness.config_command attrs)
    w a result v b before.2.2 run
  have physical := (hoare_iff_run_ambient _ _ _).mp (ConfigurationPhysical.command_physical attrs)
    w a result v b before.2.1.2.1 run
  exact ⟨⟨keys,allocation,slots⟩,⟨peer,physical,slots⟩,live⟩

theorem peer_list (attrs : DeviceAttrs) :
    Preserves (Entry temporary carriers loans) (Configuration.devicePeersSource attrs) := by
  unfold Configuration.devicePeersSource
  simp (config := {zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerCmd; exact command _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Entry temporary carriers loans)
       intro x b
       change Preserves (Entry temporary carriers loans) _)
    | rx_retention_step

/-- A concrete initialized endpoint supplies every boundary component except
exact key credit, which remains the one explicitly stated closure obligation. -/
theorem initialized_entry (trace : Runner.Trace) (placeholders : Bool)
    (run : Leanux.Proofs.Logged.runPrefixOuter (RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (keys : HolderAccount temporary w.wg) :
    ∃carriers,Entry temporary carriers [] w.wg := by
  obtain ⟨carriers,_,owner⟩ := RunnerAccount.normal trace placeholders run
  exact ⟨carriers,of_owner keys owner (KeySlotInitialized.normal trace placeholders run)⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderBoundary
