import Leanux.Proofs.WG.Index.LifecycleControlSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.LifecycleIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits Queues.RxCredits.DurableHolders
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open ConfigurationIndex

theorem open_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans) wgOpen := by
  apply Noise.LifecycleSource.open_preserves (Entry cs loans) (read_entry cs loans)
  · intro pid
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b pre run
    exact (getPeer_normal pid w v p a b run).1 ▸ pre
  · exact fun port => socket_entry cs loans (socketInit_sameSocket port)
  · exact staged_entry cs loans
  · exact keepalive_entry cs loans

theorem up_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head modifyDev; exact running_entry cs loans _)
    | (rx_retention_head wgOpen; exact open_entry cs loans)
    | rx_retention_step

theorem create_core : Preserves Reached.Core wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have observed := congrArg (fun s : WGStoreView => s.dev.map deviceFields) same
    rw [link_fields,link_fields] at observed
    exact fields_core w v observed pre
  · intro d device
    have table := congrArg (fun s : WGStoreView => s.dev.map Device.indexTable) fresh
    simp only [linkView,linkStore,linkDevice,wgStoreView,device,
      registeredLink,setupLink,Option.map_some,Option.some.injEq] at table
    refine ⟨empty_table_safe d table,hashSlotCoverage_empty d table,?_,?_⟩
    · intro entry member
      simp [table] at member
    · intro entry member
      simp [table] at member

theorem create_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  exact ⟨⟨(hoare_iff_run_ambient _ _ _).mp HolderDeviceCreate.create w a result v b pre.1.1 run,
    (hoare_iff_run_ambient _ _ _).mp DeviceAuxEntry.create_base w a result v b pre.1.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp DeviceAuxEntry.create_configured w a result v b pre.1.2.2 run⟩,
    (hoare_iff_run_ambient _ _ _).mp DeviceAuxEntry.create_slots w a result v b pre.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp create_core w a result v b pre.2.2 run⟩

theorem absent_core (w : WGWorld) (absent : w.dev=none) : Reached.Core w := by
  intro d present
  simp [absent] at present

theorem destruct_core : Ensures wgDestruct (fun _ => True)
    (fun _ w => w.dev=none ∧ Reached.Core w) := by
  intro w a result v b _ run
  have absent := wgDestruct_absent w a result v b trivial run
  exact ⟨absent,absent_core v absent⟩

theorem destruct_entry :
    Hoare wgDestruct
      (fun w => Entry [] [] w ∧ activeCursor w.nlSock7=none ∧ activeCursor w.nlSock8=none)
      (fun _ w => w.dev=none ∧ Entry [] [] w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  obtain ⟨absent,account,_⟩ := (hoare_iff_run_ambient _ _ _).mp
    HolderDeviceDelete.destruct_empty w a result v b ⟨pre.1.1.1,pre.2⟩ run
  have slots : CurrentSlots.Inv v := by
    apply (CurrentSlots.inv_iff v).mpr
    intro d pid p kid device
    simp [absent] at device
  have base : BaseCoherence.Inv v := by simp [BaseCoherence.Inv,
    BaseCoherence.slots,BaseCoherence.rows,absent]
  have configured : ConfiguredIdentity.Inv v := by
    intro s present
    simp [ConfiguredIdentity.view,absent] at present
  exact ⟨absent,⟨account,base,configured⟩,slots,absent_core v absent⟩

end Leanux.Proofs.WG.Index.LifecycleIndex
