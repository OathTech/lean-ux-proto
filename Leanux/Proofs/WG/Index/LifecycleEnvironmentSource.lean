import Leanux.Proofs.WG.Index.LifecycleEnvironmentFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.LifecycleEnvironment
open Leanux Leanux.WG Noise Queues Queues.RxCredits Queues.RxCredits.DurableHolders
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open ConfigurationIndex

theorem detach_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans)
      (modifyDev fun d => {d with carrier:=false,creatingNet:=false}) := by
  apply join_entry cs loans _
  · repeat' device_entry_step
  · repeat' slot_remove_step
  · intro w a result v b pre run
    exact (hoare_iff_run_ambient _ _ _).mp
      (frame_core (modifyDev_fields
        (fun d => {d with carrier:=false,creatingNet:=false}) (fun _=>rfl)))
        w a result v b pre.2 run

theorem preexit_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans) netnsPreExit := by
  apply Noise.LifecycleSource.preexit_preserves (Entry cs loans)
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    cases run
    exact pre
  · exact read_entry cs loans
  · exact detach_entry cs loans
  · exact socket_entry cs loans (socketReinit_sameSocket _ _)
  · exact clearEndpoint_entry cs loans

theorem lift_entry {α : Type} (cs : Ledger) (loans : Reservations)
    (action : WG.M α) (keeps : Preserves (Entry cs loans) action) :
    Preserves (fun w : World => Entry cs loans w.wg) (liftWG action) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  exact (hoare_iff_run_ambient _ _ _).mp keeps w.wg w.ambient result v.wg v.ambient pre
    ((pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) action w v result run)

theorem up_entry (cs : Ledger) (loans : Reservations) :
    Preserves (fun w : World => Entry cs loans w.wg) Env.wgUp :=
  Noise.LifecycleSource.envUp_preserves _
    (fun action same => product_entry cs loans action same)
    (lift_entry cs loans _ (LifecycleIndex.up_entry cs loans))

theorem down_entry (cs : Ledger) (loans : Reservations) :
    Preserves (fun w : World => Entry cs loans w.wg) Env.wgDown :=
  Noise.LifecycleSource.envDown_preserves _
    (fun action same => product_entry cs loans action same)
    (lift_entry cs loans _ (LifecycleIndex.down_entry cs loans))
    (product_entry cs loans _ PendingScheduler.requireIdleDevice_store)

theorem delete_entry (cs : Ledger) :
    Hoare Env.wgDelete
      (fun w : World => Entry cs [] w.wg ∧ HolderDeviceCreate.OptionalPhysical w.wg)
      (fun _ w => cs=[] ∧ w.wg.dev=none ∧ Entry cs [] w.wg ∧
        HolderDeviceCreate.OptionalPhysical w.wg) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v pre run
  obtain ⟨empty,absent,account,physical⟩ :=
    HolderDeviceDelete.delete_normal w v pre.1.1.1 pre.2 run
  have slots : CurrentSlots.Inv v.wg := by
    apply (CurrentSlots.inv_iff v.wg).mpr
    intro d pid p kid device
    simp [absent] at device
  have base : BaseCoherence.Inv v.wg := by
    simp [BaseCoherence.Inv,BaseCoherence.slots,BaseCoherence.rows,absent]
  have configured : ConfiguredIdentity.Inv v.wg := by
    intro s present
    simp [ConfiguredIdentity.view,absent] at present
  exact ⟨empty,absent,⟨⟨account,base,configured⟩,slots,LifecycleIndex.absent_core v.wg absent⟩,physical⟩

end Leanux.Proofs.WG.Index.LifecycleEnvironment
