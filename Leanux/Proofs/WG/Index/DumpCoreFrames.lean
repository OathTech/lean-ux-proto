import Leanux.Proofs.WG.Index.DumpCoreEffects

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DumpCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits Queues.RxCredits.DurableHolders

theorem contracts (entry : Option Device) :
    Config.DumpInvariant.Contracts (fun w=>DeviceFrame entry w.dev) where
  stable := by
    intro w v same pre
    have device : v.dev=w.dev := congrArg WGStoreView.dev same
    rw [device]
    exact pre
  acquire pid := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    exact StagingRich.trans pre (deviceFrame_of_rich
      (StagingRich.peerGet_rich pid w w a result v b (StagingRich.refl w) run))
  release pid := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    exact StagingRich.trans pre (deviceFrame_of_rich
      (StagingRich.peerPut_rich w pid w a result v b (StagingRich.refl w) run))

theorem call_frame (action : NetlinkDumpCall) (entry : Option Device) :
    Preserves (fun w=>DeviceFrame entry w.dev) action.original :=
  Config.DumpInvariant.call (contracts entry) action

theorem acquire_shape (present : Bool) (pid : PeerId) :
    Preserves (Shape present) (peerGet pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases device:w.dev with
  | none =>
    simp [peerGet,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident:d.peers[pid]? with
    | none =>
      simp [peerGet,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨after,_⟩ := (ensures_iff _ _ _).mpr
        (Config.peerGet_exact pid d p resident) w a result v b device run
      refine ⟨by simpa [after,device] using pre.1,?_⟩
      intro final ending
      rw [after] at ending
      cases ending
      exact handshake_acquire d pid p resident (pre.2 d device)

theorem release_shape (present : Bool) (peer : Option PeerId) :
    Preserves (Shape present) (peerPut peer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases peer with
  | none =>
    simp [peerPut,branch,AmbientM.branch] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact pre
  | some pid =>
    cases device:w.dev with
    | none =>
      simp [peerPut,requireNotPending,branch,AmbientM.branch,getPeer,getDev,
        device,invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      cases resident:d.peers[pid]? with
      | none =>
        simp [peerPut,requireNotPending,branch,AmbientM.branch,getPeer,getDev,
          device,resident,invariant,AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero:p.refcount=0
        · simp [peerPut,requireNotPending,getPeer,getDev,device,resident,zero,
            refcountDecAndTest,branch,AmbientM.branch,branchCmp,AmbientM.branchCmp,
            invariant,AmbientM.invariant] at run
          cases run
        · have positive :0<p.refcount := by omega
          have after := peerPut_normal_device pid d p resident positive w v a b result device run
          refine ⟨by simpa [after,device] using pre.1,?_⟩
          intro final ending
          rw [after] at ending
          cases ending
          exact handshake_release d pid p resident positive (pre.2 d device)

theorem shape_contracts (present : Bool) : Config.DumpInvariant.Contracts (Shape present) where
  stable := by
    intro w v same pre
    have device : v.dev=w.dev := congrArg WGStoreView.dev same
    refine ⟨by simpa [device] using pre.1,?_⟩
    intro d found
    exact pre.2 d (device.symm.trans found)
  acquire := acquire_shape present
  release := release_shape present

theorem call_shape (action : NetlinkDumpCall) (present : Bool) :
    Preserves (Shape present) action.original :=
  Config.DumpInvariant.call (shape_contracts present) action

theorem essential_contracts : Config.DumpInvariant.Contracts Essentials where
  stable := by
    intro w v same pre
    have device : v.dev=w.dev := congrArg WGStoreView.dev same
    refine ⟨BaseCoherence.transport pre.1 ?_,?_,CurrentSlots.fields_transport pre.2.2 ?_⟩
    · exact congrArg (fun d : Option Device => BaseCoherence.view {dev:=d}) device
    · intro s found
      exact pre.2.1 s (by simpa [ConfiguredIdentity.view,device] using found)
    · exact congrArg (fun d : Option Device => CurrentSlots.fields {dev:=d}) device
  acquire pid := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    refine ⟨BaseCoherence.transport pre.1
      ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.peerGet_view pid) w a result v b run),?_,
      (hoare_iff_run_ambient _ _ _).mp
        (CurrentSlots.fields_preserves (CurrentSlots.peerGet_fields pid)) w a result v b pre.2.2 run⟩
    exact (hoare_iff_run_ambient _ _ _).mp
      (ConfiguredRemoval.frame (CreationLoan.peerGet_configured_view pid)) w a result v b pre.2.1 run
  release peer := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    exact ⟨BaseCoherence.transport pre.1
      ((ProjectedAction.iff_run_ambient _ _ _).mp (BaseCoherence.peerPut_view peer) w a result v b run),
      (hoare_iff_run_ambient _ _ _).mp
        (ConfiguredIdentity.peerPut_preserves peer) w a result v b pre.2.1 run,
      (hoare_iff_run_ambient _ _ _).mp
        (CurrentSlots.peerPut_preserves peer) w a result v b pre.2.2 run⟩

theorem call_essentials (action : NetlinkDumpCall) :
    Preserves Essentials action.original :=
  Config.DumpInvariant.call essential_contracts action

theorem socket_bound_entry (cs : Ledger) (loans : Reservations) (fd : Nat) (w : WGWorld)
    (pre : ConfigurationIndex.Entry cs loans w) :
    ConfigurationIndex.Entry cs loans
      (writeSocket fd {socketAt fd w with bound:=true} w) := by
  obtain ⟨holders,paid,stable⟩ := pre.1.1
  have account:=socket_write_funded paid stable fd {socketAt fd w with bound:=true} rfl
  refine ⟨⟨⟨holders,account.1,account.2⟩,?_,?_⟩,?_,?_⟩ <;>
    unfold writeSocket <;> split
  all_goals first | exact pre.1.2.1 | exact pre.1.2.2 | exact pre.2.1 | exact pre.2.2

end Leanux.Proofs.WG.Index.DumpCore
