import Leanux.Proofs.WG.Index.LifecycleCoreFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.LifecycleIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits Queues.RxCredits.DurableHolders
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open ConfigurationIndex

theorem timers_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (timersStop pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  obtain ⟨holders,funded,stable⟩ := pre.1.1
  have work : RetirementWork holders cs loans [] w :=
    ⟨duringWork_initial funded stable,pre.1.2.2,pre.1.2.1,
      fun d hd=>(pre.2.2 d hd).2.1,fun d hd=>(pre.2.2 d hd).2.2.1,
      fun d hd=>(pre.2.2 d hd).2.2.2⟩
  have send := flushedSend_retirementWork holders cs [] loans
    (fun holders paid => initiationIndexContract_actual holders cs paid [] loans)
  have post := (hoare_iff_run_ambient _ _ _).mp
    (timersStop_retirementWork holders cs loans [] send pid) w a result v b work run
  have tables := timersStop_tables pid
    w a result v b (fun d hd=>(pre.2.2 d hd).1) run
  have slots := (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.Removal.stopTimers pid)
    w a result v b pre.2.1 run
  obtain ⟨remaining,_,fundedOut,stableOut⟩ := post.account
  exact ⟨⟨⟨remaining,fundedOut,stableOut⟩,post.base,post.configured⟩,slots,
    fun d hd=>⟨tables d hd,post.covered d hd,post.coherent d hd,post.reserved d hd⟩⟩

theorem handshake_retirement (retired : Reservations) (pid : PeerId) :
    Ensures (handshakeClear pid)
      (fun w => ∀d,w.dev=some d → DeadHashedReserved retired d)
      (fun _ w => ∀d,w.dev=some d → DeadHashedReserved retired d) := by
  intro w a result v b pre run
  cases device : w.dev with
  | none =>
    simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [handshakeClear,IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have clear : Ensures (handshakeClear pid) (fun w => w.dev=some d)
          (fun _ w => w.dev=some (Config.expiryZeroDevice d pid p)) := by
        simpa only [Config.expiryReadPrefix,requireNotPending,pure_bind] using
          Config.expiryReadPrefix_exact pid d p resident
      have present := clear w a result v b device run
      intro final ending
      rw [present] at ending
      cases ending
      exact expiryZeroDevice_deadHashedReserved retired d pid p resident (pre d device)

theorem handshake_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (handshakeClear pid) := by
  apply join_entry cs loans _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.handshake) pid)
    (CurrentSlots.handshakeClear_preserves pid)
  intro w a result v b pre run
  have tables := (hoare_iff_run_ambient _ _ _).mp (handshakeClear_tables pid)
    w a result v b (fun d hd=>(pre.2 d hd).1) run
  have covered := handshakeClear_hashSlots pid w a result v b
    (fun d hd=>(pre.2 d hd).2.1) run
  have coherent := handshakeClear_owner_coherent pid w a result v b
    (fun d hd=>(pre.2 d hd).2.2.1) run
  have reserved := handshake_retirement [] pid w a result v b
    (fun d hd=>(pre.2 d hd).2.2.2) run
  exact fun d hd=>⟨tables d hd,covered d hd,coherent d hd,reserved d hd⟩

theorem keys_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (keypairsClear pid) := by
  apply join_entry cs loans _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.join)
      (HolderDeviceStop.keys pid)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.base_frame)
        (BaseCoherence.keypairsClear_view pid))
      (ConfiguredRemoval.frame (ConfiguredMaintenance.keypairsClear_view pid)))
    (CurrentSlots.keypairsClear_preserves pid)
  intro w a result v b pre run
  have tables := (hoare_iff_run_ambient _ _ _).mp (keypairsClear_tables pid)
    w a result v b (fun d hd=>(pre.2 d hd).1) run
  have safe := keypairsClear_hashSlots_detached pid w a result v b
    ⟨fun d hd=>(pre.2 d hd).2.1,fun d hd=>(pre.2 d hd).2.2.1⟩ run
  have reserved := keypairsClear_retirement [] pid w a result v b
    (fun d hd=>(pre.2 d hd).2.2.2) run
  exact fun d hd=>⟨tables d hd,safe.1 d hd,safe.2.1 d hd,reserved d hd⟩

theorem purge_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (purgeStagedPackets pid) := by
  apply join_entry cs loans _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.join)
      (HolderTimers.purge_boundary pid)
      ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.base_frame)
        (BaseCoherence.purgeStaged_view pid))
      (ConfiguredRemoval.frame
        ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDevice.«0».Leanux.Proofs.WG.CurrentLifecycle.purgeStaged_view) pid)))
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotTimers.«0».Leanux.Proofs.WG.CurrentSlots.Timer.purge) pid)
  intro w a result v b pre run
  exact (TimerCore.purge pid w a result v b pre run).2

theorem reset_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (resetLastSentHandshake pid) := by
  apply join_entry cs loans _
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.reset) pid)
    (CurrentSlots.fields_preserves (project := id) (CurrentSlots.resetLastSentHandshake_fields pid))
  intro w a result v b pre run
  exact (hoare_iff_run_ambient _ _ _).mp (frame_core (reset_fields pid))
    w a result v b pre.2 run

theorem running_entry (cs : Ledger) (loans : Reservations) (running : Bool) :
    Preserves (Entry cs loans) (modifyDev fun d => {d with running:=running}) := by
  apply join_entry cs loans _
  · repeat' device_entry_step
  · repeat' slot_remove_step
  · intro w a result v b pre run
    exact (hoare_iff_run_ambient _ _ _).mp
      (frame_core (modifyDev_fields (fun d => {d with running:=running}) (fun _ => rfl)))
        w a result v b pre.2 run

theorem queueReset_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans) (modifyDev fun d => {d with handshakeQueueLen:=0}) := by
  apply join_entry cs loans _
  · repeat' device_entry_step
  · repeat' slot_remove_step
  · intro w a result v b pre run
    exact (hoare_iff_run_ambient _ _ _).mp
      (frame_core (modifyDev_fields (fun d => {d with handshakeQueueLen:=0}) (fun _ => rfl)))
        w a result v b pre.2 run

end Leanux.Proofs.WG.Index.LifecycleIndex
