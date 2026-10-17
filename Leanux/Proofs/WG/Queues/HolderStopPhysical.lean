import Leanux.Proofs.WG.Queues.HolderDeviceStop
import Leanux.Proofs.WG.Queues.HolderTimerPhysical
import Leanux.Proofs.WG.Queues.HolderDeviceCreate

/-! Native shutdown keeps the actual physical receive ring, even while real
flushes pay holder occurrences. An absent device carries no invented ring. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderStopPhysical
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders RxRing

theorem drain_cell (upTo : Option PeerId) : SameView nativeCell (drainHandshakeSendWq upTo) := by
  ring_cell_source [drainHandshakeSendWq,peekUnit,resolveUnit] using
    [HolderDeferred.flushedSend_cell,HolderTimerPhysical.flushedClear_cell]

theorem timers_cell (pid : PeerId) : SameView nativeCell (timersStop pid) := by
  ring_cell_source [timersStop] using [delTimer_cell,drain_cell]

theorem handshake_cell (pid : PeerId) : SameView nativeCell (handshakeClear pid) := by
  ring_cell_source [handshakeClear,indexRemove] using [handshakeZero_cell]

theorem keys_cell (pid : PeerId) : SameView nativeCell (keypairsClear pid) := by
  ring_cell_source [keypairsClear,_private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_cell]

theorem reset_cell (pid : PeerId) : SameView nativeCell (resetLastSentHandshake pid) := by
  ring_cell_source [resetLastSentHandshake] using []

theorem socket_cell (new4 new6 : Option Nat) : SameView nativeCell (socketReinit new4 new6) :=
  (socketReinit_sameSocket new4 new6).of_factor
    (fun s : WGOwnedView => s.dev.map fun d => (d.ifindex,d.decryptQueue)) nativeCell
    (fun _ => by simp only [socketView,wgOwnedView,wgStoreView,socketDevice,nativeCell,Option.map_map,Function.comp_def])

theorem purge_cell (pid : PeerId) : SameView nativeCell (purgeStagedPackets pid) := by
  ring_cell_source [purgeStagedPackets] using []

theorem stop_cell : SameView nativeCell wgStop := by
  ring_cell_source [wgStop,requireNotPending] using
    [purge_cell,timers_cell,handshake_cell,keys_cell,reset_cell,socket_cell]

theorem down_cell : SameView nativeCell wgDown := by
  ring_cell_source [wgDown] using [stop_cell]

/-- Exact cell equality transports whichever real physical alternative held. -/
theorem optional_cell (hi : HolderDeviceCreate.OptionalPhysical w)
    (same : nativeCell v=nativeCell w) : HolderDeviceCreate.OptionalPhysical v := by
  rcases hi with absent | ⟨epoch,n,h,ring,refines,cell⟩
  · left
    cases dev:v.dev with
    | none => rfl
    | some d => simp [nativeCell,absent,dev] at same
  · exact Or.inr ⟨epoch,n,h,ring,refines,same.trans cell⟩

private theorem joined (action : WG.M α) (account : Preserves (Boundary cs loans) action)
    (physical : SameView nativeCell action) :
    Preserves (fun w => Boundary cs loans w ∧ HolderDeviceCreate.OptionalPhysical w) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp account w a x v b hi.1 run,
    optional_cell hi.2 ((ProjectedAction.iff_run_ambient _ _ _).mp physical w a x v b run)⟩

theorem stop : Preserves (fun w => Boundary cs loans w ∧ HolderDeviceCreate.OptionalPhysical w) wgStop :=
  joined _ HolderDeviceStop.stop stop_cell

theorem down : Preserves (fun w => Boundary cs loans w ∧ HolderDeviceCreate.OptionalPhysical w) wgDown :=
  joined _ HolderDeviceStop.down down_cell

end Leanux.Proofs.WG.Queues.RxCredits.HolderStopPhysical
