import Leanux.Proofs.WG.Noise.PendingTicketFlushFrames
import Leanux.Proofs.WG.Noise.PendingTicketDeviceFrames
import Leanux.Proofs.WG.Noise.PendingReceptionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do Queues

theorem frame_socket {α : Type} (action : WG.M α) (frame : SameSocket action) :
    SameView view action := by
  apply frame.of_factor (fun s : WGOwnedView => storeView s.toWGStoreView) view
  intro w
  simp [storeView,socketView,socketDevice,wgOwnedView,wgStoreView,view,pending,
    Option.bind_map,Function.comp_def]

theorem purgeStagedPackets_frame (pid : PeerId) : SameView view (purgeStagedPackets pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v after run
  cases device : w.dev with
  | none =>
    simp [purgeStagedPackets,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases peer : d.peers[pid]? with
    | none =>
      simp [purgeStagedPackets,getPeer,getDev,device,peer,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      simp [purgeStagedPackets,getPeer,getDev,device,peer,modifyDev,setPeer] at run
      obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
      apply Store.ext
      · rfl
      · funext tracked
        by_cases same : pid = tracked
        · subst tracked
          simp [view,pending,device,peer]
        · simp [view,pending,device,Std.TreeMap.getElem?_insert,same]

macro "pending_retention_step " entry:term : tactic => `(tactic| first
  | (rx_retention_head ForIn.forIn
     apply list_view_spec view (Retained $entry)
     intro x acc
     change Preserves (fun w => Retained $entry (view w)) _)
  | (rx_retention_head getDev; exact (frame_store getDev_sameWGStore).wp (Retained $entry))
  | (rx_retention_head getPeer
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w ambient p v after hi run
     exact (getPeer_normal _ w v p ambient after run).1 ▸ hi)
  | (rx_retention_head modifyDev
     apply SameView.wp (modifyDev_frame _ ?_ ?_) (Retained $entry)
     all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | rx_retention_step)

/-- Normal stop retains pending tickets through its actual guarded peer
loop, work drains, key clears, empty-ring check and socket shutdown. -/
theorem wgStop_retained : RetainsCall wgStop := by
  apply retains_of_preserves
  intro entry
  refine (ensures_iff wgStop (fun w => Retained entry (view w)) (fun _ w => Retained entry (view w))).mpr ?_
  change Preserves (fun w => Retained entry (view w)) wgStop
  unfold wgStop
  simp (config := {zeta := false}) only [requireNotPending,branch,unsupported]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact (purgeStagedPackets_frame _).wp (Retained entry))
    | (rx_retention_head timersStop; exact (ensures_iff _ _ _).mp (retained_preserves (timersStop_retained _) entry))
    | (rx_retention_head handshakeClear; exact (handshakeClear_frame _).wp (Retained entry))
    | (rx_retention_head keypairsClear; exact (ensures_iff _ _ _).mp (retained_preserves (keypairsClear_retained _) entry))
    | (rx_retention_head resetLastSentHandshake; exact (resetLastSentHandshake_frame _).wp (Retained entry))
    | (rx_retention_head socketReinit; exact (frame_socket _ (socketReinit_sameSocket _ _)).wp (Retained entry))
    | pending_retention_step entry

theorem wgDown_retained : RetainsCall wgDown := by
  unfold wgDown
  exact retains_bind (retained_of_frame
    (modifyDev_frame (fun d => {d with running := false}) (fun _ => rfl) (fun _ => rfl)))
    (fun _ => wgStop_retained)

theorem wgOpen_retained : RetainsCall wgOpen := by
  apply retains_of_preserves
  intro entry
  refine (ensures_iff wgOpen (fun w => Retained entry (view w)) (fun _ w => Retained entry (view w))).mpr ?_
  change Preserves (fun w => Retained entry (view w)) wgOpen
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact (frame_socket _ (socketInit_sameSocket _)).wp (Retained entry))
    | (rx_retention_head sendStagedPackets; exact (ensures_iff _ _ _).mp (retained_preserves (sendStagedPackets_retained _) entry))
    | (rx_retention_head sendKeepalive; exact (ensures_iff _ _ _).mp (retained_preserves (sendKeepalive_retained _) entry))
    | pending_retention_step entry

theorem wgUp_retained : RetainsCall wgUp := by
  apply retains_of_preserves
  intro entry
  refine (ensures_iff wgUp (fun w => Retained entry (view w)) (fun _ w => Retained entry (view w))).mpr ?_
  change Preserves (fun w => Retained entry (view w)) wgUp
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact (ensures_iff _ _ _).mp (retained_preserves wgOpen_retained entry))
    | pending_retention_step entry

end Leanux.Proofs.WG.Noise.PendingTickets

namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do Queues

theorem stop (seen : List Nat) : Preserves (fun w => NativeInv w seen) wgStop :=
  PendingReception.native_preserves _ RxCredits.DeviceAuxEntry.stop_configured
    RxCredits.DeviceAuxEntry.stop_slots PendingTickets.wgStop_retained seen

theorem down (seen : List Nat) : Preserves (fun w => NativeInv w seen) wgDown :=
  PendingReception.native_preserves _ RxCredits.DeviceAuxEntry.down_configured
    RxCredits.DeviceAuxEntry.down_slots PendingTickets.wgDown_retained seen

end Leanux.Proofs.WG.Noise.PendingSession
