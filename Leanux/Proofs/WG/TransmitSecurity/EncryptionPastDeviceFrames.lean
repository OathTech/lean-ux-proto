import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastRemoval
import Leanux.Proofs.WG.Queues.TxLiveDevice

/-! Device-control masks retain historical packet identity. Destruction removes
the device without resetting its allocation cursor; creation uses the next epoch. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.DeviceFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition
set_option maxHeartbeats 600000

private def fromStore (s : WGStoreView) : View :=
  ⟨s.netIfindexNext,s.dev.map fun d => ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩⟩

theorem socket {action : WG.M α} (same : SameSocket action) : Preserves (Ready past active) action :=
  ready_frame (LiveFrontier.socket_frame same)
    (same.of_factor (fun s : WGOwnedView => fromStore s.toWGStoreView) view
      (fun w => by simp only [fromStore,view,socketView,socketDevice,wgOwnedView,wgStoreView,
        Option.map_map,Function.comp_def]))

theorem limiter {action : WG.M α} (same : SameRatelimiter action) :
    Preserves (Ready past active) action := by
  apply ready_frame
  · exact LiveFrontier.fields_ready (same.of_factor
      (fun s : WGStoreView => s.dev.map fun d => (d.nextSkb,d.encryptQueue)) _ (fun _ => rfl))
  · exact same.of_factor fromStore view (fun _ => rfl)

theorem absent (before : Ready past active w) : Ready past active {w with dev := none} := by
  refine ⟨LiveFrontier.absent _ rfl,before.2.1,?_⟩
  intro label member
  exact (before.2.2 label member).no_device (t := view {w with dev := none})
    (Nat.le_refl _) rfl

theorem create : Preserves (Ready past active) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  refine ⟨(hoare_iff_run_ambient _ _ _).mp LiveFrontier.device_create w a result v b before.1 run,?_⟩
  have endpoint := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w))
    w a result v b rfl run
  rcases endpoint with same | ⟨_,fresh⟩
  · have viewSame : view v = view w := by
      simpa only [fromStore,view,linkView,linkStore,linkDevice,wgStoreView,
        Option.map_map,Function.comp_def] using congrArg fromStore same
    exact viewSame ▸ before.2
  · have next : v.netIfindexNext = w.netIfindexNext + 1 :=
      congrArg WGStoreView.netIfindexNext fresh
    have epoch : ∀ d, (view v).device = some d → d.epoch = w.netIfindexNext := by
      intro d found
      have field := congrArg (fun s : WGStoreView => s.dev.map Device.ifindex) fresh
      have mapped : (view v).device.map DeviceView.epoch = some w.netIfindexNext := by
        simpa only [view,linkView,linkStore,linkDevice,wgStoreView,registeredLink,setupLink,
          Option.map_map,Option.map_some,Function.comp_def] using field
      simpa only [found,Option.map_some,Option.some.injEq] using mapped
    refine ⟨before.2.1,?_⟩
    intro label member
    apply (before.2.2 label member).new_device
    · change w.netIfindexNext < v.netIfindexNext
      rw [next]; exact Nat.lt_succ_self _
    · exact epoch

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.DeviceFrames
