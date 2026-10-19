import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpFrames
import Leanux.Proofs.WG.Queues.RoutingDispatchFrame

/-! History frames are separate from the outer dump source. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Configuration
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem dumpDispatchWith_frame (ρ : E → Option F)
    (device : DeviceRef → PrefixM E (Except Int Lean.Json))
    (start : Nat → DeviceRef → PrefixM E Unit)
    (receive : Nat → PrefixM E (Option (List NlMessage)))
    (hd : ∀ ref, HistoryFrame ρ (device ref))
    (hs : ∀ fd ref, HistoryFrame ρ (start fd ref))
    (hr : ∀ fd, HistoryFrame ρ (receive fd)) (call : Syscall) :
    HistoryFrame ρ (dumpDispatchWith liftPrefix device start receive call) := by
  cases call <;> simp only [dumpDispatchWith]
  all_goals repeat' first
    | with_reducible exact hd _
    | with_reducible exact hs _ _
    | with_reducible exact hr _
    | (joint_history_head netlinkRequestWith; apply netlinkRequestWith_frame)
    | (joint_history_head socketCallOnWith; apply socketCallOnWith_frame)
    | joint_history_step

theorem dumpDispatch_frame (ρ : E → Option F)
    {o : Ops (WGPrefix E)} (h : Ops.Frames ρ o) (call : Syscall) :
    HistoryFrame ρ (dumpDispatch o call) :=
  dumpDispatchWith_frame ρ _ _ _
    (fun ref => StateHistoryFrame.liftWGObserver (dumpDevice_frame ρ h ref))
    (fun fd ref => StateHistoryFrame.liftWGObserver (dumpStart_frame ρ h fd ref))
    (fun fd => StateHistoryFrame.liftWGObserver (dumpReceive_frame ρ h fd)) call

/-- Append transport follows the actual callback executions, including Stop. -/
theorem dumpDispatchWith_appends
    (device : DeviceRef → PrefixM E (Except Int Lean.Json))
    (start : Nat → DeviceRef → PrefixM E Unit)
    (receive : Nat → PrefixM E (Option (List NlMessage)))
    (hd : ∀ ref, Appends (device ref))
    (hs : ∀ fd ref, Appends (start fd ref))
    (hr : ∀ fd, Appends (receive fd)) (call : Syscall) :
    Appends (dumpDispatchWith liftPrefix device start receive call) := by
  cases call <;> simp only [dumpDispatchWith]
  all_goals repeat' first
    | with_reducible exact hd _
    | with_reducible exact hs _ _
    | with_reducible exact hr _
    | with_reducible apply netlinkRequestWith_appends
    | with_reducible apply socketCallOnWith_appends
    | with_reducible exact Appends.lift _
    | with_reducible exact Appends.pure _
    | with_reducible apply Appends.bind
    | split
    | contradiction
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
