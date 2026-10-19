import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpErasure

/-! Native erasure of the original outer dump syscall paths, including Stop. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged Configuration
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem dumpDispatchWith_erases
    (device : DeviceRef → PrefixM E (Except Int Lean.Json))
    (start : Nat → DeviceRef → PrefixM E Unit)
    (receive : Nat → PrefixM E (Option (List NlMessage)))
    (hd : ∀ ref, ErasesPrefix (device ref) (liftWG (wgGetDevice ref)))
    (hs : ∀ fd ref, ErasesPrefix (start fd ref) (liftWG (netlinkDumpStart fd ref)))
    (hr : ∀ fd, ErasesPrefix (receive fd) (liftWG (netlinkRecvmsg fd))) (call : Syscall) :
    ErasesPrefix (dumpDispatchWith liftPrefix device start receive call) (Leanux.dispatch call) := by
  rw [←dumpDispatch_native call]
  cases call <;> simp only [dumpDispatchWith, ←socketCallOn_factor, ←netlinkRequest_factor]
  all_goals repeat' first
    | with_reducible exact hd _
    | with_reducible exact hs _ _
    | with_reducible exact hr _
    | with_reducible apply netlinkRequestWith_erases
    | with_reducible apply socketCallOnWith_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | split
    | contradiction
    | (intro x; try dsimp only)

theorem dumpDispatch_erases {o : Ops (WGPrefix E)} (h : Ops.Erases o) (call : Syscall) :
    ErasesPrefix (dumpDispatch o call) (Leanux.dispatch call) := by
  apply dumpDispatchWith_erases
  · intro ref
    apply liftWGObserver_erases
    simpa only [dumpDevice_native] using dumpDevice_erases h ref
  · intro fd ref
    apply liftWGObserver_erases
    simpa only [dumpStart_native] using dumpStart_erases h fd ref
  · intro fd
    apply liftWGObserver_erases
    simpa only [dumpReceive_native] using dumpReceive_erases h fd

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
