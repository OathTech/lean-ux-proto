import Leanux.Proofs.WG.Lifetimes.AllocationFrames

/-! The ordinary runner fixtures satisfy the allocation invariant with an
empty history. Seccomp prefill preserves it through the shared WG projection. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem AllocationInv.wgKernel (hi : AllocationInv h w) (he : wgKernelView v = wgKernelView w) :
    AllocationInv h v := by
  have hw : v.k.wg = w.k.wg := congrArg WGKernelView.wg he
  have hp : v.k.peerCounter = w.k.peerCounter := congrArg WGKernelView.peerCounter he
  have hk : v.k.keypairCounter = w.k.keypairCounter := congrArg WGKernelView.keypairCounter he
  have hn : v.k.netIfindexNext = w.k.netIfindexNext := congrArg WGKernelView.netIfindexNext he
  apply hi.congr
  · unfold identityView Peers.snapshot keypairResidents packetResidents
    rw [hw, hp]
  · unfold allocationMetadata
    rw [hw, hk, hn]

theorem allocation_initial (rlimit : Nat) (net bare foreign stepped seccompChild : Bool) (w : World)
    (hw : w.k = Runner.initialKernel rlimit net bare foreign stepped seccompChild) :
    AllocationInv [] w := by
  have hp : w.k.peerCounter = 0 := by simp [hw, Runner.initialKernel]
  have hk : w.k.keypairCounter = 0 := by simp [hw, Runner.initialKernel]
  have hd : w.k.wg = (if net && !bare then some {ifindex := 3, ifname := "wg0"} else none) := by
    simp [hw, Runner.initialKernel]
  have hn : w.k.netIfindexNext = (if net && !bare then 4 else 3) := by
    simp [hw, Runner.initialKernel]
  by_cases active : (net && !bare) = true
  all_goals simp only [active, Bool.false_eq_true, ↓reduceIte] at hd hn
  all_goals refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩)
    | (refine ⟨?_, ?_, ?_⟩)
    | skip
  all_goals simp [Peers.AccessInv, AccessEvent.Safe, AccessEvent.Released,
    ResidentSafe, ResidentUnique, Unique, Absent, Bounded, identityView, keyStore,
    Peers.snapshot, keypairResidents, packetResidents, Packets.deviceStore,
    hd, hn, hp, hk]
  all_goals intro i; cases i <;> simp

/-- Successful prefill changes no field used by the lifetime invariant. -/
theorem allocation_prefill (n : Nat) (w : World) (k : Kernel)
    (hi : AllocationInv h w) (hr : Seccomp.Prefill.apply n w.k = .ok k) :
    AllocationInv h {w with k} :=
  hi.wgKernel (prefill_wgKernel n w.k k hr)

end Leanux.Proofs.WG.Lifetimes
