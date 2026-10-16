import Leanux.Proofs.WG.Lifetimes.AllocationFrames

/-! The actual native WG runner fixtures satisfy the allocation invariant
with an empty history. The entry premise observes only the original seven
WG store fields, leaving all other native state unrestricted. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem allocation_initial (net bare : Bool) (w : WGWorld)
    (hw : wgStoreView w = wgStoreView (Runner.initialWG net bare)) :
    AllocationInv [] w := by
  have hp : w.peerCounter = 0 := by
    simpa [wgStoreView, Runner.initialWG] using congrArg WGStoreView.peerCounter hw
  have hk : w.keypairCounter = 0 := by
    simpa [wgStoreView, Runner.initialWG] using congrArg WGStoreView.keypairCounter hw
  have hd : w.dev = (if net && !bare then some {ifindex := 3, ifname := "wg0"} else none) := by
    simpa [wgStoreView, Runner.initialWG] using congrArg WGStoreView.dev hw
  have hn : w.netIfindexNext = (if net && !bare then 4 else 3) := by
    simpa [wgStoreView, Runner.initialWG] using congrArg WGStoreView.netIfindexNext hw
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

end Leanux.Proofs.WG.Lifetimes
