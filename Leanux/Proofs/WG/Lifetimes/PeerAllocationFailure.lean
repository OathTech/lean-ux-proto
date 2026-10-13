import Leanux.Proofs.WG.Lifetimes.PeerAllocation

/-! The whole focused creation call retains allocation and initialization
write when its first cache-clock read fails. The prelude hypotheses execute
consecutive original operations, rather than assuming an observed prefix. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

/-- This conditional source-level equation needs no AllocationInv. In
particular, it reproduces the original occupied-slot overwrite behavior on
malformed Worlds; the preservation theorem separately excludes that input. -/
theorem peerCreateMixed_cache_clock_failure (key : Key) (psk : Option Key)
    (w guarded allocated reserved entry : World) (d : Device)
    (h : List LifetimeEvent) (e : Stop)
    (hdev : (getDev).run w = .ok (d, w))
    (hfull : (branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE)
      d.numPeers MAX_PEERS_PER_DEVICE).run w = .ok (false, guarded))
    (halloc : (hiddenAlloc .kmemCacheZallocPeer).run guarded = .ok (true, allocated))
    (hmem : (branch .peerCreateNoMem false).run allocated = .ok (false, reserved))
    (hcache : (branch .peerCreateDstCacheFail false).run reserved = .ok (false, entry))
    (ha : entry.armRecords = true) (hc : entry.dstCacheRecords = true)
    (hclock : (hiddenJiffies .dstCacheResetTs).run
      (Peers.creationCoreWorld entry d.nextPeer key) = .error e) :
    runPrefix (peerCreateMixed key psk) w h =
      (.error e, h ++ [.peer (.allocate d.nextPeer (entry.k.peerCounter + 1)),
        .peer (.write d.nextPeer (entry.k.peerCounter + 1))]) := by
  have hd : w.k.wg = some d := by
    cases hd : w.k.wg with
    | none => simp [getDev, getK, hd, invariant] at hdev
    | some old =>
      have same : old = d := by simpa [getDev, getK, hd] using hdev
      exact congrArg some same
  have hg := KernelFrames.branchCmp_sameWGKernel .peerCreateMaxPeers
    (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE w false guarded hfull
  have hgwg : guarded.k.wg = w.k.wg := congrArg (fun v => v.wg) hg
  have hga := hiddenAlloc_sameKernel .kmemCacheZallocPeer guarded true allocated halloc
  have ham := sameKernel_branch .peerCreateNoMem false allocated false reserved hmem
  have hmc := sameKernel_branch .peerCreateDstCacheFail false reserved false entry hcache
  have present : entry.k.wg.isSome = true := by rw [hmc, ham, hga, hgwg, hd]; rfl
  have fail := Peers.dstCacheResetPrefix_hidden_failure d.nextPeer
    (Peers.creationCoreWorld entry d.nextPeer key)
    ((h.filterMap LifetimeEvent.peer?) ++ [.allocate d.nextPeer (entry.k.peerCounter + 1),
      .write d.nextPeer (entry.k.peerCounter + 1)]) e ha hc hclock
  have localRun : runPrefix (Peers.peerCreatePrefix key psk) w (h.filterMap LifetimeEvent.peer?) =
      (.error e, h.filterMap LifetimeEvent.peer? ++
        [.allocate d.nextPeer (entry.k.peerCounter + 1), .write d.nextPeer (entry.k.peerCounter + 1)]) := by
    simp only [Peers.peerCreatePrefix, runPrefix_bind, runPrefix_lift, hdev, hfull,
      Bool.false_eq_true, ↓reduceIte, halloc, Bool.not_true, hmem, hcache,
      Peers.peerCreateCorePrefix_run, Peers.peerCreateCore_run, present, fail]
  simpa only [peerCreateMixed, peerFocus, List.map_cons, List.map_nil] using
    focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer? (Peers.peerCreatePrefix key psk)
      w h (.error e) _ localRun

end Leanux.Proofs.WG.Lifetimes
