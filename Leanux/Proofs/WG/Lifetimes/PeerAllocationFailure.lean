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
    (w guarded allocated reserved entry : WGWorld) (d : Device)
    (ambient guardedAmbient allocatedAmbient reservedAmbient entryAmbient : Ambient)
    (h : List LifetimeEvent) (e : Stop)
    (hdev : ((getDev).run w).run ambient = .ok ((d, w), ambient))
    (hfull : ((branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE)
      d.numPeers MAX_PEERS_PER_DEVICE : WG.M Bool).run w).run ambient =
        .ok ((false, guarded), guardedAmbient))
    (halloc : ((hiddenAlloc .kmemCacheZallocPeer : WG.M Bool).run guarded).run guardedAmbient =
      .ok ((true, allocated), allocatedAmbient))
    (hmem : ((branch .peerCreateNoMem false : WG.M Bool).run allocated).run allocatedAmbient =
      .ok ((false, reserved), reservedAmbient))
    (hcache : ((branch .peerCreateDstCacheFail false : WG.M Bool).run reserved).run reservedAmbient =
      .ok ((false, entry), entryAmbient))
    (ha : entryAmbient.armRecords = true) (hc : entry.dstCacheRecords = true)
    (hclock : ((hiddenJiffies .dstCacheResetTs : WG.M UInt64).run
      (Peers.creationCoreWorld entry d.nextPeer key)).run entryAmbient = .error e) :
    runStatePrefix (peerCreateMixed key psk) w ambient h =
      (.error e, h ++ [.peer (.allocate d.nextPeer (entry.peerCounter + 1)),
        .peer (.write d.nextPeer (entry.peerCounter + 1))]) := by
  have hd : w.dev = some d := by
    cases hd : w.dev with
    | none =>
      have hstop : ((Leanux.invariant "no WireGuard device in this trace's fixture" :
          WG.M Device).run w).run ambient =
          .error (.invariant "no WireGuard device in this trace's fixture") := by rfl'
      simp only [getDev, StateT.run_bind, StateT.run_get, pure_bind, hd, hstop] at hdev
      contradiction
    | some old =>
      have same : old = d := by simpa [getDev, hd] using hdev
      exact congrArg some same
  have preserved {α : Type} (a : AmbientM α) {s t : WGWorld}
      {b b' : Ambient} {x : α}
      (hr : ((StateT.lift a : WG.M α).run s).run b = .ok ((x, t), b')) : t = s :=
    (hoare_iff_run_ambient _ _ _).mp (hoare_liftAmbient a (fun v => v = s))
      s b x t b' rfl hr
  have hg : guarded = w := preserved (AmbientM.branchCmp .peerCreateMaxPeers
    (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE) hfull
  have hga : allocated = guarded := preserved (AmbientM.hiddenAlloc .kmemCacheZallocPeer) halloc
  have ham : reserved = allocated := preserved (AmbientM.branch .peerCreateNoMem false) hmem
  have hmc : entry = reserved := preserved (AmbientM.branch .peerCreateDstCacheFail false) hcache
  have present : entry.dev.isSome = true := by rw [hmc, ham, hga, hg, hd]; rfl
  have fail := Peers.dstCacheResetPrefix_hidden_failure d.nextPeer
    (Peers.creationCoreWorld entry d.nextPeer key) entryAmbient
    ((h.filterMap LifetimeEvent.peer?) ++ [.allocate d.nextPeer (entry.peerCounter + 1),
      .write d.nextPeer (entry.peerCounter + 1)]) e ha hc hclock
  have localRun : runStatePrefix (Peers.peerCreatePrefix key psk) w ambient (h.filterMap LifetimeEvent.peer?) =
      (.error e, h.filterMap LifetimeEvent.peer? ++
        [.allocate d.nextPeer (entry.peerCounter + 1), .write d.nextPeer (entry.peerCounter + 1)]) := by
    simp only [Peers.peerCreatePrefix, liftWGPrefix, runStatePrefix_bind, runStatePrefix_lift, hdev, hfull,
      Bool.false_eq_true, ↓reduceIte, halloc, Bool.not_true, hmem, hcache,
      Peers.peerCreateCorePrefix_run, Peers.peerCreateCore_run, present, fail]
  change runPrefix (focusPrefix LifetimeEvent.peer LifetimeEvent.peer?
    (Peers.peerCreatePrefix key psk w)) ambient h = _
  change runPrefix (Peers.peerCreatePrefix key psk w) ambient _ = _ at localRun
  simpa only [List.map_cons, List.map_nil] using
    focusPrefix_suffix LifetimeEvent.peer LifetimeEvent.peer? (Peers.peerCreatePrefix key psk w)
      ambient h (.error e) _ localRun

end Leanux.Proofs.WG.Lifetimes
