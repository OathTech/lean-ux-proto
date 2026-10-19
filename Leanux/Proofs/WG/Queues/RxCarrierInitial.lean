import Leanux.Proofs.WG.Queues.RxIngressStable

/-! The original empty WireGuard fixture establishes the carrier ledger.
Only native device contents are observed; unrelated worlds and Ambient
remain unrestricted. These initial facts alone are not execution closure. -/
namespace Leanux.Proofs.WG.Queues.RxCredits
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes

/-- Empty RX storage and peer queues establish empty inventory and exact
queue multiplicity. No reference-count assumption is needed for zero demand. -/
theorem empty_carriers (w : WGWorld)
    (packets : ∀ (d : Device) (id : SkbId), w.dev = some d → d.rxSkbs[id]? = none)
    (queues : ∀ (d : Device) (pid : PeerId) (p : Peer), w.dev = some d →
      d.peers[pid]? = some p → p.rxQueue.all = [])
    (keys : CurrentsCompatible w) : CarrierState [] [] w := by
  refine ⟨⟨by simp, by simp, ?_⟩, ?_, ?_, ?_, keys⟩
  · intro d id pkt hd hp
    rw [packets d id hd] at hp
    cases hp
  · intro d pid p id hd hp
    simp [queues d pid p hd hp]
  · intro o
    simp [demand, charges]
  · intro d id pkt hd hp
    rw [packets d id hd] at hp
    cases hp

/-- Empty queues and an empty logical decrypt ring establish the stable
boundary, independently of stale physical slots or the ring's size. -/
theorem empty_stable (w : WGWorld)
    (ring : ∀ d, w.dev = some d → d.decryptQueue.items = [])
    (queues : ∀ (d : Device) (pid : PeerId) (p : Peer), w.dev = some d →
      d.peers[pid]? = some p → p.rxQueue.all = []) : StableRx [] w := by
  refine ⟨by simp, ?_, ?_⟩
  · intro d hd
    simp [ring d hd, uncrypted]
  · intro d pid p id hd hp _ head
    simp [queues d pid p hd hp] at head

/-- The original WG fixture has no carriers or reservations for either
network/bare flag, with current-key compatibility derived from empty peers. -/
theorem carrier_initial (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w = wgStoreView (Runner.initialWG net bare)) :
    CarrierState [] [] w := by
  have dev : w.dev = (Runner.initialWG net bare).dev := congrArg WGStoreView.dev same
  apply empty_carriers w
  · intro d id hd
    rw [dev] at hd
    simp only [Runner.initialWG] at hd
    split at hd
    · cases hd
      simp_all
    · cases hd
  · intro d pid p hd hp
    rw [dev] at hd
    simp only [Runner.initialWG] at hd
    split at hd
    · cases hd
      simp_all
    · cases hd
  · intro pid d p kid hd hp _
    rw [dev] at hd
    simp only [Runner.initialWG] at hd
    split at hd
    · cases hd
      simp_all
    · cases hd

private theorem initialRing_items (n : Nat) : (PtrRing.init (α := SkbId) n).items = [] := by
  simpa only [Ring.Journal.run, Ring.Journal.admitted, Ring.Journal.consumed,
    List.filterMap_nil, List.nil_append] using
    (Ring.Journal.conservation_all n ([] : List (Ring.Journal.Command SkbId))).symm

/-- The same native fixture is a stable empty receive boundary. -/
theorem stable_initial (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w = wgStoreView (Runner.initialWG net bare)) :
    StableRx [] w := by
  have dev : w.dev = (Runner.initialWG net bare).dev := congrArg WGStoreView.dev same
  apply empty_stable w
  · intro d hd
    rw [dev] at hd
    simp only [Runner.initialWG] at hd
    split at hd
    · cases hd
      exact initialRing_items MAX_QUEUED_PACKETS
    · cases hd
  · intro d pid p hd hp
    rw [dev] at hd
    simp only [Runner.initialWG] at hd
    split at hd
    · cases hd
      simp_all
    · cases hd

/-- An initialized present device retains the exact physical ring, with an
empty mutation journal. An absent device has no physical RX obligation. -/
theorem ring_initial (net bare : Bool) (w : WGWorld)
    (same : wgStoreView w = wgStoreView (Runner.initialWG net bare)) :
    w.dev = none ∨ NativeRxInv 3 (PtrRing.init MAX_QUEUED_PACKETS) [] w := by
  have dev : w.dev = (Runner.initialWG net bare).dev := congrArg WGStoreView.dev same
  by_cases active : (net && !bare) = true
  · right
    refine ⟨PtrRing.init MAX_QUEUED_PACKETS, ?_, ?_⟩
    · exact ⟨[], rfl⟩
    · simp [RxRing.nativeCell, dev, Runner.initialWG, active]
  · left
    simpa [Runner.initialWG, active] using dev

end Leanux.Proofs.WG.Queues.RxCredits
