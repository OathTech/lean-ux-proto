import Leanux.Proofs.WG.Progress.CookieRingSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

/-- Incoherent physical occupancy: the logical view contains only the first
slot, but the next physical slot is also occupied. No reachability is claimed. -/
def cookieItemsGapRing (src : SkbSource) : PtrRing (List UInt8 × SkbSource) :=
  {size := 2, batch := 16, producer := 1, consumerHead := 0, consumerTail := 0,
    slots := #[some ([3, 0, 0, 0], src), some ([0, 0, 0, 0], src)]}

/-- Initial logical membership classifies every item as a cookie, while the
first consume exposes a non-cookie packet absent from that initial view. -/
theorem cookieItemsGap_not_closed (src : SkbSource) :
    (cookieItemsGapRing src).count = 1 ∧
    (cookieItemsGapRing src).items = [([3, 0, 0, 0], src)] ∧
    (∀ msg source, (msg, source) ∈ (cookieItemsGapRing src).items →
      messageType msg = MESSAGE_HANDSHAKE_COOKIE) ∧
    (cookieItemsGapRing src).consume.2.peek = some ([0, 0, 0, 0], src) ∧
    messageType [0, 0, 0, 0] ≠ MESSAGE_HANDSHAKE_COOKIE := by
  have items : (cookieItemsGapRing src).items = [([3, 0, 0, 0], src)] := by
    simp [cookieItemsGapRing, PtrRing.items, PtrRing.count]
  refine ⟨by simp [cookieItemsGapRing, PtrRing.count], items, ?_, rfl, by decide⟩
  intro msg source member
  rw [items] at member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  obtain ⟨rfl, rfl⟩ := member
  rfl

/-- The logical-membership gap is exposed by the actual first receive step,
with arbitrary unrelated WG/Ambient data and the empty index-table domain. -/
theorem receiveStep_cookieItemsGap_exposes_nonCookie
    (g : WGWorld) (ambient : Ambient) (d : Device) (src : SkbSource)
    (device : g.dev = some d) (queue : d.handshakeQueue = cookieItemsGapRing src)
    (table : d.indexTable = []) :
    ((receiveStep.run g).run ambient) =
      .ok ((true, {g with dev := some (cookieRingTailDevice d)}),
        {ambient with steps := cookiePacketSteps ambient.netRxSection ambient.steps}) ∧
    (cookieRingTailDevice d).handshakeQueue.peek = some ([0, 0, 0, 0], src) ∧
    ([0, 0, 0, 0], src) ∉ d.handshakeQueue.items := by
  have consumed : d.handshakeQueue.consume.1 = some ([3, 0, 0, 0], src) := by
    rw [queue]
    rfl
  refine ⟨receiveStep_cookieMiss_ring g ambient d [3, 0, 0, 0] src
    d.handshakeQueue.consume.2 device (Prod.ext consumed rfl) table rfl, ?_, ?_⟩
  · change d.handshakeQueue.consume.2.peek = _
    rw [queue]
    rfl
  · rw [queue, (cookieItemsGap_not_closed src).2.1]
    simp

end Leanux.Proofs.WG.Progress
