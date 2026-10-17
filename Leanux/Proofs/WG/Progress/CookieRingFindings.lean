import Leanux.Proofs.WG.Progress.CookieRingSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

/-- A concrete malformed cursor witness. No reachability claim is made. -/
def cookieBadTailRing (msg : List UInt8) (src : SkbSource) : PtrRing (List UInt8 × SkbSource) :=
  {size := 1, batch := 16, producer := 0, consumerHead := 0, consumerTail := 2,
    slots := #[some (msg, src)]}

theorem cookieBadTail_count_not_drained (msg : List UInt8) (src : SkbSource) :
    (cookieBadTailRing msg src).count = 1 ∧
      (cookieRingAfter (cookieBadTailRing msg src).count (cookieBadTailRing msg src)).peek = some (msg, src) := by
  simp [cookieBadTailRing, cookieRingAfter, PtrRing.count, PtrRing.consume,
    PtrRing.peek, PtrRing.discardOne, PtrRing.discardOne.clear]

/-- The false drain prediction is visible in an actual native receive run,
not merely in the pure ring transform. All unrelated WG/Ambient data are arbitrary. -/
theorem receiveStep_cookieBadTail_not_drained (g : WGWorld) (ambient : Ambient) (d : Device)
    (msg : List UInt8) (src : SkbSource) (device : g.dev = some d)
    (queue : d.handshakeQueue = cookieBadTailRing msg src) (table : d.indexTable = [])
    (cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE) :
    d.handshakeQueue.count = 1 ∧
    ((receiveStep.run g).run ambient) = .ok ((true, {g with dev := some (cookieRingTailDevice d)}),
      {ambient with steps := cookiePacketSteps ambient.netRxSection ambient.steps}) ∧
    (cookieRingTailDevice d).handshakeQueue.peek = some (msg, src) := by
  have consumed : d.handshakeQueue.consume.1 = some (msg, src) := by
    simp [queue, cookieBadTailRing, PtrRing.consume, PtrRing.peek]
  have step := receiveStep_cookieMiss_ring g ambient d msg src d.handshakeQueue.consume.2 device
    (Prod.ext consumed rfl) table cookie
  refine ⟨?_, step, ?_⟩
  · simp [queue, cookieBadTailRing, PtrRing.count, PtrRing.peek]
  · simpa [cookieRingTailDevice, queue, cookieRingAfter, (cookieBadTail_count_not_drained msg src).1]
      using (cookieBadTail_count_not_drained msg src).2

/-- Even coherent initialized rings retain physical metadata after a logical
drain; reconstructing an empty container loses those fields. -/
theorem cookieInitialized_retains_slot (msg : List UInt8) (src : SkbSource) :
    let ring := (PtrRing.init 32).produce (msg, src)
    ring.count = 1 ∧ ring.consume.2.empty = true ∧
      ring.consume.2.slots[0]? = some (some (msg, src)) ∧
      ring.consume.2.consumerHead = 1 ∧ ring.consume.2.consumerTail = 0 := by
  simp [PtrRing.init, PtrRing.produce, PtrRing.count, PtrRing.peek, PtrRing.consume,
    PtrRing.empty, PtrRing.discardOne, SMP_CACHE_BYTES]

end Leanux.Proofs.WG.Progress
