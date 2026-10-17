import Leanux.Proofs.WG.Progress.CookieRingModel
import Leanux.Proofs.WG.Index.LookupSource
import Leanux.Proofs.WG.Campaign2.Bridge
import Leanux.WG.Receive

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Proofs.WG.Index

/-- Actual successful cookie-miss receive step, with no ring-coherence premise.
The observed consume-result states exactly which slot was polled. -/
theorem receiveStep_cookieMiss_ring (g : WGWorld) (ambient : Ambient) (d : Device)
    (msg : List UInt8) (src : SkbSource) (ring : PtrRing (List UInt8 × SkbSource))
    (device : g.dev = some d) (queue : d.handshakeQueue.consume = (some (msg, src), ring))
    (table : d.indexTable = []) (cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE) :
    ((receiveStep.run g).run ambient) = .ok ((true,
      {g with dev := some {d with handshakeQueue := ring, handshakeQueueLen := d.handshakeQueueLen - 1}}),
      {ambient with steps := cookiePacketSteps ambient.netRxSection ambient.steps}) := by
  simp [receiveStep, receiveHandshakePacket, cookieMessageConsume,
    indexLookup_source, lookupFinish, indexBucket, getDev, modifyDev,
    branch, AmbientM.branch, device, queue, table, cookie, cookiePacketSteps]
  rfl

/-- Project the actual product execution, retaining all eight original fixture
observations. The hidden suffix is the actual unchanged suffix, not a default. -/
theorem receiveStep_cookieMiss_ring_snapshot (w : World) (d : Device)
    (msg : List UInt8) (src : SkbSource) (records : List HiddenRecord)
    (device : w.wg.dev = some d)
    (queue : d.handshakeQueue.consume.1 = some (msg, src))
    (table : d.indexTable = []) (cookie : messageType msg = MESSAGE_HANDSHAKE_COOKIE)
    (present : w.ambient.hidden = some records) :
    Campaign2.Product.observeResult ((liftWG receiveStep).run w) =
      .ok (true, cookieRingPacketSnapshot d (Campaign2.Product.snapshot w) records) := by
  have step := receiveStep_cookieMiss_ring w.wg w.ambient d msg src d.handshakeQueue.consume.2
    device (Prod.ext queue rfl) table cookie
  change Campaign2.Product.observeResult
    (((receiveStep.run w.wg).run w.ambient) >>= _) = _
  rw [step]
  simp [Campaign2.Product.observeResult, Campaign2.Product.snapshot, Campaign2.snapshot,
    Campaign2.core, cookieRingPacketSnapshot, cookieRingTailDevice, present]
  rfl


end Leanux.Proofs.WG.Progress
