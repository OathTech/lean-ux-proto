import Leanux.Proofs.WG.Roaming.CookieEndpointFrames
import Leanux.Proofs.WG.Roaming.CookieEndpointSource
import Leanux.Proofs.WG.Roaming.View

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- A type-3 message preserves every remote endpoint on normal completion
of the original whole receiver. All actual initial Product states remain
quantified; no valid-cookie, source-family, clock or reference premise is added. -/
theorem receiveHandshakePacket_cookie_endpoints (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot)
    (kind : messageType msg = MESSAGE_HANDSHAKE_COOKIE) :
    Campaign2.Product.Ensures (liftWG (receiveHandshakePacket msg src)) (fun s => s = entry)
      (fun _ final => ∀ pid, remoteAt final.toSnapshot pid = remoteAt entry.toSnapshot pid) := by
  intro initial result final pre execution
  subst entry
  change (((receiveHandshakePacket msg src).run initial.wg).run initial.ambient >>= fun ((value,current),inputs) =>
    Except.ok (value,{initial with wg := current,ambient := inputs})) = _ at execution
  cases native : ((receiveHandshakePacket msg src).run initial.wg).run initial.ambient with
  | error stop => rw [native] at execution; cases execution
  | ok pair =>
    obtain ⟨⟨value,current⟩,inputs⟩ := pair
    cases value
    rw [native] at execution
    cases execution
    have framed : Ensures (receiveHandshakePacket msg src)
        (fun g => responseEndpointMap g.dev = responseEndpointMap initial.wg.dev)
        (fun _ g => responseEndpointMap g.dev = responseEndpointMap initial.wg.dev) := by
      rw [receiveHandshakePacket_cookie_source msg src kind]
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.branch .hsCookie true)
          (fun g : WGWorld => responseEndpointMap g.dev = responseEndpointMap initial.wg.dev))) ?_
      intro _
      exact cookieMessageConsume_endpoints msg initial.wg.dev
    have same := framed initial.wg initial.ambient () current inputs rfl native
    intro pid
    have point := congrFun same pid
    have remote := congrArg (fun endpoint : Option (Option Endpoint) => endpoint.join.map destination) point
    have joinMap (p : Option Peer) : (p.map Peer.endpoint).join = p.bind Peer.endpoint := by
      cases p <;> rfl
    simpa only [responseEndpointMap,joinMap,remoteAt,Campaign2.Snapshot.peerAt,
      Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core] using remote

end Leanux.Proofs.WG.Roaming
