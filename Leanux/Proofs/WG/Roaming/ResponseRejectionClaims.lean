import Leanux.Proofs.WG.Roaming.ResponseRejectionFrames
import Leanux.Proofs.WG.Roaming.ResponseRejectionSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Both receipts come from the same entry as the original whole receiver.
After MAC admission a missing response cut is the consumer's normal rejection,
so the whole normal return preserves endpoints. No residency, owner coherence,
reference budget, source family, clock or cryptographic readiness is assumed. -/
theorem receiveHandshakePacket_response_rejection (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) :
    Campaign2.Product.Ensures (observedResponseRejection msg src) (fun s => s = entry)
      (fun receipt final => ResponseRejectionObservation entry receipt final) := by
  intro w receipt finish pre execution
  subst entry
  change ((liftWG (receiveHandshakePacket msg src)).run w >>= fun out =>
    Except.ok ((Campaign2.Product.observeResult ((liftWG (rateLimitPrefix msg src)).run w),
      Campaign2.Product.observeResult ((Product.responseCallPrefix msg src).run w)),out.2)) = _ at execution
  cases native : ((receiveHandshakePacket msg src).run w.wg).run w.ambient with
  | error stop =>
    change ((((receiveHandshakePacket msg src).run w.wg).run w.ambient >>= fun ((_,g),a) =>
      Except.ok ((),{w with wg := g, ambient := a})) >>= _) = _ at execution
    rw [native] at execution; cases execution
  | ok pair =>
    obtain ⟨⟨value,current⟩,after⟩ := pair
    cases value
    have lifted : (liftWG (receiveHandshakePacket msg src)).run w =
        .ok ((),{w with wg := current, ambient := after}) := by
      change (((receiveHandshakePacket msg src).run w.wg).run w.ambient >>= _) = _
      rw [native]; rfl
    rw [lifted] at execution
    cases execution
    have callRun := native
    rw [← receiveHandshakePacket_response msg src kind] at callRun
    change (((responseCallPrefix msg src).run w.wg).run w.ambient >>= fun ((cut,g),a) =>
      ((responseCallSuffix msg src cut).run g).run a) = _ at callRun
    cases prefixRun : ((responseCallPrefix msg src).run w.wg).run w.ambient with
    | error stop => rw [prefixRun] at callRun; cases callRun
    | ok pair =>
      obtain ⟨⟨cut,atCut⟩,cutAmbient⟩ := pair
      rw [prefixRun] at callRun
      have macRun := native
      rw [receiveHandshakePacket_rateLimit_factor msg src (by simp [kind, MESSAGE_HANDSHAKE_RESPONSE, MESSAGE_HANDSHAKE_COOKIE])] at macRun
      change (((rateLimitPrefix msg src).run w.wg).run w.ambient >>= fun ((input,g),a) =>
        ((rateLimitSuffix msg src input).run g).run a) = _ at macRun
      cases macPrefix : ((rateLimitPrefix msg src).run w.wg).run w.ambient with
      | error stop => rw [macPrefix] at macRun; cases macRun
      | ok pair =>
        obtain ⟨⟨⟨loaded,mac⟩,atMac⟩,macAmbient⟩ := pair
        have macLift : (liftWG (rateLimitPrefix msg src)).run w =
            .ok ((loaded,mac),{w with wg := atMac,ambient := macAmbient}) := by
          change (((rateLimitPrefix msg src).run w.wg).run w.ambient >>= _) = _
          rw [macPrefix]; rfl
        have cutLift : (Product.responseCallPrefix msg src).run w =
            .ok (cut.map (Product.restoreResponseCallCut (Campaign2.Product.snapshot w).fixture),
              {w with wg := atCut,ambient := cutAmbient}) := by
          dsimp only [Product.responseCallPrefix,Campaign2.Product.read,liftWG,StateT.run,
            StateT.bind,StateT.pure,StateT.map,Bind.bind,Pure.pure,Functor.map,Except.bind,Except.pure]
          simp only [StateT.run] at prefixRun
          rw [prefixRun]
        refine ⟨loaded,mac,Campaign2.Product.snapshot {w with wg := atMac,ambient := macAmbient},
          cut.map (Product.restoreResponseCallCut (Campaign2.Product.snapshot w).fixture),
          Campaign2.Product.snapshot {w with wg := atCut,ambient := cutAmbient},?_,?_⟩
        · rw [TimerDiscipline.observe_ok macLift,TimerDiscipline.observe_ok cutLift]
        · intro admitted rejected
          have noCut : cut = none := by cases cut <;> simp_all
          subst cut
          change Except.ok (((),atCut),cutAmbient) = Except.ok (((),current),after) at callRun
          cases callRun
          have endpoints := responseCallPrefix_admitted_endpoints msg src w.wg w.ambient
            loaded mac atMac macAmbient none current after macPrefix admitted prefixRun
          intro pid
          have point := congrFun endpoints pid
          have remote := congrArg (fun x : Option (Option Endpoint) => x.join.map destination) point
          change ((current.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination =
            ((w.wg.dev.bind fun d => d.peers[pid]?).bind Peer.endpoint).map destination
          have joinMap (p : Option Peer) : (p.map Peer.endpoint).join = p.bind Peer.endpoint := by
            cases p <;> rfl
          simpa only [responseEndpointMap,joinMap] using remote

end Leanux.Proofs.WG.Roaming
