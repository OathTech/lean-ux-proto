import Leanux.Proofs.WG.Roaming.HandshakeRemoteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Framing TimerDiscipline Std.Do

namespace Product

theorem observedHandshakeRemotes_facts (msg : List UInt8) (src : SkbSource)
    (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedHandshakeRemotes msg src) (fun s => s = entry)
      (fun receipt final => HandshakeFinalRemotes msg src entry receipt final) := by
  intro w receipt final pre run
  unfold observedHandshakeRemotes at run
  split at run
  next kind =>
    change ((observedInitiationHandshake msg src).run w >>= fun (observed,finish) =>
      .ok (HandshakeRemoteReceipt.initiation observed,finish)) = _ at run
    cases actual : (observedInitiationHandshake msg src).run w with
    | error stop => rw [actual] at run; cases run
    | ok pair =>
      obtain ⟨observed,finish⟩ := pair
      rw [actual] at run
      cases run
      exact ⟨kind,observedInitiationHandshake_finalRemotes msg src kind entry
        w observed final pre actual⟩
  next notInit =>
    split at run
    next kind =>
      change ((observedResponseHandshake msg src).run w >>= fun (observed,finish) =>
        .ok (HandshakeRemoteReceipt.response observed,finish)) = _ at run
      cases actual : (observedResponseHandshake msg src).run w with
      | error stop => rw [actual] at run; cases run
      | ok pair =>
        obtain ⟨observed,finish⟩ := pair
        rw [actual] at run
        cases run
        exact ⟨kind,observedResponseHandshake_finalRemotes msg src kind entry
          w observed final pre actual⟩
    next notResponse =>
      change ((liftWG (receiveHandshakePacket msg src)).run w >>= fun (_,finish) =>
        .ok (HandshakeRemoteReceipt.other,finish)) = _ at run
      cases actual : (liftWG (receiveHandshakePacket msg src)).run w with
      | error stop => rw [actual] at run; cases run
      | ok pair =>
        obtain ⟨value,finish⟩ := pair
        rw [actual] at run
        cases run
        refine ⟨notInit,notResponse,?_⟩
        exact lift_remote_effect _ (fun map => map = remoteMap entry.toSnapshot)
          (fun _ map => map = remoteMap entry.toSnapshot)
          ((ensures_iff _ _ _).mpr
            (Roaming.receiveHandshakePacket_other_remotes msg src notInit notResponse
              (remoteMap entry.toSnapshot))) w value final
          (congrArg (fun s : Campaign2.Product.Snapshot => remoteMap s.toSnapshot) pre) actual


end Product

end Leanux.Proofs.WG.Roaming
