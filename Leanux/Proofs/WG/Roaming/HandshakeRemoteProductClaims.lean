import Leanux.Proofs.WG.Roaming.HandshakeRemoteProductFrames
import Leanux.Proofs.WG.Roaming.HandshakeRemoteClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Framing TimerDiscipline Std.Do

namespace Product

theorem observedResponseHandshake_finalRemotes (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedResponseHandshake msg src) (fun s => s = entry)
      (fun observed final => ResponseCallObservation msg observed ∧
        ResponseFinalRemotes entry src observed final) := by
  intro w observed final pre run
  have facts := observedResponseHandshake_facts msg src kind w observed final trivial run
  rw [observedResponseHandshake_source msg src kind] at run
  change ((responseCallPrefix msg src).run w >>= fun (candidate,atCut) =>
    (responseCallSuffix msg src candidate).run atCut >>= fun (_,finish) =>
      Except.ok (Except.ok (candidate,Campaign2.Product.snapshot atCut),finish)) = _ at run
  cases prefixRun : (responseCallPrefix msg src).run w with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    obtain ⟨candidate,atCut⟩ := pair
    rw [prefixRun] at run
    change ((responseCallSuffix msg src candidate).run atCut >>= fun (_,finish) =>
      Except.ok (Except.ok (candidate,Campaign2.Product.snapshot atCut),finish)) = _ at run
    cases suffixRun : (responseCallSuffix msg src candidate).run atCut with
    | error stop => rw [suffixRun] at run; cases run
    | ok pair =>
      obtain ⟨value,finish⟩ := pair
      rw [suffixRun] at run
      cases run
      have same := responseCallPrefix_remotes msg src (remoteMap entry.toSnapshot)
        w candidate atCut (congrArg (fun s : Campaign2.Product.Snapshot => remoteMap s.toSnapshot) pre) prefixRun
      exact ⟨facts,candidate,Campaign2.Product.snapshot atCut,rfl,same,
        responseCallSuffix_remotes msg src candidate (remoteMap entry.toSnapshot)
          atCut value final same suffixRun⟩

theorem observedInitiationHandshake_finalRemotes (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (observedInitiationHandshake msg src) (fun s => s = entry)
      (fun observed final => InitiationCallObservation msg observed ∧
        InitiationFinalRemotes entry src observed final) := by
  intro w observed final pre run
  have facts := observedInitiationHandshake_facts msg src kind w observed final trivial run
  rw [observedInitiationHandshake_source msg src kind] at run
  change ((initiationCallPrefix msg src).run w >>= fun (candidate,atCut) =>
    (initiationCallSuffix msg src candidate).run atCut >>= fun (_,finish) =>
      Except.ok (Except.ok (candidate,Campaign2.Product.snapshot atCut),finish)) = _ at run
  cases prefixRun : (initiationCallPrefix msg src).run w with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    obtain ⟨candidate,atCut⟩ := pair
    rw [prefixRun] at run
    change ((initiationCallSuffix msg src candidate).run atCut >>= fun (_,finish) =>
      Except.ok (Except.ok (candidate,Campaign2.Product.snapshot atCut),finish)) = _ at run
    cases suffixRun : (initiationCallSuffix msg src candidate).run atCut with
    | error stop => rw [suffixRun] at run; cases run
    | ok pair =>
      obtain ⟨value,finish⟩ := pair
      rw [suffixRun] at run
      cases run
      have same := initiationCallPrefix_remotes msg src (remoteMap entry.toSnapshot)
        w candidate atCut (congrArg (fun s : Campaign2.Product.Snapshot => remoteMap s.toSnapshot) pre) prefixRun
      exact ⟨facts,candidate,Campaign2.Product.snapshot atCut,rfl,same,
        initiationCallSuffix_remotes msg src candidate (remoteMap entry.toSnapshot)
          atCut value final same suffixRun⟩


end Product

end Leanux.Proofs.WG.Roaming
