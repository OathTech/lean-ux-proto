import Leanux.Proofs.WG.Roaming.HandshakeRemoteFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Framing TimerDiscipline Std.Do

theorem observedResponseHandshake_finalRemotes (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_RESPONSE) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedResponseHandshake msg src) (fun s => s = entry)
      (fun observed final => ResponseCallObservation msg observed ∧
        ResponseFinalRemotes entry src observed final) := by
  intro g ambient observed final after pre run
  have facts := observedResponseHandshake_facts msg src kind g ambient observed final after trivial run
  rw [observedResponseHandshake_source msg src kind] at run
  change (((responseCallPrefix msg src).run g).run ambient >>= fun ((candidate,atCut),cutAmbient) =>
    ((responseCallSuffix msg src candidate).run atCut).run cutAmbient >>= fun ((_,finish),ending) =>
      Except.ok ((Except.ok (candidate,Campaign2.snapshot atCut cutAmbient),finish),ending)) = _ at run
  cases prefixRun : ((responseCallPrefix msg src).run g).run ambient with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨candidate,atCut⟩,cutAmbient⟩ := pair
    rw [prefixRun] at run
    change (((responseCallSuffix msg src candidate).run atCut).run cutAmbient >>= fun ((_,finish),ending) =>
      Except.ok ((Except.ok (candidate,Campaign2.snapshot atCut cutAmbient),finish),ending)) = _ at run
    cases suffix : ((responseCallSuffix msg src candidate).run atCut).run cutAmbient with
    | error stop => rw [suffix] at run; cases run
    | ok pair =>
      obtain ⟨⟨value,finish⟩,ending⟩ := pair
      rw [suffix] at run
      cases run
      have same : destinationAt atCut = remoteMap entry :=
        ((ProjectedAction.iff_run_ambient _ _ _).mp (responseCallPrefix_remotes msg src)
          g ambient candidate atCut cutAmbient prefixRun).trans (congrArg remoteMap pre)
      exact ⟨facts,candidate,Campaign2.snapshot atCut cutAmbient,rfl,same,
        responseCallSuffix_remotes msg src candidate (remoteMap entry)
          atCut cutAmbient value final after same suffix⟩

theorem observedInitiationHandshake_finalRemotes (msg : List UInt8) (src : SkbSource)
    (kind : messageType msg = MESSAGE_HANDSHAKE_INITIATION) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (observedInitiationHandshake msg src) (fun s => s = entry)
      (fun observed final => InitiationCallObservation msg observed ∧
        InitiationFinalRemotes entry src observed final) := by
  intro g ambient observed final after pre run
  rw [observedInitiationHandshake_source msg src kind] at run
  change (((initiationCallPrefix msg src).run g).run ambient >>= fun ((candidate,atCut),cutAmbient) =>
    ((initiationCallSuffix msg src candidate).run atCut).run cutAmbient >>= fun ((_,finish),ending) =>
      Except.ok ((Except.ok (candidate,Campaign2.snapshot atCut cutAmbient),finish),ending)) = _ at run
  cases prefixRun : ((initiationCallPrefix msg src).run g).run ambient with
  | error stop => rw [prefixRun] at run; cases run
  | ok pair =>
    obtain ⟨⟨candidate,atCut⟩,cutAmbient⟩ := pair
    rw [prefixRun] at run
    change (((initiationCallSuffix msg src candidate).run atCut).run cutAmbient >>= fun ((_,finish),ending) =>
      Except.ok ((Except.ok (candidate,Campaign2.snapshot atCut cutAmbient),finish),ending)) = _ at run
    cases suffix : ((initiationCallSuffix msg src candidate).run atCut).run cutAmbient with
    | error stop => rw [suffix] at run; cases run
    | ok pair =>
      obtain ⟨⟨value,finish⟩,ending⟩ := pair
      rw [suffix] at run
      cases run
      have same : destinationAt atCut = remoteMap entry :=
        ((ProjectedAction.iff_run_ambient _ _ _).mp (initiationCallPrefix_remotes msg src)
          g ambient candidate atCut cutAmbient prefixRun).trans (congrArg remoteMap pre)
      have facts : InitiationCallObservation msg (.ok (candidate, Campaign2.snapshot atCut cutAmbient)) :=
        ⟨candidate,Campaign2.snapshot atCut cutAmbient,rfl,
          initiationCallPrefix_facts msg src g ambient candidate atCut cutAmbient trivial prefixRun⟩
      exact ⟨facts,candidate,Campaign2.snapshot atCut cutAmbient,rfl,same,
        initiationCallSuffix_remotes msg src candidate (remoteMap entry)
          atCut cutAmbient value final after same suffix⟩


end Leanux.Proofs.WG.Roaming
