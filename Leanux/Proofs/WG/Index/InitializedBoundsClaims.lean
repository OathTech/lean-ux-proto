import Leanux.Proofs.WG.Index.InitializedBoundsSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.InitializedBounds
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

/-! Claims: only the genuine campaign projection appears in the result.
Both placeholder modes and every indexed original Stop remain unchanged. -/
def inspection (trace : Runner.Trace) (placeholders : Bool) : Inspection :=
  (runPrefixOuter (RunnerAccount.observed trace placeholders) []).1.map
    (fun (json,w) => (json,Campaign2.snapshot w.wg w.ambient))

theorem inspection_json (trace : Runner.Trace) (placeholders : Bool) :
    (inspection trace placeholders).map Prod.fst = Runner.executeTrace trace placeholders := by
  have exactRun := RunnerAccount.json trace placeholders []
  cases run : (runPrefixOuter (RunnerAccount.observed trace placeholders) []).1 <;>
    simpa only [inspection,run,Except.map] using exactRun

theorem inspection_bounds (trace : Runner.Trace) (placeholders : Bool) :
    match inspection trace placeholders with
    | .error _ => True
    | .ok (_,final) => EndpointSafe final := by
  cases run : runPrefixOuter (RunnerAccount.observed trace placeholders) [] with
  | mk outcome history =>
    cases outcome with
    | error stop => simp only [inspection,run,Except.map]
    | ok out =>
      obtain ⟨json,w⟩ := out
      simpa only [inspection,run,Except.map] using runner_normal trace placeholders json w history run

theorem accepted_bounds (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (accepted : Runner.executeTrace trace placeholders = .ok json) :
    ∃ final, inspection trace placeholders = .ok (json,final) ∧ EndpointSafe final := by
  obtain ⟨w,history,run,bounds⟩ := runner_accepted trace placeholders json accepted
  exact ⟨Campaign2.snapshot w.wg w.ambient,by simp only [inspection,run,Except.map],bounds⟩

theorem normal_session_fresh (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Snapshot) (normal : inspection trace placeholders = .ok (json,final))
    (d : Device) (device : final.wg.device = some d)
    (pid : PeerId) (p : Peer) (resident : d.peers[pid]? = some p) :
    SessionRotationFresh p d.nextKeypairId := by
  have bounds : EndpointSafe final := by
    simpa only [normal] using inspection_bounds trace placeholders
  exact slots_session_fresh d pid p (bounds d device).slots resident

theorem normal_hashed_bound (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Snapshot) (normal : inspection trace placeholders = .ok (json,final))
    (d : Device) (device : final.wg.device = some d)
    (coherent : HashedOwnersCoherent d) : KeypairOwnersBounded d := by
  have bounds : EndpointSafe final := by
    simpa only [normal] using inspection_bounds trace placeholders
  exact store_hashed_bound d (bounds d device).keys coherent

end Leanux.Proofs.WG.Index.InitializedBounds
