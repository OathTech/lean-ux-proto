import Leanux.Proofs.WG.Index.ReachedInitializedBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ReachedInitialized
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

theorem inspection_json (trace : Runner.Trace) (placeholders : Bool) :
    (inspection trace placeholders).map Prod.fst=Runner.executeTrace trace placeholders := by
  have exactRun := RunnerAccount.json trace placeholders []
  cases run:(runPrefixOuter (RunnerAccount.observed trace placeholders) []).1 <;>
    simpa only [inspection,run,Except.map] using exactRun

theorem inspection_facts (trace : Runner.Trace) (placeholders : Bool) :
    match inspection trace placeholders with
    | .error _=>True
    | .ok (json,final)=>View.IndexCore final.toSnapshot ∧ ActualAccount trace placeholders json final := by
  cases run:runPrefixOuter (RunnerAccount.observed trace placeholders) [] with
  | mk outcome history=>
    cases outcome with
    | error stop=>simp only [inspection,run,Except.map]
    | ok out=>
      obtain ⟨json,w⟩ := out
      obtain ⟨_,entry⟩ := ReachedTraffic.initialized trace placeholders json w history run
      obtain ⟨ledger,certificate,account⟩ := RunnerAccount.normal trace placeholders run
      have facts : View.IndexCore (Campaign2.Product.snapshot w).toSnapshot ∧
          ActualAccount trace placeholders json (Campaign2.Product.snapshot w) :=
        ⟨entry.2,w,history,ledger,run,rfl,certificate,account⟩
      simpa only [inspection,run,Except.map] using facts

theorem normal (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Product.Snapshot)
    (run : inspection trace placeholders=.ok (json,final)) :
    View.IndexCore final.toSnapshot ∧ ActualAccount trace placeholders json final := by
  simpa only [run] using inspection_facts trace placeholders

theorem accepted (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (run : Runner.executeTrace trace placeholders=.ok json) :
    ∃ final,inspection trace placeholders=.ok (json,final) ∧
      View.IndexCore final.toSnapshot ∧ ActualAccount trace placeholders json final := by
  obtain ⟨w,history,ledger,actual,certificate,account⟩ :=
    RunnerAccount.accepted trace placeholders run
  obtain ⟨_,entry⟩ := ReachedTraffic.initialized trace placeholders json w history actual
  exact ⟨Campaign2.Product.snapshot w,by simp only [inspection,actual,Except.map],
    entry.2,w,history,ledger,actual,rfl,certificate,account⟩

theorem normal_tables (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Product.Snapshot)
    (run : inspection trace placeholders=.ok (json,final))
    (d : Device) (device : final.wg.device=some d) :
    UniqueIndices d.indexTable ∧ UniqueOwners d.indexTable ∧ KeypairOwnersBounded d :=
  ((normal trace placeholders json final run).1 d device).1

theorem normal_hashed_owner (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Product.Snapshot)
    (run : inspection trace placeholders=.ok (json,final))
    (d : Device) (device : final.wg.device=some d)
    (entry : IndexEntry) (member : entry∈d.indexTable) :
    OwnerCoherent d entry.owner :=
  ((normal trace placeholders json final run).1 d device).2.2.1 entry member

theorem normal_session_fresh (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Product.Snapshot)
    (run : inspection trace placeholders=.ok (json,final))
    (d : Device) (device : final.wg.device=some d)
    (pid : PeerId) (peer : Peer) (resident : d.peers[pid]?=some peer) :
    SessionRotationFresh peer d.nextKeypairId :=
  InitializedBounds.slots_session_fresh d pid peer
    (((normal trace placeholders json final run).2.bounds) d device).slots resident

theorem normal_bounds (trace : Runner.Trace) (placeholders : Bool) (json : Json)
    (final : Campaign2.Product.Snapshot)
    (run : inspection trace placeholders = .ok (json,final)) :
    InitializedBounds.EndpointSafe final.toSnapshot :=
  (normal trace placeholders json final run).2.bounds

end Leanux.Proofs.WG.Index.ReachedInitialized
