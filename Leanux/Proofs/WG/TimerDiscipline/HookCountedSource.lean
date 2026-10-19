import Leanux.Proofs.WG.TimerDiscipline.HookCountedModel
import Leanux.Proofs.WG.TimerDiscipline.HookOuterFrontierSource
import Leanux.Proofs.WG.TimerDiscipline.HookInitializedSource

/-! The existing complete observer carries ordered allocation stamps through
the exact initialized execution, including the history retained on Stop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged HandshakeJournal
open Lifetimes Queues Configuration Std.Do

theorem counted_facts {history : List Event} (facts : Facts history) (ordered : Ordered history) :
    CountedFacts history :=
  ⟨facts,ordered,ordered.nodup,fun serial=>
    ⟨ordered.session_count serial,ordered.derived_count facts.2.1 serial,
      completedSessionEnqueues_per_allocation history facts.2.2.2 facts.2.1 ordered serial⟩⟩

theorem inspect_counted {α : Type} (observer : Obs α)
    (preserves : PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered observer)
    (valid : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory observer)
    (paired : PrefixPreserves (fun h _=>Paired h) Paired observer) :
    Campaign2.Product.Returns (inspect observer) (fun _=>True)
      (fun result _=>CountedResult result) := by
  intro w _
  obtain ⟨_,_,ordered,post⟩:=preserves w [] (frontier_nil _)
  obtain ⟨_,_,hv,_⟩:=valid w [] (by intro e member;cases member)
  obtain ⟨_,_,hp,_⟩:=paired w [] Paired.nil
  have facts : Facts (runPrefix observer w []).2 :=
    ⟨hv,hp,fun serial=>hp.counts serial,fun r kind member=>history_wheel hv hp r kind member⟩
  refine ⟨_,w,rfl,counted_facts facts ordered,?_⟩
  cases run : (runPrefix observer w []).1 with
  | error stop => simp only [Campaign2.Product.observeResult,Except.map]
  | ok out =>
    obtain ⟨value,last⟩:=out
    simpa only [run,Campaign2.Product.observeResult,Except.map,Campaign2.Product.snapshot,
      Campaign2.snapshot,Campaign2.core] using post

namespace Initialized
theorem observed_frontier (trace : Trace) (placeholders : Bool) :
    Ordered (runPrefixOuter (observed trace placeholders) []).2 ∧
    match (runPrefixOuter (observed trace placeholders) []).1 with
    | .error _ => True
    | .ok (_,last) => Frontier (runPrefixOuter (observed trace placeholders) []).2 last.wg.keypairCounter := by
  have checked := (prefixOuter_wp_iff (observed trace placeholders)
    (fun h=>h=[]) (fun out h=>Frontier h out.2.wg.keypairCounter) (fun _ h=>Ordered h)).mp
    (RunnerInvariant.Normal.executeTraceWith_wp (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (fun _ _ h=>h.1) (fun h w v=>frontier_wg_store h w.wg v.wg)
      syscall syscall_frontier trace placeholders (fun _ _=>frontier_nil _)) [] rfl
  cases run : runPrefixOuter (observed trace placeholders) [] with
  | mk result history =>
    cases result with
    | error err =>
      have ordered : Ordered history := by simpa only [run] using checked
      simpa only [run] using And.intro ordered True.intro
    | ok out =>
      have post : Frontier history out.2.wg.keypairCounter := by simpa only [run] using checked
      simpa only [run] using And.intro post.1 post

theorem inspection_counted (trace : Trace) (placeholders : Bool) :
    CountedResult (inspection trace placeholders) := by
  have all:=observed_frontier trace placeholders
  refine ⟨counted_facts (inspection_facts trace placeholders) all.1,?_⟩
  dsimp only [inspection]
  cases run : (runPrefixOuter (observed trace placeholders) []).1 with
  | error err => simp only [Except.map]
  | ok out =>
    obtain ⟨json,last⟩:=out
    simpa only [run,Except.map,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core] using all.2
end Initialized

end Leanux.Proofs.WG.TimerDiscipline.HookCommon

