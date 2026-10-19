import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixAdapters

/-! The actual runner preparation and return guard transport its native
companions and retain the independent certificate for all prior prefixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open TransmitSecurity RetirementSecurity CausalJournal CompleteRunner Lifetimes Queues
open Leanux.Proofs.Framing Queues.RxCredits

abbrev Entry := With Ready CompleteProduct.Safe
abbrev Exit := With Returned CompleteProduct.Safe

theorem safe (h : List Event) (w : World) (before : Entry h w) : All CompleteProduct.Safe h := before.2

theorem prepare (trace : Trace) (state : RunnerOperation.State) (h : List Event)
    (before : Entry h state.1) : Entry h (RunnerOperation.prepare trace state) :=
  ⟨ready_prepare trace state h before.1,before.2⟩

theorem close (h : List Event) (w v : World) (same : v.wg=w.wg)
    (idle : v.ambient.suspended=[]) (incoming : w.ambient.suspended=[])
    (before : Exit h w) : Entry h v :=
  ⟨ready_close h w v same idle incoming before.1,before.2⟩

theorem initial (net bare : Bool) (w : World)
    (same : wgStoreView w.wg=wgStoreView (initialWG net bare))
    (idle : w.ambient.suspended=[]) : Entry [] w :=
  ⟨ready_initial net bare w same idle,All.nil empty_safe⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Runner
