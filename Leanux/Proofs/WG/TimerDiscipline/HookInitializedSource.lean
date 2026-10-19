import Leanux.Proofs.WG.TimerDiscipline.HookSyscallSource
import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerClaims
/-! Initialized source linkage and persistent committed hook/session histories. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon.Initialized
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged HandshakeJournal Configuration

def observed (trace : Trace) (placeholders : Bool) :=
  HookRunner.observed syscall trace placeholders

theorem observed_valid (trace : Trace) (placeholders : Bool) :
    ValidHistory (runPrefixOuter (observed trace placeholders) []).2 :=
  HookRunner.observed_preserves syscall ValidHistory syscall_valid
    (by intro e member;cases member) trace placeholders

theorem observed_paired (trace : Trace) (placeholders : Bool) :
    Paired (runPrefixOuter (observed trace placeholders) []).2 :=
  HookRunner.observed_preserves syscall Paired syscall_paired Paired.nil trace placeholders

theorem observed_erases (trace : Trace) (placeholders : Bool) :
    ErasesOuter (observed trace placeholders) (sourceRunner trace placeholders) :=
  HookRunner.observed_erases syscall syscall_erases trace placeholders

abbrev Inspection :=
  Except (Nat × Stop) (Json × Campaign2.Product.Snapshot) × List Event

def inspection (trace : Trace) (placeholders : Bool := false) : Inspection :=
  let result:=runPrefixOuter (observed trace placeholders) []
  (result.1.map (fun (json,world)=>(json,Campaign2.Product.snapshot world)),result.2)

theorem inspection_json (trace : Trace) (placeholders : Bool) :
    (inspection trace placeholders).1.map Prod.fst=Runner.executeTrace trace placeholders := by
  dsimp only [inspection]
  rw [observed_erases trace placeholders []]
  have original:=Configuration.sourceRunner_json trace placeholders
  cases result : Configuration.sourceRunner trace placeholders <;>
    simpa only [result,Except.map] using original

theorem inspection_facts (trace : Trace) (placeholders : Bool) :
    Facts (inspection trace placeholders).2 := by
  have hv:=observed_valid trace placeholders
  have hp:=observed_paired trace placeholders
  exact ⟨hv,hp,fun serial=>hp.counts serial,fun r kind member=>history_wheel hv hp r kind member⟩

end Leanux.Proofs.WG.TimerDiscipline.HookCommon.Initialized
