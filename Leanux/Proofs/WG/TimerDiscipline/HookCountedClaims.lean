import Leanux.Proofs.WG.TimerDiscipline.HookCountedSource

/-! Complete original calls and initialized execution with ordered allocation
stamps and at most one completed session-derived wheel enqueue per stamp. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged HandshakeJournal Lifetimes

theorem original_schedule_counted (worker : Option Worker) :
    (do let result←inspect (schedule worker);pure result.1)=Campaign2.Product.inspect (Env.schedule worker) ∧
    Campaign2.Product.Returns (inspect (schedule worker)) (fun _=>True)
      (fun result _=>CountedResult result) :=
  ⟨inspect_source _ _ (schedule_erases worker),
    inspect_counted _ (schedule_frontier worker) (schedule_valid worker) (schedule_paired worker)⟩

theorem original_deferred_counted (call : EnvDeferredCall) :
    (do let result←inspect (deferred call);pure result.1)=Campaign2.Product.inspect call.original ∧
    Campaign2.Product.Returns (inspect (deferred call)) (fun _=>True)
      (fun result _=>CountedResult result) :=
  ⟨inspect_source _ _ (deferred_erases call),
    inspect_counted _ (deferred_frontier call) (deferred_valid call) (deferred_paired call)⟩

theorem original_syscall_counted (c : Syscall) :
    (do let result←inspect (syscall c);pure result.1)=Campaign2.Product.inspect (Leanux.syscall c) ∧
    Campaign2.Product.Returns (inspect (syscall c)) (fun _=>True)
      (fun result _=>CountedResult result) :=
  ⟨inspect_source _ _ (syscall_erases c),
    inspect_counted _ (syscall_frontier c) (syscall_valid c) (syscall_paired c)⟩

theorem original_initialized_counted (trace : Trace) (placeholders : Bool) :
    (Initialized.inspection trace placeholders).1.map Prod.fst=Runner.executeTrace trace placeholders ∧
    CountedResult (Initialized.inspection trace placeholders) :=
  ⟨Initialized.inspection_json trace placeholders,Initialized.inspection_counted trace placeholders⟩

end Leanux.Proofs.WG.TimerDiscipline.HookCommon

