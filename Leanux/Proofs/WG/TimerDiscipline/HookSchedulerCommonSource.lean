import Leanux.Proofs.WG.TimerDiscipline.HookNapiCommonSource
import Leanux.Proofs.WG.TimerDiscipline.HookDeferredSource

/-! Concrete original worker/scheduler/deferred executions. Copied consistency
trials retain their native execution without entering the committed journal. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal Lifetimes

def callbacks : HookScheduler.Callbacks Event := ⟨transmit,receive,softirq,irqExit⟩
theorem callbacks_erases : HookScheduler.ErasureContracts callbacks :=
  ⟨transmit_erases,receive_erases,softirq_erases,irqExit_erases⟩
theorem callbacks_valid : HookScheduler.HistoryContracts ValidHistory callbacks :=
  ⟨transmit_valid,receive_valid,softirq_valid,irqExit_valid⟩
theorem callbacks_paired : HookScheduler.HistoryContracts Paired callbacks :=
  ⟨transmit_paired,receive_paired,softirq_paired,irqExit_paired⟩
theorem callbacks_appends : HookScheduler.AppendContracts callbacks :=
  ⟨transmit_appends,receive_appends,softirq_appends,irqExit_appends⟩

def schedule (worker : Option Worker := none) : Obs Unit := HookScheduler.schedule callbacks worker
theorem schedule_erases (worker : Option Worker) :
    ErasesPrefix (schedule worker) (Env.schedule worker) :=
  HookScheduler.schedule_erases callbacks callbacks_erases worker
theorem schedule_valid (worker : Option Worker) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (schedule worker) :=
  HookScheduler.schedule_preserves ValidHistory callbacks callbacks_valid worker
theorem schedule_paired (worker : Option Worker) :
    PrefixPreserves (fun h _=>Paired h) Paired (schedule worker) :=
  HookScheduler.schedule_preserves Paired callbacks callbacks_paired worker
theorem schedule_appends (worker : Option Worker) : Appends (schedule worker) :=
  HookScheduler.schedule_appends callbacks callbacks_appends worker

def deferred (call : EnvDeferredCall) : Obs call.Result :=
  HookDeferred.observed callbacks sendOne call
theorem deferred_erases (call : EnvDeferredCall) :
    ErasesPrefix (deferred call) call.original :=
  HookDeferred.observed_erases callbacks callbacks_erases sendOne sendOne_erases call
theorem deferred_valid (call : EnvDeferredCall) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (deferred call) :=
  HookDeferred.observed_preserves ValidHistory callbacks callbacks_valid sendOne sendOne_valid call
theorem deferred_paired (call : EnvDeferredCall) :
    PrefixPreserves (fun h _=>Paired h) Paired (deferred call) :=
  HookDeferred.observed_preserves Paired callbacks callbacks_paired sendOne sendOne_paired call
theorem deferred_appends (call : EnvDeferredCall) : Appends (deferred call) :=
  HookDeferred.observed_appends callbacks callbacks_appends sendOne sendOne_appends call

end Leanux.Proofs.WG.TimerDiscipline.HookCommon
