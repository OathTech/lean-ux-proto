import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerWorkersSource

/-! The existing SourceScheduler supplies the run, dispatch and scheduler
control flow. Copied consistency trials execute their original native action
and emit no committed hook receipt. Every hook-bearing committed worker and
NAPI path is routed through the explicit callback contracts. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookScheduler
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Queues Leanux.Proofs.WG.Lifetimes
variable {E : Type}

def run (c : Callbacks E) (a : Activation) : PrefixM E Unit :=
  SourceScheduler.run (iteration c) a

def dispatch (c : Callbacks E) (worker : Worker) : PrefixM E Bool :=
  SourceScheduler.dispatch (iteration c) worker

def schedule (c : Callbacks E) (stack : Option Worker := none) : PrefixM E Unit :=
  SourceScheduler.schedule (iteration c) c.softirq stack

def nested (c : Callbacks E) (worker : Worker) : PrefixM E Unit :=
  RxHistory.SchedulerSource.nestedWith (fun stack=>schedule c stack) worker

theorem run_erases (c : Callbacks E) (h : ErasureContracts c) (a : Activation) :
    ErasesPrefix (run c a) (Env.Activation.run a) :=
  SourceScheduler.run_erases _ (iteration_erases c h) a

theorem dispatch_erases (c : Callbacks E) (h : ErasureContracts c) (worker : Worker) :
    ErasesPrefix (dispatch c worker) (Env.dispatch worker) :=
  SourceScheduler.dispatch_erases _ (iteration_erases c h) worker

theorem schedule_erases (c : Callbacks E) (h : ErasureContracts c) (stack : Option Worker) :
    ErasesPrefix (schedule c stack) (Env.schedule stack) :=
  SourceScheduler.schedule_erases _ _ (iteration_erases c h) h.softirq stack

theorem nested_erases (c : Callbacks E) (h : ErasureContracts c) (worker : Worker) :
    ErasesPrefix (nested c worker) (Env.nestedResched worker) := by
  unfold nested RxHistory.SchedulerSource.nestedWith Env.nestedResched
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro ready
  split
  · exact schedule_erases c h _
  · exact erasesPrefix_pure _

theorem run_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ history w, I history w → S history) (store : HookState.StoreTransport I)
    (c : Callbacks E) (h : StateContracts I S c) (leaves : StateLeaves I S) (a : Activation) :
    PrefixPreserves I S (run c a) :=
  SourceScheduler.run_preserves safe (HookState.product_transport store) _
    (iteration_preserves_state safe store c h leaves) a

theorem dispatch_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ history w, I history w → S history) (store : HookState.StoreTransport I)
    (c : Callbacks E) (h : StateContracts I S c) (leaves : StateLeaves I S) (worker : Worker) :
    PrefixPreserves I S (dispatch c worker) :=
  SourceScheduler.dispatch_preserves safe (HookState.product_transport store)
    (fun pid => by simpa only [old_native] using leaves.atoms.work (fun q => q.erase pid)) _ (iteration_preserves_state safe store c h leaves) worker

theorem schedule_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ history w, I history w → S history) (store : HookState.StoreTransport I)
    (c : Callbacks E) (h : StateContracts I S c) (leaves : StateLeaves I S) (stack : Option Worker) :
    PrefixPreserves I S (schedule c stack) :=
  SourceScheduler.schedule_preserves safe (HookState.product_transport store)
    (fun pid => by simpa only [old_native] using leaves.atoms.work (fun q => q.erase pid)) _ _ (iteration_preserves_state safe store c h leaves) h.softirq stack

theorem nested_preserves_state {I : List E → World → Prop} {S : List E → Prop}
    (safe : ∀ history w, I history w → S history) (store : HookState.StoreTransport I)
    (c : Callbacks E) (h : StateContracts I S c) (leaves : StateLeaves I S) (worker : Worker) :
    PrefixPreserves I S (nested c worker) :=
  RxHistory.SchedulerSource.nested_preserves safe (HookState.product_transport store) _
    (schedule_preserves_state safe store c h leaves) worker

theorem run_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c) (a : Activation) :
    PrefixPreserves (fun h _=>S h) S (run c a) :=
  run_preserves_state (I := fun h _ => S h) (S := S) (fun _ _ hi => hi)
    (fun _ _ _ _ hi => hi) c (history_state S c h) (history_leaves S) a

theorem dispatch_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (worker : Worker) : PrefixPreserves (fun h _=>S h) S (dispatch c worker) :=
  dispatch_preserves_state (I := fun h _ => S h) (S := S) (fun _ _ hi => hi)
    (fun _ _ _ _ hi => hi) c (history_state S c h) (history_leaves S) worker

theorem schedule_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (stack : Option Worker) : PrefixPreserves (fun h _=>S h) S (schedule c stack) :=
  schedule_preserves_state (I := fun h _ => S h) (S := S) (fun _ _ hi => hi)
    (fun _ _ _ _ hi => hi) c (history_state S c h) (history_leaves S) stack

theorem nested_preserves (S : List E → Prop) (c : Callbacks E) (h : HistoryContracts S c)
    (worker : Worker) : PrefixPreserves (fun h _=>S h) S (nested c worker) :=
  nested_preserves_state (I := fun h _ => S h) (S := S) (fun _ _ hi => hi)
    (fun _ _ _ _ hi => hi) c (history_state S c h) (history_leaves S) worker

/-- Appending is the existing trivial-safety preservation contract, so no
second traversal of the scheduler loops is needed for the append proof. -/
theorem append_history (c : Callbacks E) (h : AppendContracts c) :
    HistoryContracts (fun _=>True) c := by
  let iffAppends : ∀ {α : Type} (a : PrefixM E α),
      PrefixPreserves (fun _ _=>True) (fun _=>True) a ↔ Appends a :=
    fun a => (pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) a
  exact ⟨fun pid=>(iffAppends _).mpr (h.transmit pid),
    (iffAppends _).mpr h.receive,(iffAppends _).mpr h.softirq,(iffAppends _).mpr h.irq⟩

theorem run_appends (c : Callbacks E) (h : AppendContracts c) (a : Activation) :
    Appends (run c a) :=
  ((pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) _).mp
    (run_preserves (fun _=>True) c (append_history c h) a)

theorem dispatch_appends (c : Callbacks E) (h : AppendContracts c) (worker : Worker) :
    Appends (dispatch c worker) :=
  ((pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) _).mp
    (dispatch_preserves (fun _=>True) c (append_history c h) worker)

theorem schedule_appends (c : Callbacks E) (h : AppendContracts c) (stack : Option Worker) :
    Appends (schedule c stack) :=
  ((pinned_const _private.Leanux.Proofs.WG.Queues.NapiSource.«0».Leanux.Proofs.WG.Queues.NapiSource.trivial_iff_appends) _).mp
    (schedule_preserves (fun _=>True) c (append_history c h) stack)

theorem nested_appends (c : Callbacks E) (h : AppendContracts c) (worker : Worker) :
    Appends (nested c worker) :=
  RxHistory.SchedulerSource.nested_appends _ (schedule_appends c h) worker

end Leanux.Proofs.WG.TimerDiscipline.HookScheduler
