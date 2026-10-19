import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerCommonSource
import Leanux.Proofs.WG.TimerDiscipline.SessionWheelSource

/-! Original full poll, NAPI, scheduler and deferred outcomes with committed
hook/session receipts. Counts are per-label invocation counts, not uniqueness
or firing bounds; wheel facts concern each normal derived-hook exit. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal Lifetimes

def inspect {α : Type} (observer : Obs α) :
    Leanux.M (Campaign2.Product.Outcome α × List Event) := fun w =>
  let result:=runPrefix observer w []
  .ok ((Campaign2.Product.observeResult result.1,result.2),w)

def Facts (history : List Event) : Prop :=
  ValidHistory history ∧ Paired history ∧
  (∀ serial,history.countP (fun e=>e.sessionId==some serial)=
    history.countP (fun e=>e.derivedId==some serial)) ∧ WheelHistoryFacts history

theorem inspect_source {α : Type} (observer : Obs α) (action : Leanux.M α)
    (source : ErasesPrefix observer action) :
    (do let result←inspect observer; pure result.1)=Campaign2.Product.inspect action := by
  funext w
  change Except.ok (Campaign2.Product.observeResult (runPrefix observer w []).1,w)=
    Except.ok (Campaign2.Product.observeResult (action.run w),w)
  rw [source w []]

theorem inspect_facts {α : Type} (observer : Obs α)
    (valid : PrefixPreserves (fun h _=>ValidHistory h) ValidHistory observer)
    (paired : PrefixPreserves (fun h _=>Paired h) Paired observer) :
    Campaign2.Product.Returns (inspect observer) (fun _=>True)
      (fun result _=>Facts result.2) := by
  intro w _
  obtain ⟨_,_,hv,_⟩:=valid w [] (by intro e member;cases member)
  obtain ⟨_,_,hp,_⟩:=paired w [] Paired.nil
  exact ⟨_,w,rfl,hv,hp,fun serial=>hp.counts serial,fun r kind member=>history_wheel hv hp r kind member⟩

theorem original_poll (pid : PeerId) (budget : Nat) :
    (do let result←inspect (poll pid budget); pure result.1)=Campaign2.Product.inspect (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) ∧
    Campaign2.Product.Returns (inspect (poll pid budget)) (fun _=>True)
      (fun result _=>Facts result.2) :=
  ⟨inspect_source _ _ (poll_erases pid budget),
    inspect_facts _ (poll_valid pid budget) (poll_paired pid budget)⟩

theorem original_softirq :
    (do let result←inspect (softirq); pure result.1)=Campaign2.Product.inspect Env.napiSoftirq ∧
    Campaign2.Product.Returns (inspect (softirq)) (fun _=>True)
      (fun result _=>Facts result.2) :=
  ⟨inspect_source _ _ (softirq_erases),
    inspect_facts _ (softirq_valid) (softirq_paired)⟩

theorem original_inline :
    (do let result←inspect (inline); pure result.1)=Campaign2.Product.inspect Env.pollScheduledInline ∧
    Campaign2.Product.Returns (inspect (inline)) (fun _=>True)
      (fun result _=>Facts result.2) :=
  ⟨inspect_source _ _ (inline_erases),
    inspect_facts _ (inline_valid) (inline_paired)⟩

theorem original_irqExit :
    (do let result←inspect (irqExit); pure result.1)=Campaign2.Product.inspect Env.napiIrqExit ∧
    Campaign2.Product.Returns (inspect (irqExit)) (fun _=>True)
      (fun result _=>Facts result.2) :=
  ⟨inspect_source _ _ (irqExit_erases),
    inspect_facts _ (irqExit_valid) (irqExit_paired)⟩

theorem original_schedule (worker : Option Worker) :
    (do let result←inspect (schedule worker); pure result.1)=Campaign2.Product.inspect (Env.schedule worker) ∧
    Campaign2.Product.Returns (inspect (schedule worker)) (fun _=>True)
      (fun result _=>Facts result.2) :=
  ⟨inspect_source _ _ (schedule_erases worker),
    inspect_facts _ (schedule_valid worker) (schedule_paired worker)⟩

theorem original_deferred (call : EnvDeferredCall) :
    (do let result←inspect (deferred call); pure result.1)=Campaign2.Product.inspect call.original ∧
    Campaign2.Product.Returns (inspect (deferred call)) (fun _=>True)
      (fun result _=>Facts result.2) :=
  ⟨inspect_source _ _ (deferred_erases call),
    inspect_facts _ (deferred_valid call) (deferred_paired call)⟩

end Leanux.Proofs.WG.TimerDiscipline.HookCommon
