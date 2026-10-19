import Leanux.Proofs.WG.Progress.ActivationExitSource
import Leanux.Proofs.WG.Progress.CommittedRunModel
import Leanux.Proofs.WG.Queues.SchedulerPreservation

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress.CommittedRuns
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes RxHistory.SchedulerSource

/-- Execute the existing activation audit once and retain its receipt even when
the actual call stops. The native result is exactly that audit's erasure. -/
def run (origin : Origin) (a : Activation) : PrefixM Receipt Unit :=
  fun entry => ExceptT.mk fun history =>
    let audit := activationExitRun a entry
    (audit.erase, history ++ [⟨origin,a,Campaign2.Product.snapshot entry,
      audit.map Campaign2.Product.snapshot⟩])

theorem run_exact (origin : Origin) (a : Activation) (entry : World) (history : List Receipt) :
    runPrefix (run origin a) entry history =
      ((Env.Activation.run a).run entry, history ++ [⟨origin,a,Campaign2.Product.snapshot entry,
        (activationExitRun a entry).map Campaign2.Product.snapshot⟩]) := by
  change ((activationExitRun a entry).erase, _) = _
  rw [activationExitRun_erases]

theorem run_erases (origin : Origin) (a : Activation) :
    ErasesPrefix (run origin a) (Env.Activation.run a) := by
  intro entry history
  exact congrArg Prod.fst (run_exact origin a entry history)

namespace History

theorem run_preserves (P : Receipt → Prop)
    (fresh : ∀ origin activation entry, P ⟨origin,activation,Campaign2.Product.snapshot entry,
      (activationExitRun activation entry).map Campaign2.Product.snapshot⟩)
    (origin : Origin) (a : Activation) :
    PrefixPreserves (fun history _ => ∀ receipt ∈ history, P receipt)
      (fun history => ∀ receipt ∈ history, P receipt) (run origin a) := by
  intro entry history prior
  let receipt : Receipt := ⟨origin,a,Campaign2.Product.snapshot entry,
    (activationExitRun a entry).map Campaign2.Product.snapshot⟩
  have valid : ∀ r ∈ history ++ [receipt], P r := by
    intro r member
    rcases List.mem_append.mp member with old | added
    · exact prior r old
    · simp only [List.mem_singleton] at added
      subst r
      exact fresh origin a entry
  refine ⟨[receipt], ?_, ?_, ?_⟩
  · rw [run_exact]
  · rw [run_exact]
    exact valid
  · rw [run_exact]
    cases (Env.Activation.run a).run entry with
    | error error => trivial
    | ok pair => obtain ⟨value,final⟩:=pair; exact valid

end History

theorem run_preserves (origin : Origin) (a : Activation) :
    PrefixPreserves (fun history _ => ValidHistory history) ValidHistory (run origin a) :=
  History.run_preserves Valid (fun _ activation entry => activationExitRun_facts activation entry) origin a
def old {E α : Type} (observer : PrefixM E α) : PrefixM Receipt α :=
  liftPrefix (fun entry => (runPrefix observer entry []).1)

theorem old_eq {E α : Type} (observer : PrefixM E α) (action : Leanux.M α)
    (erases : ErasesPrefix observer action) : old observer = liftPrefix action := by
  apply congrArg liftPrefix
  funext entry
  exact erases entry []

namespace History

theorem lift_preserves (S : List Receipt → Prop) {α : Type} (action : Leanux.M α) :
    PrefixPreserves (fun history _ => S history) S (liftPrefix action) :=
  PrefixEnsures.preserves (PrefixEnsures.lift action (fun _ _ prior => prior)
    (fun _ _ _ _ prior _ => prior))

end History

theorem lift_preserves {α : Type} (action : Leanux.M α) :
    PrefixPreserves (fun history _ => ValidHistory history) ValidHistory (liftPrefix action) :=
  History.lift_preserves ValidHistory action

namespace History

theorem atoms (S : List Receipt → Prop) : AtomContracts (fun history _ => S history) S
    (fun {_} a => old a) := by
  constructor
  all_goals intros; exact (Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _

end History

theorem atoms : AtomContracts (fun history _ => ValidHistory history) ValidHistory
    (fun {_} a => old a) :=
  History.atoms ValidHistory

def dispatch (worker : Worker) : PrefixM Receipt Bool :=
  dispatchWith (fun {_} a => old a) (run .dispatch) worker

def schedule (stack : Option Worker := none) : PrefixM Receipt Unit :=
  scheduleWith (fun {_} a => old a) dispatch (run .resume)
    (liftPrefix Env.napiSoftirq) stack

namespace History

theorem dispatch_preserves (S : List Receipt → Prop)
    (runs : ∀ origin activation, PrefixPreserves (fun h _=>S h) S (run origin activation)) (worker : Worker) :
    PrefixPreserves (fun history _ => S history) S (dispatch worker) :=
  RxHistory.SchedulerSource.dispatch_preserves
    (I := fun history _ => S history) (S := S) (fun _ _ prior => prior)
    (fun _ _ _ _ prior => prior) _ (Leanux.Proofs.WG.Progress.CommittedRuns.History.atoms S) _ (runs .dispatch) worker

end History

theorem dispatch_preserves (worker : Worker) :
    PrefixPreserves (fun history _ => ValidHistory history) ValidHistory (dispatch worker) :=
  History.dispatch_preserves ValidHistory CommittedRuns.run_preserves worker

namespace History

theorem schedule_preserves (S : List Receipt → Prop)
    (runs : ∀ origin activation, PrefixPreserves (fun h _=>S h) S (run origin activation)) (stack : Option Worker) :
    PrefixPreserves (fun history _ => S history) S (schedule stack) :=
  RxHistory.SchedulerSource.schedule_preserves
    (I := fun history _ => S history) (S := S) (fun _ _ prior => prior)
    (fun _ _ _ _ prior => prior) _ (Leanux.Proofs.WG.Progress.CommittedRuns.History.atoms S) _ _ _ (Leanux.Proofs.WG.Progress.CommittedRuns.History.dispatch_preserves S runs)
      (runs .resume) ((Leanux.Proofs.WG.Progress.CommittedRuns.History.lift_preserves S) _) stack

end History

theorem schedule_preserves (stack : Option Worker) :
    PrefixPreserves (fun history _ => ValidHistory history) ValidHistory (schedule stack) :=
  History.schedule_preserves ValidHistory CommittedRuns.run_preserves stack

theorem old_native {α : Type} (a : WG.M α) :
    old (RxHistory.mixed (liftWGObserver (liftWGPrefix a))) = liftPrefix (liftWG a) :=
  old_eq _ _ (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift a)))

theorem old_trial :
    old (RxHistory.audit consistentFilterAudit) =
      (do let w ← liftPrefix getAmbient
          liftPrefix (w.suspended.filterM Env.Activation.consistent) : PrefixM Receipt (List Activation)) := by
  rw [old_eq _ _ (RxHistory.audit_erases consistentFilterAudit_erases)]
  rfl

theorem dispatch_erases (worker : Worker) :
    ErasesPrefix (dispatch worker) (Env.dispatch worker) := by
  unfold dispatch dispatchWith Env.dispatch
  simp only [old_native]
  repeat' first
    | (with_reducible exact run_erases .dispatch _)
    | (with_reducible exact erasesPrefix_lift _)
    | (with_reducible exact erasesPrefix_pure _)
    | (with_reducible apply erasesPrefix_bind)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals exact erasesPrefix_lift _

theorem schedule_erases (stack : Option Worker) :
    ErasesPrefix (schedule stack) (Env.schedule stack) := by
  rw [← Lifetimes.scheduleWithPending_eq]
  unfold schedule scheduleWith Lifetimes.scheduleWithPending
  simp only [old_eq _ _ (RxHistory.mixed_erases (pendingNapiPrefix_erases _)),
    old_eq _ _ (RxHistory.mixed_erases (activationHasWorkPrefix_erases _)),
    old_trial, bind_assoc]
  repeat' first
    | (with_reducible exact dispatch_erases _)
    | (with_reducible exact run_erases .resume _)
    | (with_reducible exact erasesPrefix_lift _)
    | (with_reducible exact erasesPrefix_pure _)
    | (with_reducible apply erasesPrefix_range)
    | (with_reducible apply erasesPrefix_bind)
    | (with_reducible split; all_goals try simp_all only []; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
  all_goals first
    | exact erasesPrefix_lift _
    | grind only [dispatch_erases, erasesPrefix_lift]

end Leanux.Proofs.WG.Progress.CommittedRuns
