import Leanux.Proofs.WG.Queues.RxWorkerHistory
import Leanux.Proofs.WG.Queues.PollSource
import Leanux.Proofs.WG.Lifetimes.BatchItemSource

/-! Exact callback laws for the existing NAPI and decrypt-worker sources.
The saved scan, hidden section guards, preparation receipt and worker markers
remain in their original observers. No replacement loop is defined here. -/
namespace Leanux.Proofs.WG.Queues.NapiSource
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open RxJoint.PollSource

variable {E F : Type}

private theorem trivial_iff_appends {α : Type} (a : PrefixM E α) :
    PrefixPreserves (fun _ _ => True) (fun _ => True) a ↔ Appends a := by
  constructor
  · intro ha w h
    obtain ⟨s,hs,_,_⟩ := ha w h True.intro
    exact ⟨s,hs⟩
  · intro ha w h _
    obtain ⟨s,hs⟩ := ha w h
    refine ⟨s,hs,True.intro,?_⟩
    cases (runPrefix a w h).1 <;> trivial

theorem softirq_projects (ρ : E → Option F)
    {scan : PrefixM E (List PeerId)} {scan' : PrefixM F (List PeerId)}
    {poll : PeerId → Nat → PrefixM E Nat} {poll' : PeerId → Nat → PrefixM F Nat}
    (hs : ProjectsPrefix ρ id scan scan')
    (hp : ∀ pid budget, ProjectsPrefix ρ id (poll pid budget) (poll' pid budget)) :
    ProjectsPrefix ρ id (RxNapi.softirqWith scan poll) (RxNapi.softirqWith scan' poll') := by
  unfold RxNapi.softirqWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | exact hs
    | (poll_source_head poll; exact hp _ _)
    | (poll_source_head runWorkerPrefix; apply runWorkerPrefix_projects ρ)
    | (poll_source_head liftPrefix; exact projectsPrefix_lift ρ _)
    | (poll_source_head Pure.pure; first
        | exact projectsPrefix_pure ρ id _
        | exact projectsPrefix_pure ρ (projectStep id) _)
    | (poll_source_head Bind.bind; first
        | apply projectsPrefix_bind ρ id id
        | apply projectsPrefix_bind ρ id (projectStep id))
    | (poll_source_head ForIn.forIn; apply projectsPrefix_forIn ρ id)
    | apply projectsPrefix_ite
    | maintenance_intro
    | dsimp only [id, projectStep]
    | split

theorem inline_projects (ρ : E → Option F)
    {scan : PrefixM E (List PeerId)} {scan' : PrefixM F (List PeerId)}
    {poll : PeerId → Nat → PrefixM E Nat} {poll' : PeerId → Nat → PrefixM F Nat}
    (hs : ProjectsPrefix ρ id scan scan')
    (hp : ∀ pid budget, ProjectsPrefix ρ id (poll pid budget) (poll' pid budget)) :
    ProjectsPrefix ρ id (RxNapi.inlineWith scan poll) (RxNapi.inlineWith scan' poll') := by
  unfold RxNapi.inlineWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | exact hs
    | (poll_source_head poll; exact hp _ _)
    | (poll_source_head liftPrefix; exact projectsPrefix_lift ρ _)
    | (poll_source_head Pure.pure; first
        | exact projectsPrefix_pure ρ id _
        | exact projectsPrefix_pure ρ (projectStep id) _)
    | (poll_source_head Bind.bind; first
        | apply projectsPrefix_bind ρ id id
        | apply projectsPrefix_bind ρ id (projectStep id))
    | (poll_source_head ForIn.forIn; apply projectsPrefix_forIn ρ id)
    | apply projectsPrefix_ite
    | maintenance_intro
    | dsimp only [id, projectStep]
    | split

theorem irqExit_projects (ρ : E → Option F)
    {scan : PrefixM E Bool} {scan' : PrefixM F Bool}
    {softirq : PrefixM E Unit} {softirq' : PrefixM F Unit}
    (hs : ProjectsPrefix ρ id scan scan') (hp : ProjectsPrefix ρ id softirq softirq') :
    ProjectsPrefix ρ id (RxNapi.irqExitWith scan softirq) (RxNapi.irqExitWith scan' softirq') := by
  unfold RxNapi.irqExitWith
  repeat' first
    | exact hs
    | exact hp
    | (poll_source_head liftPrefix; exact projectsPrefix_lift ρ _)
    | (poll_source_head Pure.pure; first
        | exact projectsPrefix_pure ρ id _
        | exact projectsPrefix_pure ρ (projectStep id) _)
    | (poll_source_head Bind.bind; first
        | apply projectsPrefix_bind ρ id id
        | apply projectsPrefix_bind ρ id (projectStep id))
    | apply projectsPrefix_ite
    | maintenance_intro
    | dsimp only [id]
    | split

theorem softirq_appends {scan : PrefixM E (List PeerId)}
    {poll : PeerId → Nat → PrefixM E Nat} (hs : Appends scan)
    (hp : ∀ pid budget, Appends (poll pid budget)) : Appends (RxNapi.softirqWith scan poll) :=
  (trivial_iff_appends _).mp (RxNapi.softirq_preserves
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi)
    ((trivial_iff_appends _).mpr hs) (fun pid budget => (trivial_iff_appends _).mpr (hp pid budget)))

theorem inline_appends {scan : PrefixM E (List PeerId)}
    {poll : PeerId → Nat → PrefixM E Nat} (hs : Appends scan)
    (hp : ∀ pid budget, Appends (poll pid budget)) : Appends (RxNapi.inlineWith scan poll) :=
  (trivial_iff_appends _).mp (RxNapi.inline_preserves
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi)
    ((trivial_iff_appends _).mpr hs) (fun pid budget => (trivial_iff_appends _).mpr (hp pid budget)))

theorem irqExit_appends {scan : PrefixM E Bool} {softirq : PrefixM E Unit}
    (hs : Appends scan) (hp : Appends softirq) : Appends (RxNapi.irqExitWith scan softirq) :=
  (trivial_iff_appends _).mp (RxNapi.irqExit_preserves
    (fun _ _ hi => hi) (fun _ _ _ _ hi => hi)
    ((trivial_iff_appends _).mpr hs) ((trivial_iff_appends _).mpr hp))

theorem decrypt_projects (ρ : E → Option F)
    {prepare : PrefixM E (Option PeerId)} {prepare' : PrefixM F (Option PeerId)}
    {put : PeerId → PrefixM E Unit} {put' : PeerId → PrefixM F Unit}
    {softirq irq : PrefixM E Unit} {softirq' irq' : PrefixM F Unit}
    (hp : ProjectsPrefix ρ id prepare prepare')
    (hu : ∀ pid, ProjectsPrefix ρ id (put pid) (put' pid))
    (hs : ProjectsPrefix ρ id softirq softirq') (hi : ProjectsPrefix ρ id irq irq') :
    ProjectsPrefix ρ id (RxWorkers.decryptWith prepare put softirq irq)
      (RxWorkers.decryptWith prepare' put' softirq' irq') := by
  unfold RxWorkers.decryptWith
  apply projectsPrefix_bind ρ id id hs
  intro _
  apply projectsPrefix_bind ρ id id hp
  intro peer
  cases peer with
  | none => exact projectsPrefix_pure ρ id false
  | some pid =>
    exact projectsPrefix_bind ρ id id hi (fun _ =>
      projectsPrefix_bind ρ id id (hu pid) (fun _ =>
        projectsPrefix_bind ρ id id hs (fun _ => projectsPrefix_pure ρ id true)))

theorem decrypt_preserves {I : List E → World → Prop} {S : List E → Prop}
    {prepare : PrefixM E (Option PeerId)} {put : PeerId → PrefixM E Unit}
    {softirq irq : PrefixM E Unit} (safe : ∀ h w, I h w → S h)
    (hp : PrefixPreserves I S prepare) (hu : ∀ pid, PrefixPreserves I S (put pid))
    (hs : PrefixPreserves I S softirq) (hi : PrefixPreserves I S irq) :
    PrefixPreserves I S (RxWorkers.decryptWith prepare put softirq irq) := by
  unfold RxWorkers.decryptWith
  apply PrefixPreserves.bind hs
  intro _
  apply PrefixPreserves.bind hp
  intro peer
  cases peer with
  | none => exact PrefixPreserves.pure safe false
  | some pid =>
    exact PrefixPreserves.bind hi (fun _ => PrefixPreserves.bind (hu pid) (fun _ =>
      PrefixPreserves.bind hs (fun _ => PrefixPreserves.pure safe true)))

theorem decrypt_appends {prepare : PrefixM E (Option PeerId)}
    {put : PeerId → PrefixM E Unit} {softirq irq : PrefixM E Unit}
    (hp : Appends prepare) (hu : ∀ pid, Appends (put pid))
    (hs : Appends softirq) (hi : Appends irq) :
    Appends (RxWorkers.decryptWith prepare put softirq irq) :=
  (trivial_iff_appends _).mp (decrypt_preserves (fun _ _ hi => hi)
    ((trivial_iff_appends _).mpr hp) (fun pid => (trivial_iff_appends _).mpr (hu pid))
    ((trivial_iff_appends _).mpr hs) ((trivial_iff_appends _).mpr hi))

theorem decrypt_erases {prepare : PrefixM E (Option PeerId)}
    {put : PeerId → PrefixM E Unit} {softirq irq : PrefixM E Unit}
    {nativeSoftirq nativeIrq : Leanux.M Unit}
    (hp : ErasesPrefix prepare (liftWG RxWorkers.prepareSource))
    (hu : ∀ pid, ErasesPrefix (put pid) (liftWG (peerPut (some pid))))
    (hs : ErasesPrefix softirq nativeSoftirq) (hi : ErasesPrefix irq nativeIrq) :
    ErasesPrefix (RxWorkers.decryptWith prepare put softirq irq)
      (WG.decryptStep nativeSoftirq nativeIrq) := by
  rw [← RxWorkers.decrypt_source]
  unfold RxWorkers.decryptWith RxWorkers.decryptSource
  apply erasesPrefix_bind hs
  intro _
  apply erasesPrefix_bind hp
  intro peer
  cases peer with
  | none => exact erasesPrefix_pure false
  | some pid =>
    exact erasesPrefix_bind hi (fun _ => erasesPrefix_bind (hu pid) (fun _ =>
      erasesPrefix_bind hs (fun _ => erasesPrefix_pure true)))

theorem workerIter_projects (ρ : E → Option F) (worker : Worker) (pid : Option Nat)
    {step after : PrefixM E Bool} {step' after' : PrefixM F Bool}
    (hs : ProjectsPrefix ρ id step step') (ha : ProjectsPrefix ρ id after after') :
    ProjectsPrefix ρ id (workerIterPrefix worker pid step after)
      (workerIterPrefix worker pid step' after') := by
  unfold workerIterPrefix
  apply projectsPrefix_bind ρ id id hs
  intro more
  dsimp only [id]
  apply projectsPrefix_ite
  · intro _
    exact projectsPrefix_pure ρ id _
  · intro _
    exact projectsPrefix_bind ρ id id ha (fun _ => projectsPrefix_pure ρ id _)

theorem workerIter_appends (worker : Worker) (pid : Option Nat)
    {step after : PrefixM E Bool} (hs : Appends step) (ha : Appends after) :
    Appends (workerIterPrefix worker pid step after) :=
  (trivial_iff_appends _).mp (workerIterPrefix_preserves worker pid (fun _ _ hi => hi)
    ((trivial_iff_appends _).mpr hs) ((trivial_iff_appends _).mpr ha))

/-- These factors pin the original saved scans and preparation receipt. They
do not replace those atoms with an unobserved native scan or preparation. -/
theorem softirq_factor : RxHistory.napiSoftirq =
    RxNapi.softirqWith (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix)))
      RxHistory.observePoll := rfl

theorem inline_factor : RxHistory.pollScheduledInline =
    RxNapi.inlineWith (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix)))
      RxHistory.observePoll := rfl

theorem irqExit_factor : RxHistory.napiIrqExit =
    RxNapi.irqExitWith (RxHistory.audit (auditFocus (liftWGObserver RxNapi.scheduledPrefix)))
      RxHistory.napiSoftirq := rfl

theorem decrypt_factor : RxHistory.decryptStep =
    RxWorkers.decryptWith Origins.HistoryAdapters.prepare
      (fun pid => RxHistory.mixed (liftWGObserver (peerPutMixed (some pid))))
      RxHistory.napiSoftirq RxHistory.napiIrqExit := rfl

theorem decryptIteration_factor : RxHistory.decryptIteration =
    workerIterPrefix .decryptWorker none RxHistory.decryptStep
      (do liftPrefix (branch .decWorkerNeedResched (← liftPrefix (Env.condResched .decryptWorker)))) := rfl

end Leanux.Proofs.WG.Queues.NapiSource
