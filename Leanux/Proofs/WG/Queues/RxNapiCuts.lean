import Leanux.Proofs.Logged.FocusComposition
import Leanux.Proofs.WG.Lifetimes.EnvTrafficAudit

/-! Literal direct-NAPI caller cuts. The saved-map scan finishes before any
poll can mutate resident peers; the IRQ predicate retains its short circuit. -/
namespace Leanux.Proofs.WG.Queues.RxNapi
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def pendingSource : WG.M (List PeerId) := do
  let d ← getDev
  return d.peers.toList.filterMap fun (pid, p) => if p.napiScheduled then some pid else none

def pendingPrefix : MixedM (List PeerId) := do
  let d ← liftWGPrefix getDev
  savedPeerFilterMap (fun pid p => if p.napiScheduled then some pid else none) d.peers.toList

def scheduledSource : WG.M Bool := do
  return (← getDev).peers.toList.any (·.2.napiScheduled)

def scheduledPrefix : MixedM Bool := do
  let d ← liftWGPrefix getDev
  savedPeerAny (·.napiScheduled) d.peers.toList

theorem pending_erases : ErasesStatePrefix pendingPrefix pendingSource := by
  unfold pendingPrefix pendingSource
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro d
  exact savedPeerFilterMap_erases _ _

theorem scheduled_erases : ErasesStatePrefix scheduledPrefix scheduledSource := by
  unfold scheduledPrefix scheduledSource
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro d
  exact savedPeerAny_erases _ _

theorem pending_preserves : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe pendingPrefix := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  unfold pendingPrefix
  exact StatePrefixEnsures.bind (getDev_saved_spec allocationAmbient (fun _ => True))
    (fun d => savedPeerFilterMap_spec allocationAmbient (fun _ => True) _ _)

theorem scheduled_preserves : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe scheduledPrefix := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  unfold scheduledPrefix
  exact StatePrefixEnsures.bind (getDev_saved_spec allocationAmbient (fun _ => True))
    (fun d => savedPeerAny_spec allocationAmbient (fun _ => True) _ _)

def softirqWith (scan : PrefixM E (List PeerId)) (poll : PeerId → Nat → PrefixM E Nat) : PrefixM E Unit := do
  let pending ← scan
  if pending.isEmpty then return
  if (← liftPrefix getAmbient).hidden.isSome && (← liftPrefix peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  if pending.length > 1 then liftPrefix (unsupported "NAPI polls of several peers in one softirq")
  runWorkerPrefix .netRx do
    for pid in pending do
      discard <| poll pid NAPI_POLL_WEIGHT

def inlineWith (scan : PrefixM E (List PeerId)) (poll : PeerId → Nat → PrefixM E Nat) : PrefixM E Unit := do
  let pending ← scan
  if pending.length > 1 then liftPrefix (unsupported "NAPI polls of several peers in one softirq")
  for pid in pending do
    discard <| poll pid NAPI_POLL_WEIGHT

def irqExitWith (scan : PrefixM E Bool) (softirq : PrefixM E Unit) : PrefixM E Unit := do
  if (← liftPrefix getAmbient).hidden.isNone then return
  if !(← scan) then return
  if (← liftPrefix peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  let here ← liftPrefix chooseNapiHere
  if here then softirq

theorem softirq_cut : softirqWith (liftWGObserver pendingPrefix) rxPollStackPrefix = napiSoftirqPrefix := by
  simp only [softirqWith, pendingPrefix, napiSoftirqPrefix, liftWGObserver_bind, bind_assoc]

theorem inline_cut : inlineWith (liftWGObserver pendingPrefix) rxPollStackPrefix = pollScheduledInlinePrefix := by
  simp only [inlineWith, pendingPrefix, pollScheduledInlinePrefix, liftWGObserver_bind, bind_assoc]

theorem irqExit_cut : irqExitWith (liftWGObserver scheduledPrefix) napiSoftirqPrefix = napiIrqExitPrefix := by
  simp only [irqExitWith, scheduledPrefix, napiIrqExitPrefix, liftWGObserver_bind, bind_assoc]

def softirqSource : Leanux.M Unit := do
  let pending ← liftWG pendingSource
  if pending.isEmpty then return
  if (← getAmbient).hidden.isSome && (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  if pending.length > 1 then unsupported "NAPI polls of several peers in one softirq"
  Leanux.Env.runWorker .netRx do
    for pid in pending do
      discard <| rxPoll pid NAPI_POLL_WEIGHT (fun pkts => pkts.forM Leanux.Env.deliverInner)

def inlineSource : Leanux.M Unit := do
  let pending ← liftWG pendingSource
  if pending.length > 1 then unsupported "NAPI polls of several peers in one softirq"
  for pid in pending do
    discard <| rxPoll pid NAPI_POLL_WEIGHT (fun pkts => pkts.forM Leanux.Env.deliverInner)

def irqExitSource : Leanux.M Unit := do
  if (← getAmbient).hidden.isNone then return
  if !(← liftWG scheduledSource) then return
  if (← peekHiddenSite) != some (HiddenSite.sectionStart .netRx).info.id then return
  let here ← chooseNapiHere
  if here then Leanux.Env.napiSoftirq

theorem softirqSource_eq : softirqSource = Leanux.Env.napiSoftirq := by
  simp only [softirqSource, pendingSource, Leanux.Env.napiSoftirq, liftWG_bind, liftWG_pure, bind_assoc, pure_bind]
  rfl

theorem inlineSource_eq : inlineSource = Leanux.Env.pollScheduledInline := by
  simp only [inlineSource, pendingSource, Leanux.Env.pollScheduledInline, liftWG_bind, liftWG_pure, bind_assoc, pure_bind]
  rfl

theorem irqExitSource_eq : irqExitSource = Leanux.Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  simp only [irqExitSource, scheduledSource, napiIrqExitSource, liftWG_bind, liftWG_pure, bind_assoc, pure_bind]
  rfl

macro "napi_erasure" : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only))

theorem softirq_erases (hs : ErasesPrefix scan (liftWG pendingSource))
    (hp : ∀ pid budget, ErasesPrefix (poll pid budget)
      (rxPoll pid budget (fun pkts => pkts.forM Leanux.Env.deliverInner))) :
    ErasesPrefix (softirqWith scan poll) Leanux.Env.napiSoftirq := by
  rw [← softirqSource_eq]
  unfold softirqWith softirqSource
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first | with_reducible exact hp _ _ | napi_erasure

theorem inline_erases (hs : ErasesPrefix scan (liftWG pendingSource))
    (hp : ∀ pid budget, ErasesPrefix (poll pid budget)
      (rxPoll pid budget (fun pkts => pkts.forM Leanux.Env.deliverInner))) :
    ErasesPrefix (inlineWith scan poll) Leanux.Env.pollScheduledInline := by
  rw [← inlineSource_eq]
  unfold inlineWith inlineSource
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first | with_reducible exact hp _ _ | napi_erasure

theorem irqExit_erases (hs : ErasesPrefix scan (liftWG scheduledSource))
    (hp : ErasesPrefix softirq Leanux.Env.napiSoftirq) :
    ErasesPrefix (irqExitWith scan softirq) Leanux.Env.napiIrqExit := by
  rw [← irqExitSource_eq]
  unfold irqExitWith irqExitSource
  napi_erasure

macro "napi_store" safe:ident store:ident : tactic => `(tactic|
  first
    | (traffic_head chooseNapiHere; exact viewLiftPrefix_preserves productStoreView $safe $store (by
        apply (ProjectedAction.iff_run _ _ _).mpr
        intro w x v hr
        cases hr
        rfl))
    | ((first | traffic_head getAmbient | traffic_head hidden | traffic_head modifyAmbient |
          traffic_head peekHiddenSite | traffic_head unsupported | traffic_head invariant);
        exact viewLiftPrefix_preserves productStoreView $safe $store
          (by intro initial; exact productAmbient_spec _ _ (fun _ _ hi => hi))))

macro "napi_preservation" safe:ident kernel:ident hp:ident : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible exact $hp _ _
    | with_reducible apply runWorkerPrefix_preserves $safe $kernel
    | napi_store $safe $kernel
    | with_reducible exact PrefixPreserves.pure $safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ $safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro z; try dsimp only))

theorem softirq_preserves (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hs : PrefixPreserves I S scan) (hp : ∀ pid budget, PrefixPreserves I S (poll pid budget)) :
    PrefixPreserves I S (softirqWith scan poll) := by
  unfold softirqWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  napi_preservation safe kernel hp

theorem inline_preserves (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hs : PrefixPreserves I S scan) (hp : ∀ pid budget, PrefixPreserves I S (poll pid budget)) :
    PrefixPreserves I S (inlineWith scan poll) := by
  unfold inlineWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  napi_preservation safe kernel hp

theorem irqExit_preserves (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hs : PrefixPreserves I S scan) (hp : PrefixPreserves I S softirq) :
    PrefixPreserves I S (irqExitWith scan softirq) := by
  unfold irqExitWith
  napi_preservation safe kernel hp

macro "napi_focus" hd:ident safe:ident kernel:ident hp:ident fp:ident : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible exact $fp _ _
    | with_reducible exact $hp _ _
    | with_reducible exact FocusesUnder.lift _
    | with_reducible exact FocusesUnder.pure _
    | with_reducible apply FocusesUnder.forIn $hd
    | with_reducible apply FocusesUnder.bind $hd
    | napi_store $safe $kernel
    | with_reducible exact PrefixPreserves.pure $safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ $safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro z; try dsimp only))


theorem worker_focus (hd : ∀ e, decode (encode e) = some e)
    (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (worker : Worker) (hp : PrefixPreserves I S body)
    (fp : FocusesUnder I encode decode gbody body) :
    FocusesUnder I encode decode (runWorkerPrefix worker gbody) (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  napi_focus hd safe kernel hp fp

theorem softirq_focus (hd : ∀ e, decode (encode e) = some e)
    (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hs : PrefixPreserves I S scan) (hp : ∀ pid budget, PrefixPreserves I S (poll pid budget))
    (fs : FocusesUnder I encode decode gscan scan)
    (fp : ∀ pid budget, FocusesUnder I encode decode (gpoll pid budget) (poll pid budget)) :
    FocusesUnder I encode decode (softirqWith gscan gpoll) (softirqWith scan poll) := by
  unfold softirqWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | with_reducible apply worker_focus hd safe kernel
    | with_reducible apply runWorkerPrefix_preserves safe kernel
    | napi_focus hd safe kernel hp fp

theorem inline_focus (hd : ∀ e, decode (encode e) = some e)
    (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hs : PrefixPreserves I S scan) (hp : ∀ pid budget, PrefixPreserves I S (poll pid budget))
    (fs : FocusesUnder I encode decode gscan scan)
    (fp : ∀ pid budget, FocusesUnder I encode decode (gpoll pid budget) (poll pid budget)) :
    FocusesUnder I encode decode (inlineWith gscan gpoll) (inlineWith scan poll) := by
  unfold inlineWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  napi_focus hd safe kernel hp fp

theorem irqExit_focus (hd : ∀ e, decode (encode e) = some e)
    (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hs : PrefixPreserves I S scan) (hp : PrefixPreserves I S softirq)
    (fs : FocusesUnder I encode decode gscan scan)
    (fp : FocusesUnder I encode decode gsoftirq softirq) :
    FocusesUnder I encode decode (irqExitWith gscan gsoftirq) (irqExitWith scan softirq) := by
  unfold irqExitWith
  napi_focus hd safe kernel hp fp

macro "napi_projects" projection:ident safe:ident kernel:ident hp:ident pp:ident : tactic => `(tactic|
  repeat' first
    | assumption
    | with_reducible exact $pp _ _
    | with_reducible exact $hp _ _
    | with_reducible exact projectsUnder_lift $projection _
    | with_reducible exact projectsUnder_pure $projection _
    | with_reducible apply projectsUnder_forIn
    | with_reducible apply projectsUnder_bind
    | napi_store $safe $kernel
    | with_reducible exact PrefixPreserves.pure $safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ $safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro z; try dsimp only))

theorem worker_projects (ρ : E → Option F)
    (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (worker : Worker) (hp : PrefixPreserves I S body)
    (pp : ProjectsUnder I ρ gbody body) :
    ProjectsUnder I ρ (runWorkerPrefix worker gbody) (runWorkerPrefix worker body) := by
  unfold runWorkerPrefix
  napi_projects ρ safe kernel hp pp

theorem softirq_projects (ρ : E → Option F)
    (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hs : PrefixPreserves I S scan) (hp : ∀ pid budget, PrefixPreserves I S (poll pid budget))
    (ps : ProjectsUnder I ρ gscan scan)
    (pp : ∀ pid budget, ProjectsUnder I ρ (gpoll pid budget) (poll pid budget)) :
    ProjectsUnder I ρ (softirqWith gscan gpoll) (softirqWith scan poll) := by
  unfold softirqWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | with_reducible apply worker_projects ρ safe kernel
    | with_reducible apply runWorkerPrefix_preserves safe kernel
    | napi_projects ρ safe kernel hp pp

theorem inline_projects (ρ : E → Option F)
    (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hs : PrefixPreserves I S scan) (hp : ∀ pid budget, PrefixPreserves I S (poll pid budget))
    (ps : ProjectsUnder I ρ gscan scan)
    (pp : ∀ pid budget, ProjectsUnder I ρ (gpoll pid budget) (poll pid budget)) :
    ProjectsUnder I ρ (inlineWith gscan gpoll) (inlineWith scan poll) := by
  unfold inlineWith
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  napi_projects ρ safe kernel hp pp

theorem irqExit_projects (ρ : E → Option F)
    (safe : ∀ h w, I h w → S h)
    (kernel : ∀ h w v, productStoreView v = productStoreView w → I h w → I h v)
    (hs : PrefixPreserves I S scan) (_hp : PrefixPreserves I S softirq)
    (ps : ProjectsUnder I ρ gscan scan)
    (pp : ProjectsUnder I ρ gsoftirq softirq) :
    ProjectsUnder I ρ (irqExitWith gscan gsoftirq) (irqExitWith scan softirq) := by
  unfold irqExitWith
  napi_projects ρ safe kernel _hp pp

end Leanux.Proofs.WG.Queues.RxNapi
