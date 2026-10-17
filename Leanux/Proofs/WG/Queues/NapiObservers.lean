import Leanux.Proofs.WG.Packets.OldRx
import Leanux.Proofs.WG.Packets.TransmitStack
import Leanux.Proofs.WG.Queues.NapiSource
import Leanux.Proofs.WG.Configuration.RoutingCallers

/-! Actual saved NAPI scans and crypt-worker callbacks with one replaceable
observed poll. The encryption item is consumed and installed before NAPI;
the saved item is then passed to the unchanged encryption tail. -/
namespace Leanux.Proofs.WG.TransmitJoint.Napi
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps

abbrev Poll := PeerId → Nat → PrefixM Event Nat

def softirqWith (poll : Poll) : PrefixM Event Unit :=
  RxNapi.softirqWith (oldRx (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix)))) poll

def inlineWith (poll : Poll) : PrefixM Event Unit :=
  RxNapi.inlineWith (oldRx (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix)))) poll

def irqExitWith (poll : Poll) : PrefixM Event Unit :=
  RxNapi.irqExitWith (oldRx (RxHistory.audit (auditFocus (liftWGObserver RxNapi.scheduledPrefix))))
    (softirqWith poll)

def decryptWith (poll : Poll) : PrefixM Event Bool :=
  RxWorkers.decryptWith (oldRx Origins.HistoryAdapters.prepare)
    (fun pid => oldRx (RxHistory.mixed (liftWGObserver (peerPutMixed (some pid)))))
    (softirqWith poll) (irqExitWith poll)

def decryptIterationWith (poll : Poll) : PrefixM Event IterResult :=
  workerIterPrefix .decryptWorker none (decryptWith poll)
    (do liftPrefix (branch .decWorkerNeedResched (← liftPrefix (Env.condResched .decryptWorker))))

def encryptIterationWith (poll : Poll) : PrefixM Event IterResult := do
  let item ← oldRx (RxHistory.mixed (liftWGObserver (liftWGPrefix TxRing.pollSource)))
  softirqWith poll
  oldRx (RxHistory.mixed (RxWorkers.encryptTail item))

variable {poll : Poll}

theorem softirq_projects
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ProjectsPrefix RxTransmit.globalRx id (softirqWith poll) RxHistory.napiSoftirq :=
  NapiSource.softirq_projects _ (oldRx_projects _ (Appends.focus _ _ _)) hp

theorem inline_projects
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ProjectsPrefix RxTransmit.globalRx id (inlineWith poll) RxHistory.pollScheduledInline :=
  NapiSource.inline_projects _ (oldRx_projects _ (Appends.focus _ _ _)) hp

theorem irqExit_projects
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ProjectsPrefix RxTransmit.globalRx id (irqExitWith poll) RxHistory.napiIrqExit :=
  NapiSource.irqExit_projects _ (oldRx_projects _ (Appends.focus _ _ _)) (softirq_projects hp)

theorem decrypt_projects
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ProjectsPrefix RxTransmit.globalRx id (decryptWith poll) RxHistory.decryptStep :=
  NapiSource.decrypt_projects _ (oldRx_projects _ (Appends.focus _ _ _))
    (fun _ => oldRx_projects _ (Appends.focus _ _ _)) (softirq_projects hp) (irqExit_projects hp)

theorem decryptIteration_projects
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ProjectsPrefix RxTransmit.globalRx id (decryptIterationWith poll) RxHistory.decryptIteration :=
  NapiSource.workerIter_projects _ _ _ (decrypt_projects hp)
    (projectsPrefix_bind _ id id (projectsPrefix_lift _ _) (fun _ => projectsPrefix_lift _ _))

theorem encryptIteration_projects
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ProjectsPrefix RxTransmit.globalRx id (encryptIterationWith poll) RxHistory.encryptIteration :=
  projectsPrefix_bind _ id id (oldRx_projects _ (Appends.focus _ _ _)) (fun _ =>
    projectsPrefix_bind _ id id (softirq_projects hp) (fun _ => oldRx_projects _ (Appends.focus _ _ _)))

theorem softirq_appends (hp : ∀ pid budget, Appends (poll pid budget)) : Appends (softirqWith poll) :=
  NapiSource.softirq_appends (oldRx_appends _) hp

theorem inline_appends (hp : ∀ pid budget, Appends (poll pid budget)) : Appends (inlineWith poll) :=
  NapiSource.inline_appends (oldRx_appends _) hp

theorem irqExit_appends (hp : ∀ pid budget, Appends (poll pid budget)) : Appends (irqExitWith poll) :=
  NapiSource.irqExit_appends (oldRx_appends _) (softirq_appends hp)

theorem decrypt_appends (hp : ∀ pid budget, Appends (poll pid budget)) : Appends (decryptWith poll) :=
  NapiSource.decrypt_appends (oldRx_appends _) (fun _ => oldRx_appends _)
    (softirq_appends hp) (irqExit_appends hp)

theorem decryptIteration_appends (hp : ∀ pid budget, Appends (poll pid budget)) : Appends (decryptIterationWith poll) :=
  NapiSource.workerIter_appends _ _ (decrypt_appends hp) (Appends.bind (Appends.lift _) (fun _ => Appends.lift _))

theorem encryptIteration_appends (hp : ∀ pid budget, Appends (poll pid budget)) : Appends (encryptIterationWith poll) :=
  Appends.bind (oldRx_appends _) (fun _ => Appends.bind (softirq_appends hp) (fun _ => oldRx_appends _))

private theorem projected_erases {g : PrefixM Event α} {lower : RxHistory.Obs α} {a : Leanux.M α}
    (project : ProjectsPrefix RxTransmit.globalRx id g lower) (erase : ErasesPrefix lower a) :
    ErasesPrefix g a := by
  intro w h
  have same := (congrArg Prod.fst (project w h)).symm.trans (erase w (h.filterMap RxTransmit.globalRx))
  cases result : (runPrefix g w h).1 <;> simpa only [result,Except.map,id_eq] using same

theorem softirq_erases
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ErasesPrefix (softirqWith poll) Env.napiSoftirq := projected_erases (softirq_projects hp) RxHistory.napiSoftirq_erases

theorem inline_erases
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ErasesPrefix (inlineWith poll) Env.pollScheduledInline := projected_erases (inline_projects hp) RxHistory.pollScheduledInline_erases

theorem irqExit_erases
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ErasesPrefix (irqExitWith poll) Env.napiIrqExit := projected_erases (irqExit_projects hp) RxHistory.napiIrqExit_erases

theorem decrypt_erases
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ErasesPrefix (decryptWith poll) (WG.decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  projected_erases (decrypt_projects hp) RxHistory.decryptStep_erases

theorem decryptIteration_erases
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ErasesPrefix (decryptIterationWith poll) (WG.decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  projected_erases (decryptIteration_projects hp) RxHistory.decryptIteration_erases

theorem encryptIteration_erases
    (hp : ∀ pid budget, ProjectsPrefix RxTransmit.globalRx id (poll pid budget) (RxHistory.observePoll pid budget)) :
    ErasesPrefix (encryptIterationWith poll) (WG.encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
  projected_erases (encryptIteration_projects hp) RxHistory.encryptIteration_erases

private theorem pending_preserves (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial)
      (oldRx (RxHistory.audit (auditFocus (liftWGObserver RxNapi.pendingPrefix)))) := by
  apply oldRx_preserves initial _ _
    (RxHistory.audit_erases (auditFocus_erases (liftWGObserver_erases RxNapi.pending_erases)))
  apply RetainsRoutingCall.liftWG
  apply ProjectedRetainsRoutingCall.of_same
  routing_handshake_source [RxNapi.pendingSource] using []

private theorem scheduled_preserves (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial)
      (oldRx (RxHistory.audit (auditFocus (liftWGObserver RxNapi.scheduledPrefix)))) := by
  apply oldRx_preserves initial _ _
    (RxHistory.audit_erases (auditFocus_erases (liftWGObserver_erases RxNapi.scheduled_erases)))
  apply RetainsRoutingCall.liftWG
  apply ProjectedRetainsRoutingCall.of_same
  routing_handshake_source [RxNapi.scheduledSource] using []

theorem softirq_preserves (initial : FlatTable × FlatTable)
    (hp : ∀ pid budget, PrefixPreserves (Inv initial) (Safe initial) (poll pid budget)) :
    PrefixPreserves (Inv initial) (Safe initial) (softirqWith poll) :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.safe) Inv.productStore (pending_preserves initial) hp

theorem inline_preserves (initial : FlatTable × FlatTable)
    (hp : ∀ pid budget, PrefixPreserves (Inv initial) (Safe initial) (poll pid budget)) :
    PrefixPreserves (Inv initial) (Safe initial) (inlineWith poll) :=
  RxNapi.inline_preserves (fun _ _ hi => hi.safe) Inv.productStore (pending_preserves initial) hp

theorem irqExit_preserves (initial : FlatTable × FlatTable)
    (hp : ∀ pid budget, PrefixPreserves (Inv initial) (Safe initial) (poll pid budget)) :
    PrefixPreserves (Inv initial) (Safe initial) (irqExitWith poll) :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.safe) Inv.productStore
    (scheduled_preserves initial) (softirq_preserves initial hp)

theorem decrypt_preserves (initial : FlatTable × FlatTable)
    (hp : ∀ pid budget, PrefixPreserves (Inv initial) (Safe initial) (poll pid budget)) :
    PrefixPreserves (Inv initial) (Safe initial) (decryptWith poll) := by
  apply NapiSource.decrypt_preserves (fun _ _ hi => hi.safe)
  · exact oldRx_preserves initial _ _ Origins.HistoryAdapters.prepare_erases
      (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same
        (pinned_const _private.Leanux.Proofs.WG.Configuration.RoutingCallers.«0».Leanux.Proofs.WG.RoutingPosition.Callers.prepare_routing)))
  · intro pid
    exact oldRx_preserves initial _ _ (RxHistory.mixed_erases (liftWGObserver_erases (peerPutMixed_erases _)))
      (RetainsRoutingCall.liftWG (peerPut_retainsRouting _))
  · exact softirq_preserves initial hp
  · exact irqExit_preserves initial hp

theorem decryptIteration_preserves (initial : FlatTable × FlatTable)
    (hp : ∀ pid budget, PrefixPreserves (Inv initial) (Safe initial) (poll pid budget)) :
    PrefixPreserves (Inv initial) (Safe initial) (decryptIterationWith poll) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) (decrypt_preserves initial hp)
    (PrefixPreserves.bind
      (viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe) Inv.productStore (condResched_sameKernel _))
      (fun _ => viewLiftPrefix_preserves productStoreView (fun _ _ hi => hi.safe) Inv.productStore
        (by intro initial; exact productAmbient_spec (AmbientM.branch _ _) _ (fun _ _ hi => hi))))

theorem encryptIteration_preserves (initial : FlatTable × FlatTable)
    (hp : ∀ pid budget, PrefixPreserves (Inv initial) (Safe initial) (poll pid budget)) :
    PrefixPreserves (Inv initial) (Safe initial) (encryptIterationWith poll) := by
  apply PrefixPreserves.bind (oldRx_preserves initial _ _
    (RxHistory.mixed_erases (liftWGObserver_erases (erasesStatePrefix_lift _)))
    (RetainsRoutingCall.liftWG (ProjectedRetainsRoutingCall.of_same
      (pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingTxFrames.«0».Leanux.Proofs.WG.AllowedIps.encryptPoll_routing))))
  intro item
  apply PrefixPreserves.bind (softirq_preserves initial hp)
  intro _
  exact oldRx_preserves initial _ _ (RxHistory.mixed_erases (RxWorkers.encryptTail_erases item))
    ((pinned_const _private.Leanux.Proofs.WG.Configuration.RoutingCallers.«0».Leanux.Proofs.WG.RoutingPosition.Callers.encryptTail_routing) item)

end Leanux.Proofs.WG.TransmitJoint.Napi
