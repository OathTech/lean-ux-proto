import Leanux.Proofs.WG.Queues.SchedulerPreservation
import Leanux.Proofs.WG.Queues.NapiSource
import Leanux.Proofs.WG.Packets.OldRx
import Leanux.Proofs.WG.Packets.TransmitStack

/-! The actual scheduler wired to the transmit journal. Callback-bearing
crypt iterations and NAPI remain explicit; the poll-free transmit worker and
handshake receive iteration use their original observed executions. -/
namespace Leanux.Proofs.WG.TransmitJoint.Scheduler
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps
open RxHistory.SchedulerSource

def tx (pid : PeerId) : PrefixM Event IterResult :=
  oldRx (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker))))

def receive : PrefixM Event IterResult := oldRx Origins.HistoryAdapters.receiveIteration

def ahead (encrypt : PrefixM Event IterResult) (pid : PeerId) : PrefixM Event Unit :=
  cryptAheadWith (fun {_} g => oldRx g) encrypt pid

def iteration (encrypt decrypt : PrefixM Event IterResult) (a : Activation) : PrefixM Event IterResult :=
  iterationWith (fun {_} g => oldRx g) encrypt (ahead encrypt) tx decrypt receive a

def run (encrypt decrypt : PrefixM Event IterResult) (a : Activation) : PrefixM Event Unit :=
  runWith (fun {_} g => oldRx g) (iteration encrypt decrypt) a

def dispatch (encrypt decrypt : PrefixM Event IterResult) (worker : Worker) : PrefixM Event Bool :=
  dispatchWith (fun {_} g => oldRx g) (run encrypt decrypt) worker

def schedule (encrypt decrypt : PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (stack : Option Worker) : PrefixM Event Unit :=
  scheduleWith (fun {_} g => oldRx g) (dispatch encrypt decrypt) (run encrypt decrypt) napi stack

def nested (encrypt decrypt : PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (worker : Worker) : PrefixM Event Unit := nestedWith (schedule encrypt decrypt napi) worker

theorem tx_preserves (initial : FlatTable × FlatTable) (pid : PeerId) :
    PrefixPreserves (Inv initial) (Safe initial) (tx pid) :=
  oldRx_preserves initial _ _
    (RxHistory.mixed_erases (txIterPrefix_erases pid (erasesPrefix_lift _))) (actualTxIter_routing pid)

theorem receive_preserves (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) receive :=
  oldRx_preserves initial _ _ Origins.HistoryAdapters.receiveIteration_erases actualReceiveIter_routing

theorem ahead_preserves (initial : FlatTable × FlatTable) (encrypt : PrefixM Event IterResult)
    (he : PrefixPreserves (Inv initial) (Safe initial) encrypt) (pid : PeerId) :
    PrefixPreserves (Inv initial) (Safe initial) (ahead encrypt pid) :=
  cryptAhead_preserves (fun _ _ hi => hi.safe) _ (transmit_atoms initial) encrypt he pid

theorem iteration_preserves (initial : FlatTable × FlatTable)
    (encrypt decrypt : PrefixM Event IterResult)
    (he : PrefixPreserves (Inv initial) (Safe initial) encrypt)
    (hd : PrefixPreserves (Inv initial) (Safe initial) decrypt) (a : Activation) :
    PrefixPreserves (Inv initial) (Safe initial) (iteration encrypt decrypt a) :=
  RxHistory.SchedulerSource.iteration_preserves _ (transmit_atoms initial) encrypt (ahead encrypt) tx decrypt receive
    he (ahead_preserves initial encrypt he) (tx_preserves initial) hd (receive_preserves initial) a

theorem run_preserves (initial : FlatTable × FlatTable)
    (encrypt decrypt : PrefixM Event IterResult)
    (he : PrefixPreserves (Inv initial) (Safe initial) encrypt)
    (hd : PrefixPreserves (Inv initial) (Safe initial) decrypt) (a : Activation) :
    PrefixPreserves (Inv initial) (Safe initial) (run encrypt decrypt a) :=
  RxHistory.SchedulerSource.run_preserves (fun _ _ hi => hi.safe) Inv.productStore _ (transmit_atoms initial)
    _ (iteration_preserves initial encrypt decrypt he hd) a

theorem dispatch_preserves (initial : FlatTable × FlatTable)
    (encrypt decrypt : PrefixM Event IterResult)
    (he : PrefixPreserves (Inv initial) (Safe initial) encrypt)
    (hd : PrefixPreserves (Inv initial) (Safe initial) decrypt) (worker : Worker) :
    PrefixPreserves (Inv initial) (Safe initial) (dispatch encrypt decrypt worker) :=
  RxHistory.SchedulerSource.dispatch_preserves (fun _ _ hi => hi.safe) Inv.productStore _ (transmit_atoms initial)
    _ (run_preserves initial encrypt decrypt he hd) worker

theorem schedule_preserves (initial : FlatTable × FlatTable)
    (encrypt decrypt : PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (he : PrefixPreserves (Inv initial) (Safe initial) encrypt)
    (hd : PrefixPreserves (Inv initial) (Safe initial) decrypt)
    (hn : PrefixPreserves (Inv initial) (Safe initial) napi) (stack : Option Worker) :
    PrefixPreserves (Inv initial) (Safe initial) (schedule encrypt decrypt napi stack) :=
  RxHistory.SchedulerSource.schedule_preserves (fun _ _ hi => hi.safe) Inv.productStore _ (transmit_atoms initial)
    _ _ napi (dispatch_preserves initial encrypt decrypt he hd) (run_preserves initial encrypt decrypt he hd) hn stack

theorem nested_preserves (initial : FlatTable × FlatTable)
    (encrypt decrypt : PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (he : PrefixPreserves (Inv initial) (Safe initial) encrypt)
    (hd : PrefixPreserves (Inv initial) (Safe initial) decrypt)
    (hn : PrefixPreserves (Inv initial) (Safe initial) napi) (worker : Worker) :
    PrefixPreserves (Inv initial) (Safe initial) (nested encrypt decrypt napi worker) :=
  RxHistory.SchedulerSource.nested_preserves (fun _ _ hi => hi.safe) Inv.productStore _
    (schedule_preserves initial encrypt decrypt napi he hd hn) worker

theorem tx_projects (pid : PeerId) : ProjectsPrefix RxTransmit.globalRx id (tx pid)
    (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  oldRx_projects _ (Appends.focus _ _ _)

theorem receive_projects : ProjectsPrefix RxTransmit.globalRx id receive Origins.HistoryAdapters.receiveIteration :=
  oldRx_projects _ (NapiSource.workerIter_appends _ _ (Appends.focus _ _ _) (Appends.lift _))

theorem ahead_projects (encrypt : PrefixM Event IterResult)
    (he : ProjectsPrefix RxTransmit.globalRx id encrypt RxHistory.encryptIteration) (pid : PeerId) :
    ProjectsPrefix RxTransmit.globalRx id (ahead encrypt pid) (RxHistory.cryptAhead pid) :=
  cryptAhead_projects RxTransmit.globalRx _ (fun {_} g => g) (fun g ha => oldRx_projects g ha)
    _ _ he pid

theorem iteration_projects (encrypt decrypt : PrefixM Event IterResult)
    (he : ProjectsPrefix RxTransmit.globalRx id encrypt RxHistory.encryptIteration)
    (hd : ProjectsPrefix RxTransmit.globalRx id decrypt RxHistory.decryptIteration) (a : Activation) :
    ProjectsPrefix RxTransmit.globalRx id (iteration encrypt decrypt a) (RxHistory.activationIteration a) :=
  RxHistory.SchedulerSource.iteration_projects RxTransmit.globalRx _ (fun {_} g => g)
    (fun g ha => oldRx_projects g ha) _ _ _ _ _ _ _ _ _ _ he (ahead_projects encrypt he)
    tx_projects hd receive_projects a

theorem run_projects (encrypt decrypt : PrefixM Event IterResult)
    (he : ProjectsPrefix RxTransmit.globalRx id encrypt RxHistory.encryptIteration)
    (hd : ProjectsPrefix RxTransmit.globalRx id decrypt RxHistory.decryptIteration) (a : Activation) :
    ProjectsPrefix RxTransmit.globalRx id (run encrypt decrypt a) (RxHistory.activationRun a) :=
  RxHistory.SchedulerSource.run_projects RxTransmit.globalRx _ (fun {_} g => g)
    (fun g ha => oldRx_projects g ha) _ _ (iteration_projects encrypt decrypt he hd) a

theorem dispatch_projects (encrypt decrypt : PrefixM Event IterResult)
    (he : ProjectsPrefix RxTransmit.globalRx id encrypt RxHistory.encryptIteration)
    (hd : ProjectsPrefix RxTransmit.globalRx id decrypt RxHistory.decryptIteration) (worker : Worker) :
    ProjectsPrefix RxTransmit.globalRx id (dispatch encrypt decrypt worker) (RxHistory.dispatch worker) :=
  RxHistory.SchedulerSource.dispatch_projects RxTransmit.globalRx _ (fun {_} g => g)
    (fun g ha => oldRx_projects g ha) _ _ (run_projects encrypt decrypt he hd) worker

theorem schedule_projects (encrypt decrypt : PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (he : ProjectsPrefix RxTransmit.globalRx id encrypt RxHistory.encryptIteration)
    (hd : ProjectsPrefix RxTransmit.globalRx id decrypt RxHistory.decryptIteration)
    (hn : ProjectsPrefix RxTransmit.globalRx id napi RxHistory.napiSoftirq) (stack : Option Worker) :
    ProjectsPrefix RxTransmit.globalRx id (schedule encrypt decrypt napi stack) (RxHistory.schedule stack) :=
  RxHistory.SchedulerSource.schedule_projects RxTransmit.globalRx _ (fun {_} g => g)
    (fun g ha => oldRx_projects g ha) _ _ _ _ _ _ (dispatch_projects encrypt decrypt he hd)
    (run_projects encrypt decrypt he hd) hn stack

theorem nested_projects (encrypt decrypt : PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (he : ProjectsPrefix RxTransmit.globalRx id encrypt RxHistory.encryptIteration)
    (hd : ProjectsPrefix RxTransmit.globalRx id decrypt RxHistory.decryptIteration)
    (hn : ProjectsPrefix RxTransmit.globalRx id napi RxHistory.napiSoftirq) (worker : Worker) :
    ProjectsPrefix RxTransmit.globalRx id (nested encrypt decrypt napi worker) (RxHistory.nestedResched worker) :=
  RxHistory.SchedulerSource.nested_projects RxTransmit.globalRx _ _
    (schedule_projects encrypt decrypt napi he hd hn) worker

theorem tx_appends (pid : PeerId) : Appends (tx pid) := oldRx_appends _
theorem receive_appends : Appends receive := oldRx_appends _

theorem ahead_appends (encrypt : PrefixM Event IterResult) (he : Appends encrypt) (pid : PeerId) :
    Appends (ahead encrypt pid) :=
  cryptAhead_appends _ (fun g _ => oldRx_appends g) encrypt he pid

theorem iteration_appends (encrypt decrypt : PrefixM Event IterResult)
    (he : Appends encrypt) (hd : Appends decrypt) (a : Activation) :
    Appends (iteration encrypt decrypt a) :=
  RxHistory.SchedulerSource.iteration_appends _ (fun g _ => oldRx_appends g)
    encrypt (ahead encrypt) tx decrypt receive he (ahead_appends encrypt he) tx_appends hd receive_appends a

theorem run_appends (encrypt decrypt : PrefixM Event IterResult)
    (he : Appends encrypt) (hd : Appends decrypt) (a : Activation) :
    Appends (run encrypt decrypt a) :=
  RxHistory.SchedulerSource.run_appends _ (fun g _ => oldRx_appends g)
    _ (iteration_appends encrypt decrypt he hd) a

theorem dispatch_appends (encrypt decrypt : PrefixM Event IterResult)
    (he : Appends encrypt) (hd : Appends decrypt) (worker : Worker) :
    Appends (dispatch encrypt decrypt worker) :=
  RxHistory.SchedulerSource.dispatch_appends _ (fun g _ => oldRx_appends g)
    _ (run_appends encrypt decrypt he hd) worker

theorem schedule_appends (encrypt decrypt : PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (he : Appends encrypt) (hd : Appends decrypt) (hn : Appends napi) (stack : Option Worker) :
    Appends (schedule encrypt decrypt napi stack) :=
  RxHistory.SchedulerSource.schedule_appends _ (fun g _ => oldRx_appends g)
    _ _ napi (dispatch_appends encrypt decrypt he hd) (run_appends encrypt decrypt he hd) hn stack

theorem nested_appends (encrypt decrypt : PrefixM Event IterResult) (napi : PrefixM Event Unit)
    (he : Appends encrypt) (hd : Appends decrypt) (hn : Appends napi) (worker : Worker) :
    Appends (nested encrypt decrypt napi worker) :=
  RxHistory.SchedulerSource.nested_appends _ (schedule_appends encrypt decrypt napi he hd hn) worker

end Leanux.Proofs.WG.TransmitJoint.Scheduler
