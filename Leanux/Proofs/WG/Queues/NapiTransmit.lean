import Leanux.Proofs.WG.Queues.NapiObservers
import Leanux.Proofs.WG.Queues.RxTransmitObserved

/-! Closed actual NAPI and crypt callbacks use the checked local transmit poll.
No caller or initialized-run premise is supplied at this boundary. -/
namespace Leanux.Proofs.WG.TransmitJoint.Napi
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues AllowedIps

def softirq : PrefixM Event Unit := softirqWith RxTransmit.observePoll

def inline : PrefixM Event Unit := inlineWith RxTransmit.observePoll

def irqExit : PrefixM Event Unit := irqExitWith RxTransmit.observePoll

def decrypt : PrefixM Event Bool := decryptWith RxTransmit.observePoll

def decryptIteration : PrefixM Event IterResult := decryptIterationWith RxTransmit.observePoll

def encryptIteration : PrefixM Event IterResult := encryptIterationWith RxTransmit.observePoll

theorem softirq_rx : ProjectsPrefix RxTransmit.globalRx id softirq RxHistory.napiSoftirq :=
  softirq_projects RxTransmit.observePoll_rx

theorem softirq_append : Appends softirq := softirq_appends RxTransmit.observePoll_appends

theorem softirq_source : ErasesPrefix softirq Env.napiSoftirq :=
  softirq_erases RxTransmit.observePoll_rx

theorem softirq_checked (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) softirq :=
  softirq_preserves initial (RxTransmit.observePoll_preserves initial)

theorem inline_rx : ProjectsPrefix RxTransmit.globalRx id inline RxHistory.pollScheduledInline :=
  inline_projects RxTransmit.observePoll_rx

theorem inline_append : Appends inline := inline_appends RxTransmit.observePoll_appends

theorem inline_source : ErasesPrefix inline Env.pollScheduledInline :=
  inline_erases RxTransmit.observePoll_rx

theorem inline_checked (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) inline :=
  inline_preserves initial (RxTransmit.observePoll_preserves initial)

theorem irqExit_rx : ProjectsPrefix RxTransmit.globalRx id irqExit RxHistory.napiIrqExit :=
  irqExit_projects RxTransmit.observePoll_rx

theorem irqExit_append : Appends irqExit := irqExit_appends RxTransmit.observePoll_appends

theorem irqExit_source : ErasesPrefix irqExit Env.napiIrqExit :=
  irqExit_erases RxTransmit.observePoll_rx

theorem irqExit_checked (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) irqExit :=
  irqExit_preserves initial (RxTransmit.observePoll_preserves initial)

theorem decrypt_rx : ProjectsPrefix RxTransmit.globalRx id decrypt RxHistory.decryptStep :=
  decrypt_projects RxTransmit.observePoll_rx

theorem decrypt_append : Appends decrypt := decrypt_appends RxTransmit.observePoll_appends

theorem decrypt_source : ErasesPrefix decrypt (WG.decryptStep Env.napiSoftirq Env.napiIrqExit) :=
  decrypt_erases RxTransmit.observePoll_rx

theorem decrypt_checked (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) decrypt :=
  decrypt_preserves initial (RxTransmit.observePoll_preserves initial)

theorem decryptIteration_rx : ProjectsPrefix RxTransmit.globalRx id decryptIteration RxHistory.decryptIteration :=
  decryptIteration_projects RxTransmit.observePoll_rx

theorem decryptIteration_append : Appends decryptIteration := decryptIteration_appends RxTransmit.observePoll_appends

theorem decryptIteration_source : ErasesPrefix decryptIteration (WG.decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) :=
  decryptIteration_erases RxTransmit.observePoll_rx

theorem decryptIteration_checked (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) decryptIteration :=
  decryptIteration_preserves initial (RxTransmit.observePoll_preserves initial)

theorem encryptIteration_rx : ProjectsPrefix RxTransmit.globalRx id encryptIteration RxHistory.encryptIteration :=
  encryptIteration_projects RxTransmit.observePoll_rx

theorem encryptIteration_append : Appends encryptIteration := encryptIteration_appends RxTransmit.observePoll_appends

theorem encryptIteration_source : ErasesPrefix encryptIteration (WG.encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) :=
  encryptIteration_erases RxTransmit.observePoll_rx

theorem encryptIteration_checked (initial : FlatTable × FlatTable) :
    PrefixPreserves (Inv initial) (Safe initial) encryptIteration :=
  encryptIteration_preserves initial (RxTransmit.observePoll_preserves initial)

end Leanux.Proofs.WG.TransmitJoint.Napi
