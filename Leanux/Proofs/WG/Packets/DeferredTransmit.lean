import Leanux.Proofs.WG.Queues.DeferredPreservation
import Leanux.Proofs.WG.Packets.TransmitStack

/-! Deferred callers use the same explicit scheduler callback at each actual
source occurrence. Atomic wheel/send/clear observations keep the old RX focus;
any newly reached transmit receipt comes from the committed scheduler callback. -/
namespace Leanux.Proofs.WG.TransmitJoint.Deferred
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps
open RxHistory.DeferredSource

def crypt (schedule : Option Worker → PrefixM Event Unit) : PrefixM Event Unit :=
  cryptWith (schedule none)

def send (schedule : Option Worker → PrefixM Event Unit) : PrefixM Event Unit :=
  sendWith (fun {_} g => oldRx g) (schedule none)

def afterXmit (schedule : Option Worker → PrefixM Event Unit) : PrefixM Event Unit :=
  afterXmitWith (fun {_} g => oldRx g) (crypt schedule) (send schedule)

def timers (schedule : Option Worker → PrefixM Event Unit) (j : UInt64) : PrefixM Event Bool :=
  timersWith (fun {_} g => oldRx g) (crypt schedule) j

def placeholder (schedule : Option Worker → PrefixM Event Unit) (j : UInt64) : PrefixM Event Unit :=
  placeholderWith (fun {_} g => oldRx g) (crypt schedule) (send schedule) j

def idle (schedule : Option Worker → PrefixM Event Unit) : PrefixM Event Unit :=
  idleWith (fun {_} g => oldRx g) (timers schedule) (placeholder schedule)

def afterAdvance (schedule : Option Worker → PrefixM Event Unit) : PrefixM Event Unit :=
  afterAdvanceWith (fun {_} g => oldRx g) (timers schedule) (placeholder schedule)

def deferred (schedule : Option Worker → PrefixM Event Unit) (call : EnvDeferredCall) : PrefixM Event call.Result :=
  deferredWith (fun {_} g => oldRx g) (crypt schedule) (send schedule) (afterXmit schedule)
    (timers schedule) (placeholder schedule) (idle schedule) (afterAdvance schedule) call

theorem crypt_projects (schedule : Option Worker → PrefixM Event Unit)
    (hs : ProjectsPrefix RxTransmit.globalRx id (schedule none) (RxHistory.schedule none)) :
    ProjectsPrefix RxTransmit.globalRx id (crypt schedule) RxHistory.runCryptWorkers :=
  RxHistory.DeferredSource.crypt_projects _ _ _ hs

theorem send_projects (schedule : Option Worker → PrefixM Event Unit)
    (hs : ProjectsPrefix RxTransmit.globalRx id (schedule none) (RxHistory.schedule none)) :
    ProjectsPrefix RxTransmit.globalRx id (send schedule) RxHistory.runSendWorkers :=
  RxHistory.DeferredSource.send_projects _ _ _ (fun g hg => oldRx_projects g hg) _ _ hs

theorem afterXmit_projects (schedule : Option Worker → PrefixM Event Unit)
    (hs : ProjectsPrefix RxTransmit.globalRx id (schedule none) (RxHistory.schedule none)) :
    ProjectsPrefix RxTransmit.globalRx id (afterXmit schedule) RxHistory.afterXmit :=
  RxHistory.DeferredSource.afterXmit_projects _ _ _ (fun g hg => oldRx_projects g hg)
    _ _ _ _ (crypt_projects schedule hs) (send_projects schedule hs)

theorem timers_projects (schedule : Option Worker → PrefixM Event Unit)
    (hs : ProjectsPrefix RxTransmit.globalRx id (schedule none) (RxHistory.schedule none)) (j : UInt64) :
    ProjectsPrefix RxTransmit.globalRx id (timers schedule j) (RxHistory.runTimers j) :=
  RxHistory.DeferredSource.timers_projects _ _ _ (fun g hg => oldRx_projects g hg)
    _ _ (crypt_projects schedule hs) j

theorem placeholder_projects (schedule : Option Worker → PrefixM Event Unit)
    (hs : ProjectsPrefix RxTransmit.globalRx id (schedule none) (RxHistory.schedule none)) (j : UInt64) :
    ProjectsPrefix RxTransmit.globalRx id (placeholder schedule j) (RxHistory.runTimersPlaceholder j) :=
  RxHistory.DeferredSource.placeholder_projects _ _ _ (fun g hg => oldRx_projects g hg)
    _ _ _ _ (crypt_projects schedule hs) (send_projects schedule hs) j

theorem idle_projects (schedule : Option Worker → PrefixM Event Unit)
    (hs : ProjectsPrefix RxTransmit.globalRx id (schedule none) (RxHistory.schedule none)) :
    ProjectsPrefix RxTransmit.globalRx id (idle schedule) RxHistory.idleTimers :=
  RxHistory.DeferredSource.idle_projects _ _ _ (fun g hg => oldRx_projects g hg)
    _ _ _ _ (timers_projects schedule hs) (placeholder_projects schedule hs)

theorem afterAdvance_projects (schedule : Option Worker → PrefixM Event Unit)
    (hs : ProjectsPrefix RxTransmit.globalRx id (schedule none) (RxHistory.schedule none)) :
    ProjectsPrefix RxTransmit.globalRx id (afterAdvance schedule) RxHistory.afterAdvance :=
  RxHistory.DeferredSource.afterAdvance_projects _ _ _ (fun g hg => oldRx_projects g hg)
    _ _ _ _ (timers_projects schedule hs) (placeholder_projects schedule hs)

theorem deferred_projects (schedule : Option Worker → PrefixM Event Unit)
    (hs : ProjectsPrefix RxTransmit.globalRx id (schedule none) (RxHistory.schedule none)) (call : EnvDeferredCall) :
    ProjectsPrefix RxTransmit.globalRx id (deferred schedule call) (RxHistory.deferred call) :=
  RxHistory.DeferredSource.deferred_projects _ _ _ (fun g hg => oldRx_projects g hg)
    _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (crypt_projects schedule hs) (send_projects schedule hs) (afterXmit_projects schedule hs)
    (timers_projects schedule hs) (placeholder_projects schedule hs)
    (idle_projects schedule hs) (afterAdvance_projects schedule hs) call

theorem crypt_appends (schedule : Option Worker → PrefixM Event Unit) (hs : Appends (schedule none)) :
    Appends (crypt schedule) := RxHistory.DeferredSource.crypt_appends _ hs

theorem send_appends (schedule : Option Worker → PrefixM Event Unit) (hs : Appends (schedule none)) :
    Appends (send schedule) :=
  RxHistory.DeferredSource.send_appends _ (fun g _ => oldRx_appends g) _ hs

theorem afterXmit_appends (schedule : Option Worker → PrefixM Event Unit) (hs : Appends (schedule none)) :
    Appends (afterXmit schedule) :=
  RxHistory.DeferredSource.afterXmit_appends _ (fun g _ => oldRx_appends g)
    _ (crypt_appends schedule hs) _ (send_appends schedule hs)

theorem timers_appends (schedule : Option Worker → PrefixM Event Unit) (hs : Appends (schedule none)) (j : UInt64) :
    Appends (timers schedule j) :=
  RxHistory.DeferredSource.timers_appends _ (fun g _ => oldRx_appends g) _ (crypt_appends schedule hs) j

theorem placeholder_appends (schedule : Option Worker → PrefixM Event Unit) (hs : Appends (schedule none)) (j : UInt64) :
    Appends (placeholder schedule j) :=
  RxHistory.DeferredSource.placeholder_appends _ (fun g _ => oldRx_appends g)
    _ (crypt_appends schedule hs) _ (send_appends schedule hs) j

theorem idle_appends (schedule : Option Worker → PrefixM Event Unit) (hs : Appends (schedule none)) :
    Appends (idle schedule) :=
  RxHistory.DeferredSource.idle_appends _ (fun g _ => oldRx_appends g)
    _ (timers_appends schedule hs) _ (placeholder_appends schedule hs)

theorem afterAdvance_appends (schedule : Option Worker → PrefixM Event Unit) (hs : Appends (schedule none)) :
    Appends (afterAdvance schedule) :=
  RxHistory.DeferredSource.afterAdvance_appends _ (fun g _ => oldRx_appends g)
    _ (timers_appends schedule hs) _ (placeholder_appends schedule hs)

theorem deferred_appends (schedule : Option Worker → PrefixM Event Unit) (hs : Appends (schedule none)) (call : EnvDeferredCall) :
    Appends (deferred schedule call) :=
  RxHistory.DeferredSource.deferred_appends _ (fun g _ => oldRx_appends g)
    _ (crypt_appends schedule hs) _ (send_appends schedule hs) _ (afterXmit_appends schedule hs)
    _ (timers_appends schedule hs) _ (placeholder_appends schedule hs)
    _ (idle_appends schedule hs) _ (afterAdvance_appends schedule hs) call

theorem crypt_preserves (initial : FlatTable × FlatTable) (schedule : Option Worker → PrefixM Event Unit)
    (hs : PrefixPreserves (Inv initial) (Safe initial) (schedule none)) :
    PrefixPreserves (Inv initial) (Safe initial) (crypt schedule) :=
  RxHistory.DeferredSource.crypt_preserves (fun _ _ hi => hi.safe) Inv.productStore _ hs

theorem send_preserves (initial : FlatTable × FlatTable) (schedule : Option Worker → PrefixM Event Unit)
    (hs : PrefixPreserves (Inv initial) (Safe initial) (schedule none)) :
    PrefixPreserves (Inv initial) (Safe initial) (send schedule) :=
  RxHistory.DeferredSource.send_preserves (fun _ _ hi => hi.safe) Inv.productStore _ (transmit_atoms initial) _ hs

theorem afterXmit_preserves (initial : FlatTable × FlatTable) (schedule : Option Worker → PrefixM Event Unit)
    (hs : PrefixPreserves (Inv initial) (Safe initial) (schedule none)) :
    PrefixPreserves (Inv initial) (Safe initial) (afterXmit schedule) :=
  RxHistory.DeferredSource.afterXmit_preserves (fun _ _ hi => hi.safe) Inv.productStore _ (transmit_atoms initial)
    _ (crypt_preserves initial schedule hs) _ (send_preserves initial schedule hs)

theorem timers_preserves (initial : FlatTable × FlatTable) (schedule : Option Worker → PrefixM Event Unit)
    (hs : PrefixPreserves (Inv initial) (Safe initial) (schedule none)) (j : UInt64) :
    PrefixPreserves (Inv initial) (Safe initial) (timers schedule j) :=
  RxHistory.DeferredSource.timers_preserves (fun _ _ hi => hi.safe) Inv.productStore _ (transmit_atoms initial)
    _ (crypt_preserves initial schedule hs) j

theorem placeholder_preserves (initial : FlatTable × FlatTable) (schedule : Option Worker → PrefixM Event Unit)
    (hs : PrefixPreserves (Inv initial) (Safe initial) (schedule none)) (j : UInt64) :
    PrefixPreserves (Inv initial) (Safe initial) (placeholder schedule j) :=
  RxHistory.DeferredSource.placeholder_preserves (fun _ _ hi => hi.safe) Inv.productStore _ (transmit_atoms initial)
    _ (crypt_preserves initial schedule hs) _ (send_preserves initial schedule hs) j

theorem idle_preserves (initial : FlatTable × FlatTable) (schedule : Option Worker → PrefixM Event Unit)
    (hs : PrefixPreserves (Inv initial) (Safe initial) (schedule none)) :
    PrefixPreserves (Inv initial) (Safe initial) (idle schedule) :=
  RxHistory.DeferredSource.idle_preserves (fun _ _ hi => hi.safe) Inv.productStore _ (transmit_atoms initial)
    _ (timers_preserves initial schedule hs) _ (placeholder_preserves initial schedule hs)

theorem afterAdvance_preserves (initial : FlatTable × FlatTable) (schedule : Option Worker → PrefixM Event Unit)
    (hs : PrefixPreserves (Inv initial) (Safe initial) (schedule none)) :
    PrefixPreserves (Inv initial) (Safe initial) (afterAdvance schedule) :=
  RxHistory.DeferredSource.afterAdvance_preserves (fun _ _ hi => hi.safe) Inv.productStore _ (transmit_atoms initial)
    _ (timers_preserves initial schedule hs) _ (placeholder_preserves initial schedule hs)

theorem deferred_preserves (initial : FlatTable × FlatTable) (schedule : Option Worker → PrefixM Event Unit)
    (hs : PrefixPreserves (Inv initial) (Safe initial) (schedule none)) (call : EnvDeferredCall) :
    PrefixPreserves (Inv initial) (Safe initial) (deferred schedule call) :=
  RxHistory.DeferredSource.deferred_preserves _ (transmit_atoms initial) _ _ _ _ _ _ _
    (crypt_preserves initial schedule hs) (send_preserves initial schedule hs) (afterXmit_preserves initial schedule hs)
    (timers_preserves initial schedule hs) (placeholder_preserves initial schedule hs)
    (idle_preserves initial schedule hs) (afterAdvance_preserves initial schedule hs) call

end Leanux.Proofs.WG.TransmitJoint.Deferred
