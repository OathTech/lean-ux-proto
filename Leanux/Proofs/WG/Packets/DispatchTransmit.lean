import Leanux.Proofs.WG.Lifetimes.DispatchSource
import Leanux.Proofs.WG.Packets.TrafficTransmit

/-! Actual socket and observation wrappers and the complete dispatch selector.
Only explicit traffic callbacks may emit new transmit handoffs; routing
configuration uses its existing completed mutations. -/
namespace Leanux.Proofs.WG.TransmitJoint.Calls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps Configuration

def socket (fd : Nat) (body : PrefixM Event Int) : PrefixM Event Int :=
  socketCallOnWith (fun {_} a => liftPrefix a) fd body

def observe (timers : PrefixM Event Unit) : PrefixM Event Int := do
  timers
  let (ret, observed) ← liftPrefix Environment.observeTail
  liftPrefix (modifyAmbient fun w => {w with extraOut := ["datagrams", "replies", "stats"].map (fun k => (k, observed.getObjValD k))})
  socket LISTEN4_FD (pure ret)

def dispatch (crypt poll after timers : PrefixM Event Unit) : Syscall → PrefixM Event Int :=
  dispatchWith (fun call => oldProduct (RoutingJoint.dispatch call))
    (fun attrs => oldProduct (RoutingJoint.dispatchSet attrs))
    (oldProduct RoutingJoint.dispatchCreate) (oldProduct RoutingJoint.dispatchDelete)
    direct (fun family port msg tos ll dest => socket SENDER_FD (Traffic.inject crypt family port msg tos ll dest))
    (Traffic.flood poll after) (Traffic.batch poll after) (observe timers)

private theorem lift_store (initial : FlatTable × FlatTable) (a : Leanux.M α)
    (frame : SameView (fun w : World => wgStoreView w.wg) a) :
    PrefixPreserves (Inv initial) (Safe initial) (liftPrefix a) :=
  viewLiftPrefix_preserves _ (fun _ _ hi => hi.safe) Inv.store frame

private theorem lift_fs (initial : FlatTable × FlatTable) (a : FS.M α) :
    PrefixPreserves (Inv initial) (Safe initial) (liftPrefix (liftFS a)) :=
  lift_store initial _ (fun state => productFS_spec a (fun w => wgStoreView w.wg = state)
    (fun _ _ _ _ hi => hi))

theorem socket_preserves (initial : FlatTable × FlatTable) (fd : Nat) (body : PrefixM Event Int)
    (hb : PrefixPreserves (Inv initial) (Safe initial) body) :
    PrefixPreserves (Inv initial) (Safe initial) (socket fd body) := by
  unfold socket socketCallOnWith
  apply PrefixPreserves.bind (lift_fs initial _)
  intro f
  split
  · exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
  · exact hb.bind (fun ret => (lift_fs initial _).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) ret))

theorem socket_projects (fd : Nat) (body : PrefixM Event Int) (lower : RxHistory.Obs Int)
    (hb : ProjectsPrefix RxTransmit.globalRx id body lower) :
    ProjectsPrefix RxTransmit.globalRx id (socket fd body) (RxHistory.socketCallOn fd lower) :=
  socketCallOnWith_projects _ fd hb

theorem socket_appends (fd : Nat) (body : PrefixM Event Int) (hb : Appends body) :
    Appends (socket fd body) := socketCallOnWith_appends fd hb

theorem observe_preserves (initial : FlatTable × FlatTable) (timers : PrefixM Event Unit)
    (ht : PrefixPreserves (Inv initial) (Safe initial) timers) :
    PrefixPreserves (Inv initial) (Safe initial) (observe timers) := by
  unfold observe
  apply ht.bind
  intro _
  apply PrefixPreserves.bind (lift_store initial _
    (observeTail_sameKernel.of_factor (fun s : ProductStore43 => s.2.2.2) _ (fun _ => rfl)))
  intro out
  apply PrefixPreserves.bind (lift_store initial _
    (fun state => productAmbient_spec _ (fun w => wgStoreView w.wg = state) (fun _ _ hi => hi)))
  intro _
  exact socket_preserves initial _ _ (PrefixPreserves.pure (fun _ _ hi => hi.safe) out.1)

theorem observe_projects (timers : PrefixM Event Unit)
    (ht : ProjectsPrefix RxTransmit.globalRx id timers RxHistory.idleTimers) :
    ProjectsPrefix RxTransmit.globalRx id (observe timers) (RxHistory.syscallDispatch .wgObserve) := by
  unfold observe RxHistory.syscallDispatch RxHistory.observe
  simp only [bind_assoc]
  apply projectsPrefix_bind _ id id ht
  intro _
  apply projectsPrefix_bind _ id id (projectsPrefix_lift _ _)
  intro out
  exact projectsPrefix_bind _ id id (projectsPrefix_lift _ _) (fun _ =>
    socket_projects _ _ _ (projectsPrefix_pure _ id out.1))

theorem observe_appends (timers : PrefixM Event Unit) (ht : Appends timers) :
    Appends (observe timers) := by
  unfold observe
  apply Appends.bind ht
  intro _
  apply Appends.bind (Appends.lift Environment.observeTail)
  intro out
  exact Appends.bind (Appends.lift _) (fun _ => socket_appends _ _ (Appends.pure out.1))

private theorem old_dispatch_preserves (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) :
    PrefixPreserves (Inv initial) (Safe initial) (oldProduct (RoutingJoint.dispatch call)) := by
  have appended : Appends (RoutingJoint.dispatch call) := by
    cases call
    case wgSet attrs => exact RoutingPosition.Controls.dispatchSet_appends attrs
    case wgCreate => exact RoutingPosition.Controls.dispatchCreate_appends
    case wgDelete => exact RoutingPosition.Controls.dispatchDelete_appends
    all_goals exact Appends.focus _ _ _
  exact oldProduct_projected initial (RoutingJoint.dispatch call) (dispatchObserved call) appended
    (RoutingJoint.dispatch_routing call) (dispatchObserved_global initial call shape)

theorem dispatch_preserves (initial : FlatTable × FlatTable) (crypt poll after timers : PrefixM Event Unit)
    (hc : PrefixPreserves (Inv initial) (Safe initial) crypt)
    (hp : PrefixPreserves (Inv initial) (Safe initial) poll)
    (ha : PrefixPreserves (Inv initial) (Safe initial) after)
    (ht : PrefixPreserves (Inv initial) (Safe initial) timers)
    (call : Syscall) (shape : SyscallAddressShape call) :
    PrefixPreserves (Inv initial) (Safe initial) (dispatch crypt poll after timers call) := by
  cases call
  case wgSet attrs => exact oldProduct_dispatchSet initial attrs shape
  case wgCreate => exact oldProduct_dispatchCreate initial
  case wgDelete => exact oldProduct_dispatchDelete initial
  case wgXmit family addr bytes opts => exact direct_preserves initial family addr bytes opts
  case wgInject family port msg tos ll dest =>
    exact socket_preserves initial _ _
      (Traffic.inject_preserves initial crypt hc family port msg tos ll dest)
  case wgFlood count port family msgs => exact Traffic.flood_preserves initial poll after hp ha count port family msgs
  case wgBatch items _ => exact Traffic.batch_preserves initial poll after hp ha items
  case wgObserve => exact observe_preserves initial timers ht
  all_goals exact old_dispatch_preserves initial _ shape

private theorem old_projects (g : PrefixM RoutingJoint.Event α) (lower : RxHistory.Obs α)
    (ha : Appends g) (hp : ProjectsPrefix RoutingJoint.rxEvent id g lower) :
    ProjectsPrefix RxTransmit.globalRx id (oldProduct g) lower := by
  intro w h
  have outer := oldProduct_projects g ha w h
  have inner := hp w (h.filterMap oldEvent)
  have histories : (h.filterMap oldEvent).filterMap RoutingJoint.rxEvent =
      h.filterMap RxTransmit.globalRx := List.filterMap_filterMap
  rw [histories,congrArg Prod.fst outer,congrArg Prod.snd outer] at inner
  unfold RxTransmit.globalRx at *
  cases result : (runPrefix (oldProduct g) w h).1 <;>
    simpa only [result,Except.map,id_eq,List.filterMap_filterMap] using inner

private theorem old_dispatch_projects (call : Syscall) :
    ProjectsPrefix RxTransmit.globalRx id (oldProduct (RoutingJoint.dispatch call)) (RxHistory.syscallDispatch call) := by
  have appended : Appends (RoutingJoint.dispatch call) := by
    cases call
    case wgSet attrs => exact RoutingPosition.Controls.dispatchSet_appends attrs
    case wgCreate => exact RoutingPosition.Controls.dispatchCreate_appends
    case wgDelete => exact RoutingPosition.Controls.dispatchDelete_appends
    all_goals exact Appends.focus _ _ _
  exact old_projects _ _ appended (RoutingJoint.dispatch_rx call)

theorem dispatch_projects (crypt poll after timers : PrefixM Event Unit)
    (hc : ProjectsPrefix RxTransmit.globalRx id crypt RxHistory.runCryptWorkers)
    (hp : ProjectsPrefix RxTransmit.globalRx id poll RxHistory.pollScheduledInline)
    (ha : ProjectsPrefix RxTransmit.globalRx id after RxHistory.afterBatch)
    (ht : ProjectsPrefix RxTransmit.globalRx id timers RxHistory.idleTimers) (call : Syscall) :
    ProjectsPrefix RxTransmit.globalRx id (dispatch crypt poll after timers call) (RxHistory.syscallDispatch call) := by
  cases call
  case wgXmit family addr bytes opts => exact direct_rx family addr bytes opts
  case wgInject family port msg tos ll dest =>
    exact socket_projects _ _ _ (Traffic.inject_projects crypt hc family port msg tos ll dest)
  case wgFlood count port family msgs => exact Traffic.flood_projects poll after hp ha count port family msgs
  case wgBatch items _ => exact Traffic.batch_projects poll after hp ha items
  case wgObserve => exact observe_projects timers ht
  all_goals exact old_dispatch_projects _

theorem dispatch_appends (crypt poll after timers : PrefixM Event Unit)
    (hc : Appends crypt) (hp : Appends poll) (ha : Appends after) (ht : Appends timers) (call : Syscall) :
    Appends (dispatch crypt poll after timers call) := by
  cases call
  case wgXmit family addr bytes opts => exact direct_appends family addr bytes opts
  case wgInject family port msg tos ll dest =>
    exact socket_appends _ _ (Traffic.inject_appends crypt hc family port msg tos ll dest)
  case wgFlood count port family msgs => exact Traffic.flood_appends poll after hp ha count port family msgs
  case wgBatch items _ => exact Traffic.batch_appends poll after hp ha items
  case wgObserve => exact observe_appends timers ht
  all_goals exact oldProduct_appends _

end Leanux.Proofs.WG.TransmitJoint.Calls
