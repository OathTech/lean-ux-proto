import Leanux.Proofs.WG.Queues.JointRtnetlink
import Leanux.Proofs.WG.Queues.JointDestruct

/-! The same deletion execution retains idle checks, stepped-dump rejection,
routing notifications, completed peer removal and final device retirement. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes AllowedIps
universe u

def envDeleteWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → Leanux.M α → m α) (idle down destruct : m Unit) : m Int := do
  if (← lift getWG).dev.isSome then idle
  let pending (sock : WG.NlSock) : Bool :=
    sock.cbRunning || sock.queue.any fun chunk => chunk.messages.any fun m => match m with | .done .. => true | _ => false
  let k ← lift getWG
  if pending k.nlSock7 || pending k.nlSock8 then
    lift (unsupported "a delete with a stepped dump pending (the dump's cursor holds the device reference; the guest refuses wg_delete_with_dump_pending)")
  let onDown : m Unit := do
    lift Net.Fib.rtCacheFlush
    lift (Net.Fib.netdevDown WG0_IFINDEX)
    lift (modifyRouting fun w => { w with defaultRoute6 := false, addrs6 := [], ipv6Gen := w.ipv6Gen + 1 })
  let onUnregister : m Unit := do
    lift Env.inetdevDestroy
    lift (Net.Fib.netdevUnregister WG0_IFINDEX)
    lift (modifyRouting fun w => { w with addrs6 := [], defaultRoute6 := false, ipv6Gen := w.ipv6Gen + 1 })
  if (← lift getWG).dev.isNone then return -ENODEV
  if (← lift (liftWG getDev)).running then
    down
    onDown
  lift (skipCut allocCuts)
  onUnregister
  lift (liftWG mayHaveSlept)
  destruct
  return 0

theorem envDelete_factor : Env.wgDelete = envDeleteWith (fun {_} a => a)
    Env.requireIdleDevice (liftWG wgDown) (liftWG wgDestruct) := by
  simp only [Env.wgDelete,WG.wgDelete,envDeleteWith]
  rfl

theorem envDeleteObserved_factor : envWgDeleteObserved = envDeleteWith (fun {_} a => liftPrefix a)
    (liftPrefix Env.requireIdleDevice) (liftPrefix (liftWG wgDown))
    (liftWGObserver wgDestructObserved) := rfl

theorem envDeleteAudit_factor : envWgDeleteAudit = envDeleteWith (fun {_} a => liftPrefix a)
    (auditFocus requireIdleDevicePrefix) (auditFocus (liftWGObserver wgDownPrefix))
    (auditFocus (liftWGObserver wgDestructPrefix)) := rfl

theorem envDeleteWith_projects {E F : Type} (ρ : E → Option F)
    {idle down destruct : PrefixM E Unit} {idle' down' destruct' : PrefixM F Unit}
    (hi : ProjectsPrefix ρ id idle idle') (hd : ProjectsPrefix ρ id down down')
    (hx : ProjectsPrefix ρ id destruct destruct') :
    ProjectsPrefix ρ id (envDeleteWith (fun {_} a => liftPrefix a) idle down destruct)
      (envDeleteWith (fun {_} a => liftPrefix a) idle' down' destruct') := by
  unfold envDeleteWith
  repeat' first
    | with_reducible exact hi
    | with_reducible exact hd
    | with_reducible exact hx
    | with_reducible exact projectsPrefix_lift ρ _
    | with_reducible exact projectsPrefix_pure ρ id _
    | with_reducible apply projectsPrefix_bind ρ id id
    | (maintenance_intro; try dsimp only [id])
    | (split <;> try contradiction)
  all_goals exact fun _ _ => rfl

theorem envDeleteWith_appends {E : Type} {idle down destruct : PrefixM E Unit}
    (hi : Appends idle) (hd : Appends down) (hx : Appends destruct) :
    Appends (envDeleteWith (fun {_} a => liftPrefix a) idle down destruct) := by
  unfold envDeleteWith
  repeat' first
    | with_reducible exact hi
    | with_reducible exact hd
    | with_reducible exact hx
    | rx_append_step

theorem envDeleteWith_focuses {E F : Type} (encode : E → F) (decode : F → Option E)
    (he : ∀ e, decode (encode e) = some e)
    {idle down destruct : PrefixM F Unit} {idle' down' destruct' : PrefixM E Unit}
    (hi : FocusesUnder (fun _ _ => True) encode decode idle idle')
    (hd : FocusesUnder (fun _ _ => True) encode decode down down')
    (hx : FocusesUnder (fun _ _ => True) encode decode destruct destruct')
    (ai : Appends idle') (ad : Appends down') (ax : Appends destruct') :
    FocusesUnder (fun _ _ => True) encode decode
      (envDeleteWith (fun {_} a => liftPrefix a) idle down destruct)
      (envDeleteWith (fun {_} a => liftPrefix a) idle' down' destruct') := by
  have preserve {G α : Type} {a : PrefixM G α} (ha : Appends a) :
      PrefixPreserves (fun _ _ => True) (fun _ => True) a :=
    (pinned_const _private.Leanux.Proofs.WG.Queues.JointNetlink.«0».Leanux.Proofs.WG.Configuration.true_preserves) ha
  unfold envDeleteWith
  repeat' first
    | with_reducible exact hi
    | with_reducible exact hd
    | with_reducible exact hx
    | with_reducible exact FocusesUnder.lift _
    | with_reducible exact FocusesUnder.pure _
    | with_reducible apply FocusesUnder.bind he
    | with_reducible apply preserve
    | with_reducible exact ai
    | with_reducible exact ad
    | with_reducible exact ax
    | rx_append_step

theorem envDeleteWith_focus {E F : Type} (encode : E → F) (decode : F → Option E)
    (he : ∀ e, decode (encode e) = some e) (idle down destruct : PrefixM E Unit)
    (hi : Appends idle) (hd : Appends down) (hx : Appends destruct) :
    envDeleteWith (fun {_} a => liftPrefix a) (focusPrefix encode decode idle)
      (focusPrefix encode decode down) (focusPrefix encode decode destruct) =
      focusPrefix encode decode (envDeleteWith (fun {_} a => liftPrefix a) idle down destruct) := by
  funext w h
  exact envDeleteWith_focuses encode decode he (FocusesUnder.focus idle)
    (FocusesUnder.focus down) (FocusesUnder.focus destruct) hi hd hx w h True.intro

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Configuration AllowedIps

def envDelete : PrefixM Event Int := envDeleteWith (fun {_} a => liftPrefix a)
  (rxAction (RxHistory.mixed requireIdleDevicePrefix))
  (rxAction (RxHistory.mixed (liftWGObserver wgDownPrefix)))
  (liftWGObserver destructDevice)

theorem envDelete_routing : ProjectsPrefix routingEvent id envDelete envWgDeleteObserved := by
  rw [envDeleteObserved_factor]
  exact envDeleteWith_projects routingEvent
    (rxAction_routing (RxHistory.mixed_erases requireIdleDevicePrefix_erases))
    (rxAction_routing (RxHistory.mixed_erases (liftWGObserver_erases wgDownPrefix_erases)))
    (destructDevice_routing.liftWGObserver _ _)

theorem envDelete_rx : ProjectsPrefix rxEvent id envDelete (RxHistory.audit envWgDeleteAudit) := by
  rw [envDeleteAudit_factor]
  unfold RxHistory.audit
  rw [← envDeleteWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl)
    (auditFocus requireIdleDevicePrefix) (auditFocus (liftWGObserver wgDownPrefix))
    (auditFocus (liftWGObserver wgDestructPrefix))
    (Appends.focus _ _ _) (Appends.focus _ _ _) (Appends.focus _ _ _)]
  exact envDeleteWith_projects rxEvent (rxAction_rx (Appends.focus _ _ _))
    (rxAction_rx (Appends.focus _ _ _)) destructDevice_rx_product

def dispatchDelete : PrefixM Event Int :=
  rtnetlinkRequestWith (fun {_} a => liftPrefix a) envDelete

theorem dispatchDelete_routing : ProjectsPrefix routingEvent id dispatchDelete (dispatchObserved .wgDelete) := by
  change ProjectsPrefix routingEvent id dispatchDelete (rtnetlinkRequestObserved envWgDeleteObserved)
  rw [rtnetlinkRequestObserved_factor]
  exact rtnetlinkRequestWith_projects routingEvent envDelete_routing

theorem dispatchDelete_rx : ProjectsPrefix rxEvent id dispatchDelete (RxHistory.syscallDispatch .wgDelete) := by
  change ProjectsPrefix rxEvent id dispatchDelete (RxHistory.audit (rtnetlinkRequestAudit envWgDeleteAudit))
  rw [rtnetlinkRequestAudit_factor]
  unfold RxHistory.audit
  have ha : Appends envWgDeleteAudit := by
    rw [envDeleteAudit_factor]
    exact envDeleteWith_appends (Appends.focus _ _ _) (Appends.focus _ _ _) (Appends.focus _ _ _)
  rw [← rtnetlinkRequestWith_focus RxHistory.Event.audit RxHistory.auditEvent (fun _ => rfl) _ ha]
  exact rtnetlinkRequestWith_projects rxEvent envDelete_rx

theorem dispatchDelete_erases : ErasesPrefix dispatchDelete (Leanux.dispatch .wgDelete) := by
  intro w h
  have hp := congrArg Prod.fst (dispatchDelete_rx w h)
  have he := RxHistory.syscallDispatch_erases .wgDelete w (h.filterMap rxEvent)
  have same := hp.symm.trans he
  change ((runPrefix dispatchDelete w h).1.map (fun (x,v) => (x,v))) = _ at same
  cases hr : (runPrefix dispatchDelete w h).1 <;> simpa only [hr,Except.map] using same

end Leanux.Proofs.WG.Queues.RoutingJoint
