import Leanux.Proofs.WG.Configuration.RoutingConfiguration
import Leanux.Proofs.WG.Configuration.RoutingTraffic
import Leanux.Proofs.WG.Origins.OwnerControlCalls

/-! Every actual syscall dispatch arm preserves routing at earlier consume
positions. Poll-bearing traffic uses the concrete checked callbacks; routing
configuration retains its original address-shape premise. -/
namespace Leanux.Proofs.WG.RoutingPosition.Calls
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AllowedIps Configuration Origins RoutingPosition.Callers

private theorem fs (initial : FlatTable × FlatTable) (a : FS.M α) :
    Focused initial (liftPrefix (liftFS a)) :=
  lift initial _ (ProjectedRetainsRoutingCall.of_same
    (fun state => productFS_spec a (fun w => routingView w.wg = state) (fun _ _ _ _ hi => hi)))

private theorem quiet (initial : FlatTable × FlatTable) (a : AuditM α)
    (w : World) (h : List RoutingJoint.Event) (hh : Checks initial h) :
    Checks initial (runPrefix (RoutingJoint.rxAction (RxHistory.audit a)) w h).2 :=
  Controls.audit_projection_checks initial (Appends.focus _ _ _)
    ((Appends.focus _ _ _).project_focus RoutingJoint.Event.rx RoutingJoint.rxEvent (fun _ => rfl)) w h hh

theorem socketCallOn (initial : FlatTable × FlatTable) (fd : Nat) (body : RxHistory.Obs Int)
    (hb : Focused initial body) : Focused initial (RxHistory.socketCallOn fd body) := by
  unfold RxHistory.socketCallOn
  apply bind initial _ _
  · exact fs initial _
  · intro f
    apply FocusedInvariant.ite
    · intro _; exact pure initial _
    · intro _
      apply bind initial _ _ hb
      intro ret
      exact bind initial _ _
        (fs initial _)
        (fun _ => pure initial ret)

theorem dispatch (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) :
    PrefixPreserves (Inv initial) (Safe initial) (RoutingJoint.dispatch call) := by
  cases call
  case wgSet attrs => exact Controls.dispatchSet initial attrs shape
  case wgCreate => exact Controls.dispatchCreate initial
  case wgDelete => exact Controls.dispatchDelete initial
  case wgInject family port msg tos ll dest =>
    exact (socketCallOn initial _ _ (Traffic.inject initial family port msg tos ll dest)).2
  case wgFlood count port family messages => exact (Traffic.flood initial count port family messages).2
  case wgBatch items _ => exact (Traffic.batch initial items).2
  case wgObserve =>
    suffices observed : Focused initial (RxHistory.syscallDispatch .wgObserve) from observed.2
    unfold RxHistory.syscallDispatch
    apply bind initial _ _ (Traffic.observe initial)
    intro out
    apply bind initial _ _
    · exact store initial _ (fun state => productAmbient_spec _ _ (fun _ _ hi => hi))
    · intro _
      exact socketCallOn initial _ _ (pure initial out.1)
  all_goals
    apply combine initial _ _ (Appends.focus _ _ _)
      (RoutingJoint.dispatch_routing _) (dispatchObserved_global initial _ shape)
    intro w h hi
    exact quiet initial _ w h hi.2

private theorem lift_frame (initial : FlatTable × FlatTable) (a : Leanux.M α)
    (frame : SameView (fun w : World => routingView w.wg) a) :
    PrefixPreserves (Inv initial) (Safe initial) (liftPrefix a) :=
  lift_preserves initial a (ProjectedRetainsRoutingCall.of_same frame)

private theorem lift_fs (initial : FlatTable × FlatTable) (a : FS.M α) :
    PrefixPreserves (Inv initial) (Safe initial) (liftPrefix (liftFS a)) :=
  lift_frame initial _ (fun s => productFS_spec a (fun w => routingView w.wg = s) (fun _ _ _ _ hi => hi))

private theorem lift_seccomp (initial : FlatTable × FlatTable) (a : Seccomp.M α) :
    PrefixPreserves (Inv initial) (Safe initial) (liftPrefix (liftSeccomp a)) :=
  lift_frame initial _ (fun s => productSeccomp_spec a (fun w => routingView w.wg = s) (fun _ _ _ _ hi => hi))

private theorem lift_ambient (initial : FlatTable × FlatTable) (a : AmbientM α) :
    PrefixPreserves (Inv initial) (Safe initial) (liftPrefix (liftAmbient a)) :=
  lift_frame initial _ (fun s => productAmbient_spec a (fun w => routingView w.wg = s) (fun _ _ hi => hi))

private theorem lift_modify (initial : FlatTable × FlatTable) (f : World → World)
    (same : ∀ w, routingView (f w).wg = routingView w.wg) :
    PrefixPreserves (Inv initial) (Safe initial) (liftPrefix (modify f)) :=
  lift_frame initial _ (fun s => hoare_modify (P := fun w => routingView w.wg = s) f (fun w hi => (same w).trans hi))

macro "routing_outer_step " initial:term : tactic => `(tactic| first
  | owner_outer_callback
  | (current_env_at unsupported; exact lift_ambient $initial (AmbientM.unsupported _))
  | (current_env_at liftPrefix; first
      | exact lift_fs $initial _
      | exact lift_seccomp $initial _
      | exact lift_ambient $initial _
      | exact lift_modify $initial _ (fun _ => rfl))
  | (current_env_at Pure.pure; exact PrefixPreserves.pure (fun _ _ hi => Inv.safe hi) _)
  | (current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (current_env_at ite; apply PrefixPreserves.ite)
  | (current_env_at dite; split)
  | support_intro
  | current_env_match)

private theorem syscall_tail_preserves (initial : FlatTable × FlatTable) (call : Syscall) (dispatch : PrefixM RoutingJoint.Event Int)
    (sendWorkers timers route xmit advance cleanup : PrefixM RoutingJoint.Event Unit)
    (hd : PrefixPreserves (Inv initial) (Safe initial) dispatch) (hs : PrefixPreserves (Inv initial) (Safe initial) sendWorkers)
    (ht : PrefixPreserves (Inv initial) (Safe initial) timers) (hr : PrefixPreserves (Inv initial) (Safe initial) route)
    (hx : PrefixPreserves (Inv initial) (Safe initial) xmit) (ha : PrefixPreserves (Inv initial) (Safe initial) advance)
    (hc : PrefixPreserves (Inv initial) (Safe initial) cleanup) :
    PrefixPreserves (Inv initial) (Safe initial) (do
      let ret ← dispatch
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
      match call with
      | .wgSet _ | .wgInject .. => sendWorkers; timers
      | .wgUp => sendWorkers; timers; route
      | .wgXmit .. => xmit; timers
      | .wgBatch .. => timers
      | .wgAdvance _ => advance
      | .wgNetnsClose => cleanup
      | _ => pure ()
      match call with
      | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
      | .wgAddroute .. | .wgAddaddr .. =>
        let shape := Net.Fib.shape (← liftPrefix getRouting)
        liftPrefix (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie",shape)]})
      | _ => pure ()
      pure ret) := by
  have routing : PrefixPreserves (Inv initial) (Safe initial) (liftPrefix (getRouting : Leanux.M Net.Routing)) :=
    lift_frame initial _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v run; cases run; rfl)
  apply PrefixPreserves.bind hd
  intro ret
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    intro c acc
    exact (lift_seccomp initial (Seccomp.enterHarnessCall c)).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.safe) _)
  · intro _
    apply PrefixPreserves.bind (lift_fs initial taskWorkRun)
    intro _
    cases call
    all_goals dsimp only
    all_goals repeat' first
      | owner_outer_callback
      | (change PrefixPreserves (Inv initial) (Safe initial) _; current_env_at getRouting; exact routing)
      | routing_outer_step initial

private theorem syscall_entry_preserves (initial : FlatTable × FlatTable) (call : Syscall) (body : PrefixM RoutingJoint.Event Int)
    (hb : PrefixPreserves (Inv initial) (Safe initial) body) : PrefixPreserves (Inv initial) (Safe initial) (do
  liftPrefix (modify fun w => { w with fs := {w.fs with userOut := none, userFds := none}, seccomp := {w.seccomp with emitted := {}, translatedLen := none} })
  liftPrefix (modifyWG fun g => {g with queuedThisCall := []})
  liftPrefix (modifyAmbient fun a => {a with steps := #[],extraOut := [],fired := #[],netRxSections := 0,netRxSection := 0})
  match syscallNr call with
  | some nr => liftPrefix (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none =>
    if call.isNet && (← liftPrefix getCurrent).seccomp.mode != .disabled then
      liftPrefix (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  body) := by
  have current : PrefixPreserves (Inv initial) (Safe initial) (liftPrefix Leanux.getCurrent) := by
    unfold Leanux.getCurrent
    exact lift_fs initial (StateT.lift TaskM.getCurrent)
  change PrefixPreserves (Inv initial) (Safe initial) _
  apply PrefixPreserves.bind
  · apply lift_modify initial
    intro w
    rfl
  intro _
  apply PrefixPreserves.bind
  · apply lift_modify initial
    intro w
    rfl
  intro _
  apply PrefixPreserves.bind
  · apply lift_modify initial
    intro w
    rfl
  intro _
  cases hn : syscallNr call
  all_goals repeat' first
    | owner_outer_callback
    | (change PrefixPreserves (Inv initial) (Safe initial) _; current_env_at Leanux.getCurrent; exact current)
    | routing_outer_step initial
    | owner_control_audit_reduce

/-- Exact entry resets, dispatch, wait callbacks and final FIB observation.
Every callback retains its full actual product observer domain. -/
theorem syscallWith_preserves (initial : FlatTable × FlatTable) (call : Syscall) (dispatch : PrefixM RoutingJoint.Event Int)
    (sendWorkers timers route xmit advance cleanup : PrefixM RoutingJoint.Event Unit)
    (hd : PrefixPreserves (Inv initial) (Safe initial) dispatch) (hs : PrefixPreserves (Inv initial) (Safe initial) sendWorkers)
    (ht : PrefixPreserves (Inv initial) (Safe initial) timers) (hr : PrefixPreserves (Inv initial) (Safe initial) route)
    (hx : PrefixPreserves (Inv initial) (Safe initial) xmit) (ha : PrefixPreserves (Inv initial) (Safe initial) advance)
    (hc : PrefixPreserves (Inv initial) (Safe initial) cleanup) :
    PrefixPreserves (Inv initial) (Safe initial) (syscallWith (fun {_} a => liftPrefix a)
      dispatch sendWorkers timers route xmit advance cleanup call) := by
  exact syscall_entry_preserves initial call _
    (syscall_tail_preserves initial call dispatch sendWorkers timers route xmit advance cleanup hd hs ht hr hx ha hc)

/-- The concrete return-to-user suffix follows the original call positions,
including post-errno callbacks and final FIB observation. -/
theorem syscall (initial : FlatTable × FlatTable) (call : Syscall)
    (shape : SyscallAddressShape call) :
    PrefixPreserves (Inv initial) (Safe initial) (RoutingJoint.syscall call) := by
  exact syscallWith_preserves initial call _ _ _ _ _ _ _ (dispatch initial call shape)
    (Deferred.runSendWorkers initial).2 (Deferred.idleTimers initial).2
    (audit initial _ _ routeIntoWg0Audit_erases
      (ProjectedRetainsRoutingCall.of_same routeIntoWg0_routing)).2
    (Deferred.afterXmit initial).2 (Deferred.afterAdvance initial).2
    (audit initial _ _ envNetnsCleanupAudit_erases netnsCleanup_routing).2

end Leanux.Proofs.WG.RoutingPosition.Calls
