import Leanux.Proofs.WG.Queues.JointDelete

/-! A shared proof-side syscall boundary retains the actual entry resets,
seccomp path, return-to-user callbacks and final IPv4 shape output. The
callbacks range over the whole original product observer domain. -/
namespace Leanux.Proofs.WG.Configuration
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
universe u

def syscallWith {m : Type → Type u} [Monad m]
    (lift : {α : Type} → Leanux.M α → m α) (dispatch : m Int)
    (sendWorkers timers route xmit advance cleanup : m Unit) (call : Syscall) : m Int := do
  lift (modify fun w => { w with fs := {w.fs with userOut := none, userFds := none}, seccomp := {w.seccomp with emitted := {}, translatedLen := none} })
  lift (modifyWG fun g => {g with queuedThisCall := []})
  lift (modifyAmbient fun a => {a with steps := #[], extraOut := [], fired := #[], netRxSections := 0, netRxSection := 0})
  match syscallNr call with
  | some nr => lift (liftSeccomp (Seccomp.enterHarnessCall nr))
  | none =>
    if call.isNet && (← lift getCurrent).seccomp.mode != .disabled then
      lift (unsupported "a network operation after a seccomp mode was set (the fixture's calls are not modelled under a filter)")
  let ret ← dispatch
  for c in Env.windowTailCalls do lift (liftSeccomp (Seccomp.enterHarnessCall c))
  lift (liftFS taskWorkRun)
  match call with
  | .wgSet _ | .wgInject .. => sendWorkers; timers
  | .wgUp => sendWorkers; timers; route
  | .wgXmit .. => xmit; timers
  | .wgBatch .. => timers   -- W7: the batch runs its queued units itself
  | .wgAdvance _ => advance
  | .wgNetnsClose => cleanup
  | _ => pure ()
  match call with
  | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
  | .wgAddroute .. | .wgAddaddr .. =>
    let shape := Net.Fib.shape (← lift getRouting)
    lift (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie", shape)]})
  | _ => pure ()
  return ret

theorem syscall_factor (call : Syscall) : Leanux.syscall call =
    syscallWith (fun {_} a => a) (Leanux.dispatch call) Env.runSendWorkers Env.idleTimers
      Env.routeIntoWg0 Env.afterXmit Env.afterAdvance Env.netnsCleanup call := rfl

theorem syscallObserved_factor (call : Syscall) : syscallObserved call =
    syscallWith (fun {_} a => liftPrefix a) (dispatchObserved call)
      (liftPrefix Env.runSendWorkers) (liftPrefix Env.idleTimers) (liftPrefix Env.routeIntoWg0)
      (liftPrefix Env.afterXmit) (liftPrefix Env.afterAdvance) (liftPrefix Env.netnsCleanup) call := rfl

theorem syscallRx_factor (call : Syscall) : Queues.RxHistory.syscall call =
    syscallWith (fun {_} a => liftPrefix a) (Queues.RxHistory.syscallDispatch call)
      Queues.RxHistory.runSendWorkers Queues.RxHistory.idleTimers
      (Queues.RxHistory.audit routeIntoWg0Audit) Queues.RxHistory.afterXmit Queues.RxHistory.afterAdvance
      (Queues.RxHistory.audit envNetnsCleanupAudit) call := rfl

theorem syscallWith_projects {E F : Type} (ρ : E → Option F)
    {dispatch : PrefixM E Int} {dispatch' : PrefixM F Int}
    {send timers route xmit advance cleanup : PrefixM E Unit}
    {send' timers' route' xmit' advance' cleanup' : PrefixM F Unit}
    (hd : ProjectsPrefix ρ id dispatch dispatch')
    (hs : ProjectsPrefix ρ id send send') (ht : ProjectsPrefix ρ id timers timers')
    (hr : ProjectsPrefix ρ id route route') (hx : ProjectsPrefix ρ id xmit xmit')
    (ha : ProjectsPrefix ρ id advance advance') (hc : ProjectsPrefix ρ id cleanup cleanup') (call : Syscall) :
    ProjectsPrefix ρ id (syscallWith (fun {_} a => liftPrefix a) dispatch send timers route xmit advance cleanup call)
      (syscallWith (fun {_} a => liftPrefix a) dispatch' send' timers' route' xmit' advance' cleanup' call) := by
  have tail : ProjectsPrefix ρ id (do
      let ret ← dispatch
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
      match call with
      | .wgSet _ | .wgInject .. => send; timers
      | .wgUp => send; timers; route
      | .wgXmit .. => xmit; timers
      | .wgBatch .. => timers   -- W7: the batch runs its queued units itself
      | .wgAdvance _ => advance
      | .wgNetnsClose => cleanup
      | _ => pure ()
      match call with
      | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
      | .wgAddroute .. | .wgAddaddr .. =>
        let shape := Net.Fib.shape (← liftPrefix getRouting)
        liftPrefix (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie",shape)]})
      | _ => pure ()
      pure ret) (do
      let ret ← dispatch'
      for c in Env.windowTailCalls do liftPrefix (liftSeccomp (Seccomp.enterHarnessCall c))
      liftPrefix (liftFS taskWorkRun)
      match call with
      | .wgSet _ | .wgInject .. => send'; timers'
      | .wgUp => send'; timers'; route'
      | .wgXmit .. => xmit'; timers'
      | .wgBatch .. => timers'   -- W7: the batch runs its queued units itself
      | .wgAdvance _ => advance'
      | .wgNetnsClose => cleanup'
      | _ => pure ()
      match call with
      | .wgUp | .wgDown | .wgDelete | .wgDeladdr _ | .wgDelroute .. | .wgSetMtu _ | .wgNetnsClose
      | .wgAddroute .. | .wgAddaddr .. =>
        let shape := Net.Fib.shape (← liftPrefix getRouting)
        liftPrefix (modifyAmbient fun w => {w with extraOut := w.extraOut ++ [("fib_trie",shape)]})
      | _ => pure ()
      pure ret) := by
    apply projectsPrefix_bind ρ id id hd
    intro ret
    apply projectsPrefix_bind ρ id id
    · apply projectsPrefix_forIn ρ id
      intro c acc
      exact projectsPrefix_bind ρ id (projectStep id) (projectsPrefix_lift ρ _)
        (fun _ => projectsPrefix_pure ρ (projectStep id) _)
    · intro _
      apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
      intro _
      cases call
      all_goals repeat' first
        | exact hs
        | exact ht
        | exact hr
        | exact hx
        | exact ha
        | exact hc
        | exact projectsPrefix_lift ρ _
        | exact projectsPrefix_pure ρ id _
        | apply projectsPrefix_bind ρ id id
        | (maintenance_intro; try dsimp only [id])
  unfold syscallWith
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro _
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro _
  apply projectsPrefix_bind ρ id id (projectsPrefix_lift ρ _)
  intro _
  cases hn : syscallNr call
  all_goals repeat' first
    | with_reducible exact tail
    | exact projectsPrefix_lift ρ _
    | exact projectsPrefix_pure ρ id _
    | apply projectsPrefix_bind ρ id id
    | (maintenance_intro; try dsimp only [id])
    | split

end Leanux.Proofs.WG.Configuration

namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Configuration

def syscallCreate : PrefixM Event Int := syscallWith (fun {_} a => liftPrefix a) dispatchCreate (liftPrefix Env.runSendWorkers) (liftPrefix Env.idleTimers)
  (liftPrefix Env.routeIntoWg0) (liftPrefix Env.afterXmit) (liftPrefix Env.afterAdvance) (liftPrefix Env.netnsCleanup) .wgCreate

def syscallDelete : PrefixM Event Int := syscallWith (fun {_} a => liftPrefix a) dispatchDelete (liftPrefix Env.runSendWorkers) (liftPrefix Env.idleTimers)
  (liftPrefix Env.routeIntoWg0) (liftPrefix Env.afterXmit) (liftPrefix Env.afterAdvance) (liftPrefix Env.netnsCleanup) .wgDelete

theorem syscallCreate_routing : ProjectsPrefix routingEvent id syscallCreate (syscallObserved .wgCreate) := by
  rw [syscallObserved_factor]
  have h := syscallWith_projects routingEvent dispatchCreate_routing
    (projectsPrefix_pure routingEvent id ()) (projectsPrefix_pure routingEvent id ())
    (projectsPrefix_pure routingEvent id ()) (projectsPrefix_pure routingEvent id ())
    (projectsPrefix_pure routingEvent id ()) (projectsPrefix_pure routingEvent id ()) .wgCreate
  exact h

theorem syscallCreate_rx : ProjectsPrefix rxEvent id syscallCreate (RxHistory.syscall .wgCreate) := by
  rw [syscallRx_factor]
  have h := syscallWith_projects rxEvent dispatchCreate_rx
    (projectsPrefix_pure rxEvent id ()) (projectsPrefix_pure rxEvent id ())
    (projectsPrefix_pure rxEvent id ()) (projectsPrefix_pure rxEvent id ())
    (projectsPrefix_pure rxEvent id ()) (projectsPrefix_pure rxEvent id ()) .wgCreate
  exact h

theorem syscallDelete_routing : ProjectsPrefix routingEvent id syscallDelete (syscallObserved .wgDelete) := by
  rw [syscallObserved_factor]
  have h := syscallWith_projects routingEvent dispatchDelete_routing
    (projectsPrefix_pure routingEvent id ()) (projectsPrefix_pure routingEvent id ())
    (projectsPrefix_pure routingEvent id ()) (projectsPrefix_pure routingEvent id ())
    (projectsPrefix_pure routingEvent id ()) (projectsPrefix_pure routingEvent id ()) .wgDelete
  exact h

theorem syscallDelete_rx : ProjectsPrefix rxEvent id syscallDelete (RxHistory.syscall .wgDelete) := by
  rw [syscallRx_factor]
  have h := syscallWith_projects rxEvent dispatchDelete_rx
    (projectsPrefix_pure rxEvent id ()) (projectsPrefix_pure rxEvent id ())
    (projectsPrefix_pure rxEvent id ()) (projectsPrefix_pure rxEvent id ())
    (projectsPrefix_pure rxEvent id ()) (projectsPrefix_pure rxEvent id ()) .wgDelete
  exact h

theorem syscallCreate_erases : ErasesPrefix syscallCreate (Leanux.syscall .wgCreate) := by
  intro w h
  have hp := congrArg Prod.fst (syscallCreate_rx w h)
  have he := RxHistory.syscall_erases .wgCreate w (h.filterMap rxEvent)
  have same := hp.symm.trans he
  change ((runPrefix syscallCreate w h).1.map (fun (x,v) => (x,v))) = _ at same
  cases hr : (runPrefix syscallCreate w h).1 <;> simpa only [hr,Except.map] using same

theorem syscallDelete_erases : ErasesPrefix syscallDelete (Leanux.syscall .wgDelete) := by
  intro w h
  have hp := congrArg Prod.fst (syscallDelete_rx w h)
  have he := RxHistory.syscall_erases .wgDelete w (h.filterMap rxEvent)
  have same := hp.symm.trans he
  change ((runPrefix syscallDelete w h).1.map (fun (x,v) => (x,v))) = _ at same
  cases hr : (runPrefix syscallDelete w h).1 <;> simpa only [hr,Except.map] using same

end Leanux.Proofs.WG.Queues.RoutingJoint
