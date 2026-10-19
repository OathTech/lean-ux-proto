import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendFinalNative

/-! Exact full-run projection to original native append cuts. The same Driver
keeps all native scheduling and state transitions; the raw target independently
observes actual socket appends and retains them across every later Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity

theorem timer (d : Device) (bound : UInt64) (pid : PeerId) (kind : PeerTimer) (entry : WheelEntry) :
    ProjectsPrefix raw? (fun _ => 0) (CausalJournal.hooks.timerSelected d bound pid kind entry)
      (RawAppend.hooks.timerSelected d bound pid kind entry) := by
  intro w h
  change (Except.ok (ε := Stop) (0,w),h.filterMap raw?) =
    ((runPrefix (CausalSources.timerEnter CausalJournal.Event.scope
      (CausalJournal.Event.old ∘ Journal.Event.timerSelected) d bound pid kind entry) w h).1.map
      (fun (_,v) => (0,v)),
      (runPrefix (CausalSources.timerEnter CausalJournal.Event.scope
        (CausalJournal.Event.old ∘ Journal.Event.timerSelected) d bound pid kind entry) w h).2.filterMap raw?)
  simp only [CausalSources.timerEnter,TimerDispatch.scope_run]
  change (Except.ok (ε := Stop) (0,w),h.filterMap raw?) =
    (Except.ok (ε := Stop) (0,w),
      ((h ++ [CausalJournal.Event.old (.timerSelected ⟨d,bound,pid,kind,entry,w⟩)]) ++
        [CausalJournal.Event.scope (.entered ⟨(h ++ [CausalJournal.Event.old (.timerSelected ⟨d,bound,pid,kind,entry,w⟩)]).length,
          .timer bound pid kind entry⟩)]).filterMap raw?)
  simp only [List.filterMap_append,List.filterMap_cons,List.filterMap_nil,raw?,journal?,List.append_nil]

theorem hooks_projects : Driver.HooksProjects raw? CausalJournal.hooks RawAppend.hooks where
  stagedPurge := purge
  peerRelease := release
  deliver := DeliverySource.observed_projects raw? CausalJournal.Event.delivery (fun _ => rfl)
  keepalivePrepare := fun _ => Journal.state_receipt_projects raw? _ _ _ (fun _ => rfl)
    (Driver.Projection.state_lift raw? _)
  fixture := ⟨(fun _ => 0),
    (fun trigger => CausalScope.enterState_projects CausalJournal.Event.scope (.fixture trigger) raw? (fun _ => rfl)),
    (fun token => CausalScope.leaveState_projects CausalJournal.Event.scope token raw? (fun _ => rfl))⟩
  handshake := handshake
  flushedSend := flushed
  armTimer := effects.arm
  queueSend := effects.append
  candidate := ⟨(fun _ => 0),
    (fun skb packet => CausalScope.enter_projects CausalJournal.Event.scope (.candidate skb packet) raw? (fun _ => rfl)),
    (fun token => CausalScope.leave_projects CausalJournal.Event.scope token raw? (fun _ => rfl)),
    (fun entry _ _ projected => CausalScope.prefix_projects CausalJournal.Event.scope (.stackInput entry) raw?
      (fun _ => rfl) _ _ (fun _ => projected))⟩
  timer := ⟨(fun _ => 0),timer,
    (fun token => CausalScope.leave_projects CausalJournal.Event.scope token raw? (fun _ => rfl))⟩
  prepare := prepare
  counterCheck := counter
  selection := selection
  confirmation := confirmation
  session := session
  reserve := reserve
  allocate := allocate
  create := create
  front := front
  poll := poll
  encrypt := encrypt
  transmit := transmit

/-- Every raw original-append occurrence is retained in exactly the projected
final journal position order, through native delivery clears and later Stops. -/
theorem execute_projects (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter raw? id (CausalJournal.execute trace placeholders) (RawAppend.execute trace placeholders) :=
  Driver.execute_projects hooks_projects trace placeholders

theorem initialized_history (trace : Runner.Trace) (placeholders : Bool) :
    (runPrefixOuter (RawAppend.execute trace placeholders) []).2 =
      (runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap raw? := by
  exact congrArg Prod.snd (execute_projects trace placeholders [])

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
