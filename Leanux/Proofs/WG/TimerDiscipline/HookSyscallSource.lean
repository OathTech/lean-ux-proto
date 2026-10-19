import Leanux.Proofs.WG.TimerDiscipline.HookOuterRulesSource
import Leanux.Proofs.WG.TimerDiscipline.HookRunnerSource
/-! The actual top-level dispatch and syscall, including inline maintenance,
traffic, observation waits and every deferred tail. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged HandshakeJournal Lifetimes Queues Configuration

def set (attrs : DeviceAttrs) : Obs Int :=
  netlinkRequestWith (fun {_} a=>liftPrefix a) (liftWGObserver (deviceCommand attrs))
def down : Obs Int :=
  socketCallOnWith (fun {_} a=>liftPrefix a) SENDER_FD HandshakeMaintenance.envDown
def delete : Obs Int :=
  rtnetlinkRequestWith (fun {_} a=>liftPrefix a) HandshakeMaintenance.envDelete
def observe : Obs Int := do
  deferred .idle
  let (ret,result) ← liftPrefix Environment.observeTail
  liftPrefix (modifyAmbient fun w=>{w with extraOut:=
    (["datagrams","replies","stats"].map (fun k=>(k,result.getObjValD k)))})
  socketCallOnWith (fun {_} a=>liftPrefix a) LISTEN4_FD (pure ret)

def retained : Syscall → Obs Int
  | .wgDown => down
  | c => liftPrefix (Leanux.dispatch c)

def dispatch (c : Syscall) : Obs Int :=
  dispatchWith retained set (liftPrefix (Leanux.dispatch .wgCreate)) delete
    (fun family addr bytes opts=>liftPrefix (Leanux.dispatch (.wgXmit family addr bytes opts)))
    (fun family port msg tos ll dest=>socketCallOnWith (fun {_} a=>liftPrefix a)
      SENDER_FD (HookTraffic.inject family port msg tos ll dest))
    HookTraffic.flood HookTraffic.batch observe c

def syscall (c : Syscall) : Obs Int :=
  syscallWith (fun {_} a=>liftPrefix a) (dispatch c)
    (deferred .sendAll) (deferred .idle) (liftPrefix Env.routeIntoWg0)
    (deferred .afterXmit) (deferred .afterAdvance) (liftPrefix Env.netnsCleanup) c

theorem set_erases (attrs : DeviceAttrs) :
    ErasesPrefix (set attrs) (Leanux.dispatch (.wgSet attrs)) :=
  netlinkRequestWith_erases (liftWGObserver_erases (deviceCommand_erases attrs))
theorem down_erases : ErasesPrefix down (Leanux.dispatch .wgDown) :=
  socketCallOnWith_erases _ HandshakeMaintenance.envDown_erases
theorem delete_erases : ErasesPrefix delete (Leanux.dispatch .wgDelete) :=
  rtnetlink_erases _ _ HandshakeMaintenance.envDelete_erases
theorem observe_erases : ErasesPrefix observe (Leanux.dispatch .wgObserve) := by
  unfold observe Leanux.dispatch
  rw [Environment.observe_eq]
  simp only [bind_assoc]
  apply erasesPrefix_bind (deferred_erases .idle)
  intro _
  apply erasesPrefix_bind (erasesPrefix_lift _)
  rintro ⟨ret,result⟩
  exact erasesPrefix_bind (erasesPrefix_lift _)
    (fun _=>socketCallOnWith_erases _ (erasesPrefix_pure ret))

theorem dispatch_erases (c : Syscall) : ErasesPrefix (dispatch c) (Leanux.dispatch c) := by
  cases c
  case wgSet attrs => exact set_erases attrs
  case wgDelete => exact delete_erases
  case wgDown => exact down_erases
  case wgInject family port msg tos ll dest =>
    exact socketCallOnWith_erases _ (HookTraffic.inject_erases family port msg tos ll dest)
  case wgFlood count port family msgs => exact HookTraffic.flood_erases count port family msgs
  case wgBatch items wait => exact HookTraffic.batch_erases items
  case wgObserve => exact observe_erases
  all_goals exact erasesPrefix_lift _

theorem syscall_erases (c : Syscall) : ErasesPrefix (syscall c) (Leanux.syscall c) := by
  let lower : PrefixM Empty Int := syscallWith (fun {_} a=>liftPrefix a)
    (liftPrefix (Leanux.dispatch c)) (liftPrefix Env.runSendWorkers)
    (liftPrefix Env.idleTimers) (liftPrefix Env.routeIntoWg0)
    (liftPrefix Env.afterXmit) (liftPrefix Env.afterAdvance) (liftPrefix Env.netnsCleanup) c
  apply Progress.CommittedRuns.Syscalls.empty_projects_erases
    (syscall c) (Configuration.syscallObserved c) lower
  · exact syscallWith_projects _
      (Noise.DriverTags.Initialized.empty_projection _ _ (dispatch_erases c))
      (Noise.DriverTags.Initialized.empty_projection _ _ (deferred_erases .sendAll))
      (Noise.DriverTags.Initialized.empty_projection _ _ (deferred_erases .idle))
      (projectsPrefix_lift _ _)
      (Noise.DriverTags.Initialized.empty_projection _ _ (deferred_erases .afterXmit))
      (Noise.DriverTags.Initialized.empty_projection _ _ (deferred_erases .afterAdvance))
      (projectsPrefix_lift _ _) c
  · rw [Configuration.syscallObserved_factor]
    exact syscallWith_projects _
      (Noise.DriverTags.Initialized.empty_projection _ _ (Configuration.dispatchObserved_erases c))
      (projectsPrefix_lift _ _) (projectsPrefix_lift _ _) (projectsPrefix_lift _ _)
      (projectsPrefix_lift _ _) (projectsPrefix_lift _ _) (projectsPrefix_lift _ _) c
  · exact Configuration.syscallObserved_erases c

structure OuterContracts (S : List Event → Prop) : Prop where
  device : ∀ attrs,StatePrefixPreserves (fun h _ _=>S h) S (deviceCommand attrs)
  down : PrefixPreserves (fun h _=>S h) S HandshakeMaintenance.envDown
  delete : PrefixPreserves (fun h _=>S h) S HandshakeMaintenance.envDelete
  inject : ∀ family port msg tos ll dest,PrefixPreserves (fun h _=>S h) S
    (HookTraffic.inject family port msg tos ll dest)
  flood : ∀ count port family msgs,PrefixPreserves (fun h _=>S h) S (HookTraffic.flood count port family msgs)
  batch : ∀ items,PrefixPreserves (fun h _=>S h) S (HookTraffic.batch items)
  deferred : ∀ c,PrefixPreserves (fun h _=>S h) S (HookCommon.deferred c)

theorem outer_valid : OuterContracts ValidHistory :=
  ⟨deviceCommand_valid,HandshakeMaintenance.envDown_valid,HandshakeMaintenance.envDelete_valid,
    HookTraffic.inject_valid,HookTraffic.flood_valid,HookTraffic.batch_valid,deferred_valid⟩
theorem outer_paired : OuterContracts Paired :=
  ⟨deviceCommand_paired,HandshakeMaintenance.envDown_paired,HandshakeMaintenance.envDelete_paired,
    HookTraffic.inject_paired,HookTraffic.flood_paired,HookTraffic.batch_paired,deferred_paired⟩

theorem set_preserves (S : List Event → Prop) (hc : OuterContracts S) (attrs : DeviceAttrs) :
    PrefixPreserves (fun h _=>S h) S (set attrs) :=
  Roaming.RemoteOuterRules.netlink (fun h _=>S h) S (fun _ _ h=>h) (fun _=>quiet_preserves S _)
    (fun _=>quiet_preserves S _) _ (hc.device attrs).liftWGObserver.preserves

theorem down_preserves (S : List Event → Prop) (hc : OuterContracts S) :
    PrefixPreserves (fun h _=>S h) S down :=
  Roaming.RemoteOuterRules.socket (fun h _=>S h) S (fun _ _ h=>h) (fun _=>quiet_preserves S _) _ _ hc.down
theorem delete_preserves (S : List Event → Prop) (hc : OuterContracts S) :
    PrefixPreserves (fun h _=>S h) S delete :=
  rtnetlink_preserves S _ hc.delete
theorem observe_preserves (S : List Event → Prop) (hc : OuterContracts S) :
    PrefixPreserves (fun h _=>S h) S observe := by
  unfold observe
  apply (hc.deferred .idle).bind
  intro _
  apply (quiet_preserves S _).bind
  rintro ⟨ret,result⟩
  apply (quiet_preserves S _).bind
  intro _
  exact Roaming.RemoteOuterRules.socket (fun h _=>S h) S (fun _ _ h=>h)
    (fun _=>quiet_preserves S _) _ _ (PrefixPreserves.pure (I:=fun h _=>S h) (S:=S) (fun _ _ h=>h) ret)

theorem dispatch_preserves (S : List Event → Prop) (hc : OuterContracts S) (c : Syscall) :
    PrefixPreserves (fun h _=>S h) S (dispatch c) := by
  apply dispatchWith_preserves
  · intro c _
    cases c
    case wgDown => exact down_preserves S hc
    all_goals exact quiet_preserves S _
  · exact set_preserves S hc
  · exact quiet_preserves S _
  · exact delete_preserves S hc
  · intro _ _ _ _; exact quiet_preserves S _
  · intro family port msg tos ll dest
    exact Roaming.RemoteOuterRules.socket (fun h _=>S h) S (fun _ _ h=>h) (fun _=>quiet_preserves S _) _ _
      (hc.inject family port msg tos ll dest)
  · exact hc.flood
  · exact hc.batch
  · exact observe_preserves S hc

theorem syscall_preserves (S : List Event → Prop) (hc : OuterContracts S) (c : Syscall) :
    PrefixPreserves (fun h _=>S h) S (syscall c) :=
  SyscallSource.preserves (I:=fun h _=>S h) (S:=S)
    (fun _ _ h=>h) (fun _ _ _ _ h=>h) c _ _ _ _ _ _ _
    (dispatch_preserves S hc c) (hc.deferred .sendAll) (hc.deferred .idle)
    (quiet_preserves S _) (hc.deferred .afterXmit) (hc.deferred .afterAdvance) (quiet_preserves S _)

theorem syscall_valid (c : Syscall) :
    PrefixPreserves (fun h _=>ValidHistory h) ValidHistory (syscall c) :=
  syscall_preserves ValidHistory outer_valid c
theorem syscall_paired (c : Syscall) :
    PrefixPreserves (fun h _=>Paired h) Paired (syscall c) :=
  syscall_preserves Paired outer_paired c

end Leanux.Proofs.WG.TimerDiscipline.HookCommon
