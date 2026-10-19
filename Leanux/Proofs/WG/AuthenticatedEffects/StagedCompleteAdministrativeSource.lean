import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdministrativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEnvironment
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchSource

/-! Retained syscall arms use the actual dump, lifecycle and native wrappers.
Final cursor repayments stay observed and can settle packet obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Administrative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal Driver NestedPeerRelease
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "complete_administrative_step" : tactic => `(tactic| first
  | (complete_product_head dumpDeviceWith; exact state (CompleteDump.device _))
  | (complete_product_head dumpStartWith; exact state (CompleteDump.start _ _))
  | (complete_product_head dumpReceiveWith; exact state (CompleteDump.receive _))
  | (complete_product_head netlinkRequestWith; apply netlink)
  | (complete_product_head socketCallOnWith; apply socket)
  | (complete_product_wg getNlSock
     exact wg _ (CompleteDump.native _ ((getNlSock_sameWGWorld _).factor dumpView)))
  | (complete_product_wg setNlSock
     exact wg _ (CompleteDump.native _ (setNlSock_sameDump _ _)))
  | (first | complete_product_native skipCutExactly | complete_product_native modifyAmbient
     exact ambient _)
  | complete_outer_step)

theorem retained (call : Syscall) (kept : DispatchRetained call) : Checked (retainedObserved hooks call) := by
  cases call <;> simp only [DispatchRetained] at kept
  all_goals try contradiction
  case wgUp => exact socket _ _ env_up
  case wgDown => exact socket _ _ env_down
  case wgGet ref =>
    simp only [retainedObserved,dumpDispatch,dumpDispatchWith]
    repeat' complete_administrative_step
  case wgGetStart ref =>
    simp only [retainedObserved,dumpDispatch,dumpDispatchWith]
    repeat' complete_administrative_step
  case wgGetRecv =>
    simp only [retainedObserved,dumpDispatch,dumpDispatchWith]
    repeat' complete_administrative_step
  case wgSetMtu n =>
    exact CompleteProduct.native _ (fun h => native_socket _ _ h (native_of_checked (mtu n) h))
  case wgDeladdr family =>
    exact CompleteProduct.native _ (fun h => native_rtnetlink _ h
      (native_of_checked (product_store _ (wgDeladdr_sameKernel family)) h))
  case wgDelroute family named dst plen oif typeCode metric =>
    exact CompleteProduct.native _ (fun h => native_rtnetlink _ h (del_route family named dst plen oif typeCode metric h))
  case wgAddroute dst plen oif typeCode metric mtu nlflags =>
    exact CompleteProduct.native _ (fun h => native_rtnetlink _ h (add_route dst plen oif typeCode metric mtu nlflags h))
  case wgAddaddr addr plen =>
    exact CompleteProduct.native _ (fun h => native_rtnetlink _ h (add_addr addr plen h))
  case wgNetnsClose => exact store _ SyscallFrames.netnsClose_sameWGStore
  case wgAdvance ticks =>
    apply CompleteProduct.native
    intro h
    have files {α : Type} (a : FS.M α) : Preserves (Carrier h) (monadLift a : Leanux.M α) :=
      native_of_checked (fs a) h
    have effect {α : Type} (a : AmbientM α) := native_of_checked (ambient a) h
    have advance := native_of_checked (product_store _ (advance_sameKernel ticks)) h
    change Preserves (Carrier h) (Leanux.dispatch (.wgAdvance ticks))
    dsimp only [Leanux.dispatch]
    routing_tx_source [unsupported] using [files,effect,advance]
  case seccompProbe nr args target strict => cases target <;> exact seccomp _
  case seccompInstall => exact seccomp _
  case seccompPrctl => exact seccomp _
  case seccompCapdrop => exact seccomp _
  case seccompQuery => exact seccomp _
  all_goals exact fs _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.Administrative
