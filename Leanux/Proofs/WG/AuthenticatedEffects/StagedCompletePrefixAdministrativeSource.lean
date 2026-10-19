import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdministrativeFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteAdministrativeSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDumpClosed
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDumpFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixSchedulerFrames
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpDispatchSource

/-! Retained syscall arms preserve every journal prefix through actual dump
callbacks and literal native wrappers. Lifecycle source contracts stay explicit.
Final cursor repayments stay observed and can settle packet obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Administrative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
open TransmitSecurity RetirementSecurity CausalJournal Driver NestedPeerRelease
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

macro "prefix_administrative_step" : tactic => `(tactic| first
  | (prefix_product_head dumpDeviceWith; exact state (Dump.device _))
  | (prefix_product_head dumpStartWith; exact state (Dump.start _ _))
  | (prefix_product_head dumpReceiveWith; exact state (Dump.receive _))
  | (prefix_product_head netlinkRequestWith; apply netlink)
  | (prefix_product_head socketCallOnWith; apply socket)
  | (prefix_product_wg getNlSock
     exact wg _ (Dump.native _ ((getNlSock_sameWGWorld _).factor dumpView)))
  | (prefix_product_wg setNlSock
     exact wg _ (Dump.native _ (setNlSock_sameDump _ _)))
  | (first | prefix_product_native skipCutExactly | prefix_product_native modifyAmbient
     exact ambient _)
  | prefix_outer_step)

theorem retained (env_up : Checked (envUpObserved hooks))
    (env_down : Checked (envDownObserved hooks)) (call : Syscall) (kept : DispatchRetained call) : Checked (retainedObserved hooks call) := by
  have endpoint := CompleteProduct.Administrative.retained call kept
  cases call <;> simp only [DispatchRetained] at kept
  all_goals try contradiction
  case wgUp => exact socket _ _ env_up
  case wgDown => exact socket _ _ env_down
  case wgGet ref =>
    simp only [retainedObserved,dumpDispatch,dumpDispatchWith]
    repeat' prefix_administrative_step
  case wgGetStart ref =>
    simp only [retainedObserved,dumpDispatch,dumpDispatchWith]
    repeat' prefix_administrative_step
  case wgGetRecv =>
    simp only [retainedObserved,dumpDispatch,dumpDispatchWith]
    repeat' prefix_administrative_step
  all_goals exact Ensures.quiet endpoint (fun _ _=>rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product.Administrative
