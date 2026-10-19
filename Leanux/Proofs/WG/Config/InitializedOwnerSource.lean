import Leanux.Proofs.WG.Config.InitializedOwnerAccountClaims
import Leanux.Proofs.WG.Config.OwnerDriverSource
import Leanux.Proofs.WG.Config.InitializedOwnerModel
import Leanux.Proofs.WG.Config.OwnerRunnerNormalSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerDriver
open Lean Leanux Leanux.WG AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open Leanux.Proofs.WG.Config.OwnerConfiguration

theorem initial (net bare : Bool) (w : World)
    (same : wgStoreView w.wg=wgStoreView (Runner.initialWG net bare)) : Inv [] w := by
  refine ⟨⟨[],Index.Reached.initial_entry net bare w same⟩,?_⟩
  intro d device
  exact optionalReady_initial net bare d ((congrArg WGStoreView.dev same).symm.trans device)

theorem initialized
    (trace : Runner.Trace) (shape : Configuration.TraceAddressShape trace)
    (placeholders : Bool) (json : Json) (w : World) (history : List RxHistory.Event)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (json,w),history)) :
    Inv history w :=
  OwnerRunnerNormal.executeTraceWith_normal_shaped_variant Inv OwnerChecks.Safe
    safe store Configuration.SyscallAddressShape RxHistory.syscall syscall trace
    (fun op member results ends index=>Configuration.toSyscall_shape results ends index op
      (shape op member)) placeholders
    (fun w same=>initial trace.net trace.bare w same) run

/-- Concrete syscall contracts yield ownership at the same initialized inspection
endpoint. No equality of returned JSON is used to identify states. -/
theorem inspection_ready
    (trace : Runner.Trace) (shape : Configuration.TraceAddressShape trace)
    (placeholders : Bool) (json : Json) (final : Campaign2.Product.Snapshot)
    (run : (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final)) :
    ProjectedOptionalReady final.toSnapshot := by
  obtain ⟨w,history,ledger,actual,projection,certificate,holders⟩ :=
    (InitializedRouting.normal trace shape placeholders json final run).2.2.2.2.2
  subst final
  exact (initialized trace shape placeholders json w history actual).2

end Leanux.Proofs.WG.Config.OwnerDriver
