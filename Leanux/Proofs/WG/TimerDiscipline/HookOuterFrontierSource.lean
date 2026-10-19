import Leanux.Proofs.WG.TimerDiscipline.HookConfigurationFrontierSource
import Leanux.Proofs.WG.TimerDiscipline.HookSchedulerFrontierSource
import Leanux.Proofs.WG.TimerDiscipline.HookTrafficFrontierSource
import Leanux.Proofs.Framing.EnvOperations
import Leanux.Proofs.WG.TimerDiscipline.HookOuterFrontierFrames

/-! Counter-frontier transport through every original syscall, with all
configuration, scheduler, traffic and deferred callback obligations discharged. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.HookCommon
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open HandshakeJournal Lifetimes Queues Configuration

theorem inject_frontier (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (HookTraffic.inject family port msg tos ll dest) :=
  HookTraffic.inject_frontier (deferred_frontier .crypt) family port msg tos ll dest

theorem afterBatch_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered HookTraffic.afterBatch :=
  HookTraffic.afterBatch_frontier (deferred_frontier .crypt) (deferred_frontier .sendAll)
    sendOne_frontier schedule_frontier

theorem flood_frontier (count port family : Nat) (msgs : List (List UInt8)) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered
      (HookTraffic.flood count port family msgs) :=
  HookTraffic.flood_frontier inline_frontier afterBatch_frontier count port family msgs

theorem batch_frontier (items : List Env.BatchItem) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (HookTraffic.batch items) :=
  HookTraffic.batch_frontier (HookTraffic.batchItem_frontier inline_frontier) afterBatch_frontier items

theorem observe_frontier :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered observe := by
  unfold observe
  apply (deferred_frontier .idle).bind
  intro _
  apply (HookState.lift_store (fun _ _ h=>h.1)
    (fun h w v=>frontier_wg_store h w.wg v.wg) _ observeTail_sameKernel).bind
  rintro ⟨ret,result⟩
  apply (HookState.ambient (fun _ _ h=>h.1)
    (fun h w v=>frontier_wg_store h w.wg v.wg) _).bind
  intro _
  exact Roaming.RemoteOuterRules.socket _ _ (fun _ _ h=>h.1) files_frontier _ _
    (PrefixPreserves.pure (fun _ _ h=>h.1) ret)

theorem dispatch_frontier (c : Syscall) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (dispatch c) := by
  apply dispatchWith_preserves
  · exact retained_frontier
  · exact set_frontier
  · exact create_frontier
  · exact delete_frontier
  · exact xmit_frontier
  · intro family port msg tos ll dest
    exact Roaming.RemoteOuterRules.socket _ _ (fun _ _ h=>h.1) files_frontier _ _
      (inject_frontier family port msg tos ll dest)
  · exact flood_frontier
  · exact batch_frontier
  · exact observe_frontier

theorem syscall_frontier (c : Syscall) :
    PrefixPreserves (fun h w=>Frontier h w.wg.keypairCounter) Ordered (syscall c) :=
  SyscallSource.preserves (I:=fun h w=>Frontier h w.wg.keypairCounter) (S:=Ordered)
    (fun _ _ h=>h.1) (fun h w v=>frontier_wg_store h w.wg v.wg) c _ _ _ _ _ _ _
    (dispatch_frontier c) (deferred_frontier .sendAll) (deferred_frontier .idle)
    (quiet_frontier _ (product_snapshot_counter Keypairs.EnvFrames.routeIntoWg0_sameSnapshot))
    (deferred_frontier .afterXmit) (deferred_frontier .afterAdvance)
    (quiet_frontier _ (product_snapshot_counter Keypairs.EnvFrames.netnsCleanup_sameSnapshot))

end Leanux.Proofs.WG.TimerDiscipline.HookCommon

