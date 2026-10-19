import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerCompanion
import Leanux.Proofs.WG.Queues.HolderEntryDispatch

/-! The companion projection separates WG-store transport from suspended
actor state. An arbitrary ambient edit never supplies a missing idle fact. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits TransmitSecurity RetirementSecurity CausalJournal HandshakeSecurity

theorem Companions.store (before : Companions w)
    (same : wgStoreView v.wg=wgStoreView w.wg) : Companions v := by
  obtain ⟨⟨history,cs,entry⟩,positive⟩ := before
  refine ⟨⟨history,cs,HolderEntryDispatch.wg_store entry.1 same,entry.2.store same⟩,?_⟩
  have counts : PeerReference.view v.wg=PeerReference.view w.wg :=
    congrArg (fun s : WGStoreView => fun pid : PeerId => (s.dev.bind fun d => d.peers[pid]?).map Peer.refcount) same
  change PeerReference.Positive (PeerReference.view v.wg)
  rw [counts]
  exact positive

theorem Ready.store (before : Ready h w)
    (same : wgStoreView v.wg=wgStoreView w.wg) (idle : v.ambient.suspended=[]) : Ready h v :=
  ⟨CompleteProduct.store_transport h w v same before.1,before.2.1.store same,
    TxWork.serving_store_transport same before.2.2.1,idle⟩

theorem ready_prepare (trace : Trace) (state : RunnerOperation.State) (h : List Event)
    (before : Ready h state.1) : Ready h (RunnerOperation.prepare trace state) :=
  before.store rfl before.2.2.2

theorem ready_close (h : List Event) (w v : World) (same : v.wg=w.wg)
    (idle : v.ambient.suspended=[]) (incoming : w.ambient.suspended=[])
    (before : Returned h w) : Ready h v :=
  ⟨CompleteProduct.store_transport h w v (congrArg wgStoreView same) before.1,
    before.2.1.store (congrArg wgStoreView same),
    TxWork.serving_store_transport (congrArg wgStoreView same)
      (TxWork.RunnerBoundary.at_idle before.2.2 incoming),idle⟩

theorem ready_initial (net bare : Bool) (w : World)
    (same : wgStoreView w.wg=wgStoreView (initialWG net bare))
    (idle : w.ambient.suspended=[]) : Ready [] w := by
  have companions : Companions {w with wg:=initialWG net bare} :=
    ⟨⟨[],[],RetiredPeer.Outer.initialized net bare _ rfl⟩,PeerReference.initial net bare⟩
  exact ⟨CompleteProduct.store_transport [] {w with wg:=initialWG net bare} w same
      (CompleteProduct.initial net bare w),companions.store same,
    TxWork.RunnerBoundary.at_idle (TxWork.initial_at net bare w same) idle,idle⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
