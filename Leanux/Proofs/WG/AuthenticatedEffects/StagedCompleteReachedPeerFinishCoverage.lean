import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerFinishFrames

/-! Complete native coverage of releaseFinish after the actual counted
receipt. The two identity writes preserve the same packet ledger, while a
pending cached timer stops at the original guard and retains that receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Finish
open Leanux Leanux.WG Leanux.Proofs.Logged
open HandshakeSecurity.StagedDisposal CompleteCarrier TransmitSecurity
open Staged.Obligations AllocatedObligation

inductive Cases (pid : PeerId) (p : Peer) (w : WGWorld) (a : Ambient) :
    Except Stop ((Unit × WGWorld) × Ambient) → Prop where
  | busy (found : pending p=some timer) :
      Cases pid p w a (.error (.invariant s!"peer {pid} released with its {repr timer} timer pending"))
  | quiet (found : pending p=none) :
      Cases pid p w a (.ok (((),timersWorld pid w),workClock pid a))

theorem cases (pid : PeerId) (p : Peer) (w : WGWorld) (a : Ambient) :
    Cases pid p w a (((releaseFinish pid p).run w).run a) := by
  cases found : pending p with
  | some timer => rw [stopped found]; exact .busy found
  | none =>
    have performed := prefix_run found .timersRetired pid w a
    have final := point_continuation performed
    change ((releaseFinish pid p).run w).run a=.ok (((),timersWorld pid w),workClock pid a) at final
    rw [final]
    exact .quiet found

theorem Cases.literal (path : Cases pid p w a result) :
    ((releaseFinish pid p).run w).run a=result := by
  cases path with
  | busy found => exact stopped found pid w a
  | quiet found => exact point_continuation (prefix_run found .timersRetired pid w a)

/-- The carrier is derived at the actual counted release receipt. Every
subsequent native write uses that same ledger; the original observer and its
remaining finish agree at each quiet cut. A busy guard asserts no error world. -/
theorem after_release (before : Accounted history ledger debts locals w)
    (native : ((releaseCut peer).run w).run a=.ok ((some (pid,p),v),b)) :
    ∃ next,
      Staged.Obligations.Step ledger next ∧ AllocatedFrame ledger next ∧
      PeerRelease.Successor (some (pid,p)) w history.length ledger next ∧
      let recorded := history++[releaseEvent peer (some (pid,p)) w v a b]
      Accounted recorded next debts locals v ∧
      Cases pid p v b (((releaseFinish pid p).run v).run b) ∧
      (pending p=none → ∀ site : Site,
        ((prefixAt site pid p).run v).run b=
          .ok (((),atWorld site pid v),atClock site pid b) ∧
        Accounted recorded next debts locals (atWorld site pid v) ∧
        runWGPrefix (CausalJournal.peerRelease peer) w a history=
          runWGPrefix (liftWGPrefix (tailAt site pid)) (atWorld site pid v) (atClock site pid b) recorded) := by
  obtain ⟨next,step,frame,successor,entry,complete⟩ :=
    StagedTerminalComplete.Source.original_native_entry peer before.entry before.complete a b native
  have accounted : Accounted (history++[releaseEvent peer (some (pid,p)) w v a b]) next debts locals v :=
    ⟨entry,complete⟩
  refine ⟨next,step,frame,successor,accounted,cases pid p v b,?_⟩
  intro quiet site
  exact ⟨prefix_run quiet site pid v b,prefix_accounted accounted site,
    release_continuation native (prefix_run quiet site pid v b)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement.Finish
