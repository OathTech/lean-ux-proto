import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPeerRetirementReceipt

/-! Complete original observer outcomes retain the fixed primitive source
case and actual receipt suffix. The remaining releaseFinish is a named
native child, not an inferred silent frame or an invented stopped world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Obligations CausalJournal CompleteCarrier
open HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000

inductive ObservedRelease (peer : Option PeerId) (w : WGWorld) (a : Ambient)
    (h : List CausalJournal.Event) :
    Except Stop ((Unit × WGWorld) × Ambient) × List CausalJournal.Event → Prop where
  | cutStopped (path : ReleaseCase peer w a (.error stop)) :
      ObservedRelease peer w a h (.error stop,h)
  | noFinish (path : ReleaseCase peer w a (.ok ((none,v),b))) :
      ObservedRelease peer w a h (.ok (((),v),b),h++[releaseEvent peer none w v a b])
  | finish (path : ReleaseCase peer w a (.ok ((some (pid,p),v),b)))
      (child : ((releaseFinish pid p).run v).run b=result) :
      ObservedRelease peer w a h (result,h++[releaseEvent peer (some (pid,p)) w v a b])

/-- Every actual observer outcome has its original primitive branch; both
failed tests/guards and failures in the subsequent finish are distinguished. -/
theorem observed_release_cases (peer : Option PeerId) (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event) :
    ObservedRelease peer w a h (runWGPrefix (CausalJournal.peerRelease peer) w a h) := by
  have path := release_cases peer w a
  cases native : ((releaseCut peer).run w).run a with
  | error stop =>
    rw [release_stopped native]
    exact .cutStopped (native ▸ path)
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩:=out
    cases value with
    | none =>
      rw [release_none_recorded native]
      exact .noFinish (native ▸ path)
    | some pair =>
      obtain ⟨pid,p⟩:=pair
      rw [release_recorded native]
      exact .finish (native ▸ path) rfl

theorem ObservedRelease.literal (path : ObservedRelease peer w a h result) :
    runWGPrefix (CausalJournal.peerRelease peer) w a h=result := by
  cases path with
  | cutStopped path => exact release_stopped path.literal
  | noFinish path => exact release_none_recorded path.literal
  | finish path child => rw [release_recorded path.literal,child]

/-- Receipt emission is the sole history change, even if the actual finish
stops; a projection that ignores it preserves the entire previous history. -/
theorem release_projection (rho : CausalJournal.Event → Option E)
    (quiet : ∀ value v b, rho (releaseEvent peer value w v a b)=none) :
    ((runWGPrefix (CausalJournal.peerRelease peer) w a h).2.filterMap rho)=h.filterMap rho := by
  generalize performed : runWGPrefix (CausalJournal.peerRelease peer) w a h=result
  have path := observed_release_cases peer w a h
  rw [performed] at path
  cases path with
  | cutStopped => rfl
  | noFinish => simp [List.filterMap_append,quiet]
  | finish => simp [List.filterMap_append,quiet]

theorem purge_projection (rho : CausalJournal.Event → Option E)
    (quiet : ∀ v b, rho (purgeEvent pid w v a b)=none) :
    ((runWGPrefix (CausalJournal.stagedPurge pid) w a h).2.filterMap rho)=h.filterMap rho := by
  rw [StagedEntry.Purge.run]
  cases native : ((purgeStagedPackets pid).run w).run a with
  | error stop => rfl
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩:=out
    cases value
    change (h++[purgeEvent pid w v a b]).filterMap rho=h.filterMap rho
    simp [List.filterMap_append,quiet]

/-- Purge's complete observer classification includes its intermediate
charge cut on every normal branch, rather than only the final empty queue. -/
theorem observed_purge_cases (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List CausalJournal.Event) :
    (∃ stop, ((getPeer pid).run w).run a=.error stop ∧
      runWGPrefix (CausalJournal.stagedPurge pid) w a h=(.error stop,h)) ∨
    (∃ d p, w.dev=some d ∧ d.peers[pid]?=some p ∧
      ((purgeChargeTo pid).run w).run a=.ok ((p,charged p d w),a) ∧
      runWGPrefix (CausalJournal.stagedPurge pid) w a h=
        (.ok (((),cleared pid p d w),a),h++[purgeEvent pid w (cleared pid p d w) a a])) := by
  rcases purge_cases pid w a with ⟨stop,read,failed⟩ | ⟨d,p,device,resident,charged,_⟩
  · refine Or.inl ⟨stop,read,?_⟩
    rw [StagedEntry.Purge.run,failed]
  · exact Or.inr ⟨d,p,device,resident,charged,purge_recorded device resident⟩

theorem release_old :
    ((runWGPrefix (CausalJournal.peerRelease peer) w a h).2.filterMap old?)=h.filterMap old? :=
  release_projection old? (by intros; rfl)

theorem purge_old :
    ((runWGPrefix (CausalJournal.stagedPurge pid) w a h).2.filterMap old?)=h.filterMap old? :=
  purge_projection old? (by intros; rfl)

/-- Exact final-erasure receipt and carrier survive the actual failed
finish. Only the completed pre-finish world is asserted. -/
theorem release_finish_stopped (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (tested : (testAmbient p.refcount).run (entryClock a)=.ok (true,b))
    (quiet : queued p=false)
    (failed : ((releaseFinish pid p).run (finalWorld pid p d w)).run (indexClock pid d b)=.error stop) :
    let history := h++[releaseEvent (some pid) (some (pid,p)) w (finalWorld pid p d w) a (indexClock pid d b)]
    let next := settle (cohort ledger pid p d) (.counted h.length .finalRelease) ledger
    runWGPrefix (CausalJournal.peerRelease (some pid)) w a h=(.error stop,history) ∧
      Accounted history next debts locals (finalWorld pid p d w) := by
  refine ⟨?_,(release_accounted before device resident tested quiet).1⟩
  rw [release_recorded (erase_prefix device resident tested quiet),failed]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.PeerRetirement
