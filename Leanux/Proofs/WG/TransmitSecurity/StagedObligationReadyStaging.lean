import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadySubmit
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationReadyRestore
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySelection

/-! Complete actual staging-source composition. Every native take outcome is
handled, and both consuming branches receive the whole indexed entry bundle.
Only the actual create and queued-initiation source callbacks remain open. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open Staged.Origins AuthenticatedEffects CausalJournal StagedProvenance RetirementSecurity AllocatedObligation
open HandshakeSecurity.StagedConservation

theorem staging (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (Safe : List Event → Prop)
    (entrySafe : ∀ ledger h w, StagedEntry.Inv h ledger debts locals w → Safe h)
    (activeSafe : ∀ ledger generation peer position h,
      SoundHeld.Active ledger debts generation pid peer position h → Safe h)
    (Post : List Event → WGWorld → Ambient → Prop) (postSafe : ∀ h w a, Post h w a → Safe h)
    (idlePost : ∀ h w a, StagedEntry.Inv h ledger debts locals w → Post h w a)
    (queued : ∀ ledger, StatePrefixEnsures (fun h w _ => StagedEntry.Inv h ledger debts locals w)
      Safe (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false) (fun _ => Post))
    (created : ∀ ledger items, StatePrefixEnsures
      (fun h w _ => StagedEntry.Inv h ledger debts (⟨.unpublished,pid,items⟩ :: locals) w ∧
        CreateDisposal.PendingBatch h ledger items)
      Safe (CausalJournal.create pid items) (fun _ => Post)) :
    StatePrefixEnsures (fun h w _ => StagedEntry.Inv h ledger debts locals w) Safe
      (Driver.stagingObserved hooks pid) (fun _ => Post) := by
  intro w a h before
  cases native : ((Take.takePrefix pid).run w).run a with
  | error stop =>
    have selected := (StagedEntry.selection_take_stop pid before a native).1
    rw [HeldSource.staging_factor]
    simp only [StateT.run_bind,runPrefix_bind]
    change runPrefix ((CausalJournal.selection pid).run w) a h = _ at selected
    rw [selected]
    exact ⟨[],by simp,entrySafe _ _ _ before,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let r : Take.Receipt := ⟨pid,⟨value,w,v,a,b⟩⟩
    have valid : r.Valid := native
    cases value with
    | none =>
      obtain ⟨selected,entry⟩ := StagedEntry.selection_idle r valid rfl before
      rw [HeldSource.staging_factor]
      simp only [StateT.run_bind,runPrefix_bind]
      change runPrefix ((CausalJournal.selection pid).run w) a h = _ at selected
      rw [selected]
      exact ⟨[.stagingTaken r,.old (.responder (.selected pid ⟨none,w,v,a,b⟩))],
        by simp [r,List.append_assoc],entrySafe _ _ _ entry,idlePost _ _ _ entry⟩
    | some peer =>
      obtain ⟨after,generation,_,run⟩ := after_take r valid rfl before Safe Post postSafe
      have result := run (activeSafe after generation peer h.length)
        (fun key invalid => no_key after debts locals generation pid peer h.length key invalid Safe
          (activeSafe after generation peer h.length) (entrySafe _) Post (queued _))
        (fun kid packets => submit after debts locals generation pid peer h.length kid packets Safe
          (activeSafe after generation peer h.length) Post created)
      obtain ⟨suffix,extended,safe,post⟩ := result
      refine ⟨[.stagingTaken r] ++ suffix,?_,safe,?_⟩
      · simpa only [runWGPrefix,runStatePrefix,List.append_assoc] using extended
      · cases actual : (runWGPrefix (Driver.stagingObserved hooks pid) w a h).1 with
        | error stop =>
          have actual' := actual
          dsimp only [runWGPrefix,runStatePrefix] at actual'
          rw [actual']
          trivial
        | ok out =>
          obtain ⟨⟨value,u⟩,c⟩ := out
          have actual' := actual
          dsimp only [runWGPrefix,runStatePrefix] at actual'
          rw [actual']
          simpa only [r,runWGPrefix,runStatePrefix,actual'] using post

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.ReadyCarrier
