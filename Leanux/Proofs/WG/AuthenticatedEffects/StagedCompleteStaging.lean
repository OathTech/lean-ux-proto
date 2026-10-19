import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNoKey
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSubmit
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySelection

/-! Whole actual staging carries both accounting directions, including Stop
after take and before borrowing, rejection restoration, and publication. All
consuming callbacks are concrete; only interpretation of retained cuts as the
caller's history safety predicate is supplied by the caller. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations RetirementSecurity
open AllocatedObligation CausalJournal CompleteCarrier StagedTerminalComplete
open HandshakeSecurity.StagedConservation

theorem after_take (r : Take.Receipt) (native : r.Valid) (chosen : r.run.value = some peer)
    (before : Accounted history ledger debts locals r.run.before) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h)
    (activeSafe : ∀ ledger generation position h,
      Active ledger debts generation r.pid peer position h → Safe h) :
    let out := runWGPrefix (Driver.stagingObserved hooks r.pid) r.run.before r.run.ambientBefore history
    ∃ suffix, out.2 = (history ++ [.stagingTaken r]) ++ suffix ∧ Safe out.2 ∧
      match out.1 with
      | .error _ => True
      | .ok ((_,w),a) => Carrier debts locals out.2 w a := by
  obtain ⟨after,generation,_,_,held⟩ := taken r native chosen before
  exact SelectionCarrier.after_take r native chosen
    (Ready after debts locals generation r.pid peer history.length) Safe
    (fun _ _ _ before => activeSafe _ _ _ _ before.active) held
    (borrow after debts locals generation r.pid peer history.length Safe (activeSafe _ _ _))
    (fun _ _ _ run before => selected_event before run) (Carrier debts locals)
    (fun keypair => checked after debts locals generation r.pid peer history.length keypair Safe
      (activeSafe _ _ _) (Carrier debts locals)
      (fun h w _ after => after.elim (fun ledger => accountSafe ledger locals h w))
      (HeldSource.noKey r.pid peer) (HeldSource.submit r.pid)
      (fun key invalid => no_key after debts locals generation r.pid peer history.length key invalid Safe
        (activeSafe _ _ _) (fun ledger => accountSafe ledger locals))
      (fun kid packets => submit after debts locals generation r.pid peer history.length kid packets Safe
        (activeSafe _ _ _) accountSafe))

theorem staging_fixed (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h)
    (activeSafe : ∀ ledger generation peer position h,
      Active ledger debts generation pid peer position h → Safe h) :
    StatePrefixEnsures (fun h w _ => Accounted h ledger debts locals w) Safe
      (Driver.stagingObserved hooks pid) (fun _ => Carrier debts locals) := by
  intro w a h before
  cases native : ((Take.takePrefix pid).run w).run a with
  | error stop =>
    have selected := (StagedEntry.selection_take_stop pid before.entry a native).1
    rw [HeldSource.staging_factor]
    simp only [StateT.run_bind,runPrefix_bind]
    change runPrefix ((CausalJournal.selection pid).run w) a h = _ at selected
    rw [selected]
    exact ⟨[],by simp,accountSafe _ _ _ _ before,True.intro⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let r : Take.Receipt := ⟨pid,⟨value,w,v,a,b⟩⟩
    have valid : r.Valid := native
    cases value with
    | none =>
      obtain ⟨selected,entry⟩ := StagedEntry.selection_idle r valid rfl before.entry
      have complete := (before.complete.append_quiet
        (suffix := [Event.stagingTaken r])
        (fun _ member => by cases List.mem_singleton.mp member; intro pos; rfl)).append_quiet
        (suffix := [Event.old (.responder (.selected pid ⟨none,w,v,a,b⟩))])
        (fun _ member => by cases List.mem_singleton.mp member; intro pos; rfl)
      rw [HeldSource.staging_factor]
      simp only [StateT.run_bind,runPrefix_bind]
      change runPrefix ((CausalJournal.selection pid).run w) a h = _ at selected
      rw [selected]
      exact ⟨[.stagingTaken r,.old (.responder (.selected pid ⟨none,w,v,a,b⟩))],
        by simp [r,List.append_assoc],accountSafe _ _ _ _ ⟨entry,complete⟩,ledger,entry,complete⟩
    | some peer =>
      obtain ⟨suffix,extended,safe,post⟩ := after_take r valid rfl before Safe accountSafe
        (fun ledger generation position => activeSafe ledger generation peer position)
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

theorem staging (pid : PeerId) (Safe : List Event → Prop)
    (accountSafe : ∀ ledger locals h w, Accounted h ledger debts locals w → Safe h)
    (activeSafe : ∀ ledger generation peer position h,
      Active ledger debts generation pid peer position h → Safe h) :
    StatePrefixPreserves (Carrier debts locals) Safe (Driver.stagingObserved hooks pid) := by
  intro w a h before
  obtain ⟨ledger,accounted⟩ := before
  exact staging_fixed ledger debts locals pid Safe accountSafe activeSafe w a h accounted

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSelected
