import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryRestore

/-! Actual restoration observer transport. Normal completion emits its native
receipt and recovers the entry bundle; Stop retains the incoming active cut
and exact event prefix, rather than treating the interrupted batch as lost. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Restoration
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal RetirementSecurity StagedProvenance Staged
open HandshakeSecurity.StagedConservation

def Normal (_before : Ready h ledger debts locals position generation pid allocation packets w)
    (a : Ambient) (history : List Event) (v : WGWorld) (b : Ambient) : Prop :=
  let r : Restore.Receipt := ⟨pid,packets,⟨(),w,v,a,b⟩⟩
  let after := transferLocation (.selected position) (.staged generation pid allocation) ledger
  history = h ++ [.stagedRestored r] ∧ r.Valid ∧ Staged.Obligations.Step ledger after ∧
    Inv history after debts locals v ∧ pendingAt (.selected position) after = [] ∧
    pendingAt (.staged generation pid allocation) after = pendingAt (.selected position) ledger ∧
    ∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
      (ticket,Status.terminal outcome) ∈ after

/-- The observed call binds the restored ledger to its own native receipt,
including its packet order and resident peer allocation. -/
theorem normal (before : Ready h ledger debts locals position generation pid allocation packets w)
    (a b : Ambient) (v : WGWorld) (history : List Event)
    (run : runWGPrefix (CausalJournal.stagedRestore pid packets) w a h = (.ok (((),v),b),history)) :
    Normal before a history v b := by
  have observed := runWGPrefix_receiptWGObserved (liftWGPrefix (Restore.nativeRestore pid packets))
    (fun run => Event.stagedRestored ⟨pid,packets,run⟩) w a h
  rw [runWGPrefix_lift] at observed
  change runWGPrefix (CausalJournal.stagedRestore pid packets) w a h = _ at observed
  rw [observed] at run
  cases native : ((Restore.nativeRestore pid packets).run w).run a with
  | error stop => rw [native] at run; cases run
  | ok out =>
    obtain ⟨⟨value,u⟩,c⟩ := out
    cases value
    rw [native] at run
    cases run
    have result := restored (⟨pid,packets,⟨(),w,v,a,b⟩⟩ : Restore.Receipt) native
      before.active before.epoch before.vacant before.aligned
    exact ⟨rfl,native,result⟩

/-- Native Stop produces no completed restore receipt. The retained cut is
this actual active entry, still containing every selected ticket and owner. -/
theorem stopped (before : Ready h ledger debts locals position generation pid allocation packets w)
    (a : Ambient) (history : List Event) (stop : Stop)
    (run : runWGPrefix (CausalJournal.stagedRestore pid packets) w a h = (.error stop,history)) :
    history = h ∧ Ready history ledger debts locals position generation pid allocation packets w ∧
      ((Restore.nativeRestore pid packets).run w).run a = .error stop := by
  have observed := runWGPrefix_receiptWGObserved (liftWGPrefix (Restore.nativeRestore pid packets))
    (fun run => Event.stagedRestored ⟨pid,packets,run⟩) w a h
  rw [runWGPrefix_lift] at observed
  change runWGPrefix (CausalJournal.stagedRestore pid packets) w a h = _ at observed
  rw [observed] at run
  cases native : ((Restore.nativeRestore pid packets).run w).run a with
  | error actual =>
    rw [native] at run
    cases run
    exact ⟨rfl,before,rfl⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    rw [native] at run
    cases run

/-- Complete source contract with a nontrivial stopped result. The only caller
premises are the explicit active carrier, epoch, vacant queue and alignment;
there is no assumption that restoration returns normally. -/
theorem checked (before : Ready h ledger debts locals position generation pid allocation packets w)
    (a : Ambient) :
    let result := runWGPrefix (CausalJournal.stagedRestore pid packets) w a h
    match result.1 with
    | .error stop => result.2 = h ∧ Ready result.2 ledger debts locals position generation pid allocation packets w ∧
        ((Restore.nativeRestore pid packets).run w).run a = .error stop
    | .ok ((_,v),b) => Normal before a result.2 v b := by
  cases executed : runWGPrefix (CausalJournal.stagedRestore pid packets) w a h with
  | mk result history =>
    cases result with
    | error stop => exact stopped before a history stop executed
    | ok out =>
      obtain ⟨⟨value,v⟩,b⟩ := out
      cases value
      exact normal before a b v history executed

/-- With the actual vacant-queue caller facts, the restore itself completes
and recovers the entry bundle. This conclusion does not assume a successful
restore run or successful later handshake queueing. -/
theorem total (before : Ready h ledger debts locals position generation pid allocation packets w)
    (a : Ambient) :
    ∃ v, let r : Restore.Receipt := ⟨pid,packets,⟨(),w,v,a,a⟩⟩
      runWGPrefix (CausalJournal.stagedRestore pid packets) w a h =
        (.ok (((),v),a),h ++ [.stagedRestored r]) ∧
      Normal before a (h ++ [.stagedRestored r]) v a := by
  obtain ⟨v,native⟩ := native_total pid packets w a before.vacant
  have observed := Restore.observed_completed Event.stagedRestored pid packets w v a a h native
  refine ⟨v,observed,?_⟩
  exact normal before a a v _ observed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Restoration
