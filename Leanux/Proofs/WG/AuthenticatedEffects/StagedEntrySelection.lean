import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTake

/-! The original selection's completed take is observable before key borrowing.
Idle and failed reads retain the entry bundle; a later borrow Stop retains the
actual active take ledger, native ownership and exact cached peer. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal RetirementSecurity StagedProvenance
open HandshakeSecurity.StagedConservation

/-- A failed native take emits no fabricated completed receipt. The accounted
entry remains the actual pre-read cut and no selected ledger is invented. -/
theorem selection_take_stop (pid : PeerId) (before : Inv history ledger debts locals w)
    (a : Ambient) (stopped : ((Take.takePrefix pid).run w).run a = .error stop) :
    runWGPrefix (CausalJournal.selection pid) w a history = (.error stop,history) ∧
      Inv history ledger debts locals w := by
  have captured := runWGPrefix_receiptWGObserved (liftWGPrefix (Take.takePrefix pid))
    (fun run => Event.stagingTaken ⟨pid,run⟩) w a history
  rw [runWGPrefix_lift,stopped] at captured
  have inner : runWGPrefix (Take.observed Event.stagingTaken pid) w a history = (.error stop,history) := by
    unfold Take.observed
    rw [runWGPrefix,runStatePrefix_bind]
    change runStatePrefix _ w a history = _ at captured
    rw [captured]
  have outer := runWGPrefix_receiptWGObserved (Take.observed Event.stagingTaken pid)
    (fun run => Event.old (.responder (.selected pid run))) w a history
  rw [inner] at outer
  exact ⟨outer,before⟩

theorem selection_missing (pid : PeerId) (before : Inv history ledger debts locals w)
    (a : Ambient) (absent : (w.dev.bind fun d => d.peers[pid]?) = none) :
    ∃ stop, runWGPrefix (CausalJournal.selection pid) w a history = (.error stop,history) ∧
      Inv history ledger debts locals w := by
  obtain ⟨stop,stopped⟩ := TakeFrames.missing pid w a absent
  exact ⟨stop,selection_take_stop pid before a stopped⟩

/-- Empty staging preserves the entry bundle through both actual receipts.
The native idle peer still exists and has an empty staged list. -/
theorem selection_idle (r : Take.Receipt) (valid : r.Valid) (empty : r.run.value = none)
    (before : Inv history ledger debts locals r.run.before) :
    let finalHistory := (history ++ [.stagingTaken r]) ++
      [.old (.responder (.selected r.pid ⟨none,r.run.before,r.run.after,r.run.ambientBefore,r.run.ambientAfter⟩))]
    runWGPrefix (CausalJournal.selection r.pid) r.run.before r.run.ambientBefore history =
      (.ok ((none,r.run.after),r.run.ambientAfter),finalHistory) ∧
      Inv finalHistory ledger debts locals r.run.after := by
  dsimp only
  obtain ⟨_,_,source⟩ := selection_after_accounted_take r valid before.core.valid before.core.queues before.core.selected
  rw [empty] at source
  have idleBundle := idle r valid empty before
  refine ⟨source,?_⟩
  exact idleBundle.1.views _ (by intro e member; have eq := List.mem_singleton.mp member; subst e; rfl)
    rfl rfl rfl rfl rfl rfl

/-- A stopped key borrow retains the exact selected frontier from the completed
native take. Packet cells, native owners and the cached peer are all from this
same invocation; no completed outer-selection receipt is assumed. -/
theorem selection_borrow_stopped (r : Take.Receipt) (valid : r.Valid)
    (chosen : r.run.value = some peer) (before : Inv history ledger debts locals r.run.before)
    (stopped : ((Take.borrow r.run.value).run r.run.after).run r.run.ambientAfter = .error stop) :
    ∃ after, runWGPrefix (CausalJournal.selection r.pid) r.run.before r.run.ambientBefore history =
        (.error stop,history ++ [.stagingTaken r]) ∧
      TakeAccounted (births history) ledger history r after ∧
      Active (history ++ [.stagingTaken r]) after debts locals history.length r.run.after ∧
      ∃ d, r.run.before.dev = some d ∧ d.peers[r.pid]? = some peer ∧ peer.staged.isEmpty = false ∧
        r.run.after = {r.run.before with dev := some {d with peers := d.peers.insert r.pid {peer with staged := []}}} ∧
        Staged.stagedAt r.run.after r.pid = some (peer.internalId,[]) := by
  obtain ⟨after,accounted,active,_⟩ := taken r valid chosen before
  exact ⟨after,selection_borrow_stop r valid stopped history,accounted,active,TakeFrames.cached r valid chosen⟩

def SelectionContinuation (r : Take.Receipt) (history : List Event) : Prop :=
  runWGPrefix (CausalJournal.selection r.pid) r.run.before r.run.ambientBefore history =
    match ((Take.borrow r.run.value).run r.run.after).run r.run.ambientAfter with
    | .error stop => (.error stop,history ++ [.stagingTaken r])
    | .ok ((value,w),a) => (.ok ((value,w),a),(history ++ [.stagingTaken r]) ++
        [.old (.responder (.selected r.pid ⟨value,r.run.before,w,r.run.ambientBefore,a⟩))])

theorem selection_continuation (r : Take.Receipt) (valid : r.Valid)
    (before : Inv history ledger debts locals r.run.before) : SelectionContinuation r history := by
  obtain ⟨_,_,source⟩ := selection_after_accounted_take r valid before.core.valid before.core.queues before.core.selected
  exact source

/-- This boundary is obtained by running the native take, without a supplied
successful-take premise. A successful nonempty branch exposes its exact borrow
continuation; its active bundle is at the retained take cut, not a later state. -/
theorem selection_boundary (pid : PeerId) (before : Inv history ledger debts locals w) (a : Ambient) :
    (∃ stop, ((Take.takePrefix pid).run w).run a = .error stop ∧
      runWGPrefix (CausalJournal.selection pid) w a history = (.error stop,history) ∧
      Inv history ledger debts locals w) ∨
    (∃ r : Take.Receipt, r.pid = pid ∧ r.run.before = w ∧ r.run.ambientBefore = a ∧ r.Valid ∧ SelectionContinuation r history ∧
      ((r.run.value = none ∧
        Inv (history ++ [.stagingTaken r]) ledger debts locals r.run.after) ∨
      (∃ peer after, r.run.value = some peer ∧ TakeAccounted (births history) ledger history r after ∧
        Active (history ++ [.stagingTaken r]) after debts locals history.length r.run.after ∧
        ∃ d, r.run.before.dev = some d ∧ d.peers[r.pid]? = some peer ∧ peer.staged.isEmpty = false ∧
          r.run.after = {r.run.before with dev := some {d with peers := d.peers.insert r.pid {peer with staged := []}}} ∧
          Staged.stagedAt r.run.after r.pid = some (peer.internalId,[])))) := by
  cases run : ((Take.takePrefix pid).run w).run a with
  | error stop => exact Or.inl ⟨stop,rfl,selection_take_stop pid before a run⟩
  | ok out =>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let r : Take.Receipt := ⟨pid,⟨value,w,v,a,b⟩⟩
    have valid : r.Valid := run
    refine Or.inr ⟨r,rfl,rfl,rfl,valid,selection_continuation r valid before,?_⟩
    cases value with
    | none => exact Or.inl ⟨rfl,(idle r valid rfl before).1⟩
    | some peer =>
      obtain ⟨after,accounted,active,_⟩ := taken r valid rfl before
      exact Or.inr ⟨peer,after,rfl,accounted,active,TakeFrames.cached r valid rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
