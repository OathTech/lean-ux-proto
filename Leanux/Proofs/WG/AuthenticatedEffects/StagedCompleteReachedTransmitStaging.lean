import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitCaller

/-! The actual routed prefix supplies the staging account. Selected callbacks
and silent allocation intervals are then derived by the fixed staging source;
post-staging release remains the original transmit continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier AllocatedObligation

/-- The incoming product carrier supplies its own account; no independent
reachable-state premise is introduced for the front or staging call. -/
theorem product_caller_cases (input : Input) (history : List Event) (world : World)
    (before : CompleteProduct.Carrier history world) :
    (∃ stop last, Stopped input history world.wg world.ambient stop last) ∨
    (∃ value v b prior after, Path input history world.wg world.ambient value v b prior ∧
      Accounted (resultHistory input value world.wg v world.ambient b prior) after [] [] v) := by
  obtain ⟨ledger,accounted⟩:=before.1
  exact caller_cases input history world.wg world.ambient accounted

/-- Complete staging source alternatives at this exact front return. Debts
and local ownership remain the caller's explicit lists, including on selected Stops. -/
theorem Path.staging_cases (path : Path input h w a (.ok pid) v b prior)
    (before : Accounted h ledger debts locals w) :
    ∃ after, let events:=resultHistory input (.ok pid) w v a b prior
      Accounted events after debts locals v ∧
      (Staging.TakeStopped events pid v b ∨
        Staging.BorrowStopped events after debts locals pid v b ∨
        Staging.GuardStopped events after debts locals pid v b ∨
        (∃ lastWorld lastClock lastHistory,
          runWGPrefix (Driver.stagingObserved hooks pid) v b events=
            (.ok (((),lastWorld),lastClock),lastHistory) ∧
          Accounted lastHistory after debts locals lastWorld) ∨
        Staging.Callback events after debts locals pid v b) := by
  obtain ⟨after,accounted,_⟩:=path.accounted before
  exact ⟨after,accounted,Staging.caller_cases accounted pid b⟩

/-- A selected path is reached by the literal front-then-staging prefix,
including the exact journal position used for its take and allocation. -/
theorem Path.selected_literal
    (path : Path input h w a (.ok pid) v b prior)
    (selected : Staging.CallbackPath (resultHistory input (.ok pid) w v a b prior)
      after debts locals pid v b peer keypair selectedHistory selectedWorld selectedClock
      selectedLedger generation decision last cut clock) :
    runWGPrefix (stagingPrefix input) w a h=
      (.ok ((.ok (pid,some (peer,decision)),cut),clock),last) := by
  unfold stagingPrefix
  change runStatePrefix (_ >>= _) w a h=_
  rw [runStatePrefix_bind]
  have front:=path.front
  change runStatePrefix _ _ _ _=_ at front
  rw [front]
  dsimp only
  rw [runStatePrefix_bind]
  have performed:=selected.literal
  change runStatePrefix _ _ _ _=_ at performed
  rw [performed]
  rfl

theorem Path.selected_continuation
    (path : Path input h w a (.ok pid) v b prior)
    (selected : Staging.CallbackPath (resultHistory input (.ok pid) w v a b prior)
      after debts locals pid v b peer keypair selectedHistory selectedWorld selectedClock
      selectedLedger generation decision last cut clock) :
    runWGPrefix (Driver.transmitObserved hooks input.family input.address input.packets input.mtu) w a h=
      runWGPrefix (Staging.allocationTail pid peer decision >>= fun _=>repayment pid) cut clock last := by
  rw [staging_factor]
  change runStatePrefix (_ >>= _) w a h=_
  rw [runStatePrefix_bind]
  have performed:=path.selected_literal selected
  change runStatePrefix _ _ _ _=_ at performed
  rw [performed]
  rfl

/-- The allocation result carries the exact fixed assignment and each
partial native map. The subsequent create and reference repayment may Stop. -/
theorem Path.allocation
    (path : Path input h w a (.ok pid) v b prior)
    (selected : Staging.CallbackPath (resultHistory input (.ok pid) w v a b prior)
      after debts locals pid v b peer keypair selectedHistory selectedWorld selectedClock
      selectedLedger generation (.submit kid packets) last cut clock) :
    ∃ (items : List SkbId) (allocated : WGWorld),
      let nativeReceipt : WGRunWitness (List SkbId):=⟨items,cut,allocated,clock,clock⟩
      let events:=last++[Event.old (.allocated packets nativeReceipt)]
      let next:=assignBatch (resultHistory input (.ok pid) w v a b prior).length last.length selectedLedger
      runWGPrefix (Driver.transmitObserved hooks input.family input.address input.packets input.mtu) w a h=
        runWGPrefix (CausalJournal.create pid items >>= fun _=>repayment pid) allocated clock events ∧
      nativeReceipt.Valid (packets.mapM newTxSkb) ∧
      Accounted events next debts (⟨.unpublished,pid,items⟩::locals) allocated ∧
      AllocatedObligation.CreateDisposal.PendingBatch events next items ∧
      ∀ n, n≤packets.length → ∃ prefixItems transient,
        Allocation.Interval last selectedLedger debts locals generation pid peer
          (resultHistory input (.ok pid) w v a b prior).length kid packets cut clock n prefixItems transient ∧
        runWGPrefix (liftWGPrefix ((packets.take n).mapM newTxSkb)) cut clock last=
          (.ok ((prefixItems,transient),clock),last) ∧
        ∃ rest, (((packets.drop n).mapM newTxSkb).run transient).run clock=.ok ((rest,allocated),clock) ∧
          items=prefixItems++rest := by
  obtain ⟨items,allocated,performed,native,step,accounted,pending,intervals⟩:=
    Allocation.allocate_intervals selected.ready selected.shape
  refine ⟨items,allocated,?_,native,accounted,pending,intervals⟩
  rw [path.selected_continuation selected]
  simp only [Staging.allocationTail,bind_assoc]
  change runStatePrefix (_ >>= _) cut clock last=_
  rw [runStatePrefix_bind]
  change runStatePrefix _ _ _ _=_ at performed
  rw [performed]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit
