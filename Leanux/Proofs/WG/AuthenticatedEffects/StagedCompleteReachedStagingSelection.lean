import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingCarrier

/-! Source classification at the original staged take and key borrow. The
selected ledger and Ready entry come from the incoming concrete account and
the same native take witness, including a borrow failure after the take. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier
open HandshakeSecurity.StagedConservation

def Selected (history : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (w : WGWorld) (a : Ambient)
    (peer : Peer) (keypair : Option KeypairId) (h : List Event) (v : WGWorld) (b : Ambient)
    (after : Ledger) (generation : Nat) : Prop :=
  ∃ r : Take.Receipt,
    r.pid=pid ∧ r.run.before=w ∧ r.run.ambientBefore=a ∧ r.Valid ∧ r.run.value=some peer ∧
    after=transferLocation (.staged generation pid peer.internalId) (.selected history.length) ledger ∧
    ((Take.borrow (some peer)).run r.run.after).run r.run.ambientAfter=.ok ((some (peer,keypair),v),b) ∧
    h=(history++[.stagingTaken r])++
      [.old (.responder (.selected pid ⟨some (peer,keypair),w,v,a,b⟩))] ∧
    CompleteSelected.Ready after debts locals generation pid peer history.length h v b

/-- The exhaustive native boundary does not assume selection succeeded.
Each failed branch records its own actual call and exact retained journal. -/
theorem selection_cases (before : Accounted history ledger debts locals w) (pid : PeerId) (a : Ambient) :
    (∃ stop, ((Take.takePrefix pid).run w).run a=.error stop ∧
      runWGPrefix (CausalJournal.selection pid) w a history=(.error stop,history)) ∨
    (∃ v b h, runWGPrefix (CausalJournal.selection pid) w a history=(.ok ((none,v),b),h) ∧
      Accounted h ledger debts locals v) ∨
    (∃ (r : Take.Receipt) (peer : Peer) (after : Ledger) (generation : Nat) (stop : Stop),
      r.pid=pid ∧ r.run.before=w ∧ r.run.ambientBefore=a ∧ r.Valid ∧ r.run.value=some peer ∧
      after=transferLocation (.staged generation pid peer.internalId) (.selected history.length) ledger ∧
      CompleteSelected.Ready after debts locals generation pid peer history.length
        (history++[.stagingTaken r]) r.run.after r.run.ambientAfter ∧
      ((Take.borrow (some peer)).run r.run.after).run r.run.ambientAfter=.error stop ∧
      runWGPrefix (CausalJournal.selection pid) w a history=(.error stop,history++[.stagingTaken r])) ∨
    (∃ peer keypair h v b after generation,
      runWGPrefix (CausalJournal.selection pid) w a history=(.ok ((some (peer,keypair),v),b),h) ∧
      Selected history ledger debts locals pid w a peer keypair h v b after generation) := by
  cases takeRun : ((Take.takePrefix pid).run w).run a with
  | error stop=>exact Or.inl ⟨stop,rfl,(selection_take_stop pid before.entry a takeRun).1⟩
  | ok out=>
    obtain ⟨⟨value,u⟩,c⟩:=out
    let r : Take.Receipt:=⟨pid,⟨value,w,u,a,c⟩⟩
    have valid : r.Valid:=takeRun
    cases value with
    | none=>
      obtain ⟨performed,entry⟩:=selection_idle r valid rfl before.entry
      have complete := (before.complete.append_quiet
        (suffix := [Event.stagingTaken r])
        (fun _ member=>by cases List.mem_singleton.mp member; intro position; rfl)).append_quiet
        (suffix := [Event.old (.responder (.selected pid ⟨none,w,u,a,c⟩))])
        (fun _ member=>by cases List.mem_singleton.mp member; intro position; rfl)
      exact Or.inr (Or.inl ⟨u,c,_,performed,entry,complete⟩)
    | some peer=>
      obtain ⟨after,generation,_,assigned,ready⟩:=CompleteSelected.taken r valid rfl before
      have source := selection_continuation r valid before.entry
      change runWGPrefix (CausalJournal.selection pid) w a history=_ at source
      cases borrowRun : ((Take.borrow (some peer)).run u).run c with
      | error stop=>
        have stopped := source
        change runWGPrefix (CausalJournal.selection pid) w a history=
          (match ((Take.borrow (some peer)).run u).run c with
            | .error reason=>(.error reason,history++[.stagingTaken r])
            | .ok ((choice,v),b)=>(.ok ((choice,v),b),(history++[.stagingTaken r])++
              [.old (.responder (.selected pid ⟨choice,w,v,a,b⟩))])) at stopped
        rw [borrowRun] at stopped
        exact Or.inr (Or.inr (Or.inl ⟨r,peer,after,generation,stop,rfl,rfl,rfl,valid,rfl,assigned,ready,borrowRun,stopped⟩))
      | ok out=>
        obtain ⟨⟨choice,v⟩,b⟩:=out
        have lifted : runWGPrefix (liftWGPrefix (Take.borrow (some peer))) u c
            (history++[.stagingTaken r])=(.ok ((choice,v),b),history++[.stagingTaken r]) := by
          rw [runWGPrefix_lift,borrowRun]
        obtain ⟨keypair,chosen,borrowed⟩:=normal
          (CompleteSelected.borrow after debts locals generation pid peer history.length
            (CompleteSelected.Active after debts generation pid peer history.length) (fun _=>id)) ready lifted
        subst choice
        let witness : WGRunWitness (Option (Peer×Option KeypairId)):=⟨some (peer,keypair),w,v,a,b⟩
        have finalReady:=CompleteSelected.selected_event borrowed witness
        have selected := source
        change runWGPrefix (CausalJournal.selection pid) w a history=
          (match ((Take.borrow (some peer)).run u).run c with
            | .error reason=>(.error reason,history++[.stagingTaken r])
            | .ok ((choice,v),b)=>(.ok ((choice,v),b),(history++[.stagingTaken r])++
              [.old (.responder (.selected pid ⟨choice,w,v,a,b⟩))])) at selected
        rw [borrowRun] at selected
        exact Or.inr (Or.inr (Or.inr ⟨peer,keypair,_,v,b,after,generation,selected,
          r,rfl,rfl,rfl,valid,rfl,assigned,borrowRun,rfl,finalReady⟩))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
