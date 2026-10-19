import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingSelection

/-! Actual caller paths from a concrete staging entry. Failure certificates
retain the real failed take, borrow or guarded prefix and its saved native
entry. Normal callback certificates derive Ready and batch Shape from those
same calls, rather than taking either as a new caller assumption. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations CausalJournal CompleteCarrier
open HandshakeSecurity.StagedConservation

structure CallbackPath (history : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (w : WGWorld) (a : Ambient)
    (peer : Peer) (keypair : Option KeypairId) (selectedHistory : List Event)
    (selectedWorld : WGWorld) (selectedClock : Ambient) (after : Ledger) (generation : Nat)
    (decision : Decision) (h : List Event) (v : WGWorld) (b : Ambient) : Prop where
  selected : Selected history ledger debts locals pid w a peer keypair selectedHistory selectedWorld selectedClock after generation
  selectionRun : runWGPrefix (CausalJournal.selection pid) w a history=
    (.ok ((some (peer,keypair),selectedWorld),selectedClock),selectedHistory)
  guardRun : runWGPrefix (allocationPrefix pid peer keypair) selectedWorld selectedClock selectedHistory=
    (.ok ((decision,v),b),h)
  ready : CompleteSelected.Ready after debts locals generation pid peer history.length h v b
  shape : Matches pid peer.staged decision

theorem CallbackPath.literal
    (path : CallbackPath history ledger debts locals pid w a peer keypair selectedHistory
      selectedWorld selectedClock after generation decision h v b) :
    runWGPrefix (stagingPrefix pid) w a history=(.ok ((some (peer,decision),v),b),h) := by
  unfold stagingPrefix
  simp only [runWGPrefix,runStatePrefix_bind]
  have selected := path.selectionRun
  change runStatePrefix _ _ _ _=_ at selected
  rw [selected]
  change runStatePrefix (_ >>= _) selectedWorld selectedClock selectedHistory=_
  rw [runStatePrefix_bind]
  have guarded := path.guardRun
  change runStatePrefix _ _ _ _=_ at guarded
  rw [guarded]
  rfl

theorem CallbackPath.continuation
    (path : CallbackPath history ledger debts locals pid w a peer keypair selectedHistory
      selectedWorld selectedClock after generation decision h v b) :
    runWGPrefix (Driver.stagingObserved hooks pid) w a history=
      runWGPrefix (allocationTail pid peer decision) v b h := by
  rw [whole_factor]
  change runStatePrefix (_ >>= _) w a history=_
  rw [runStatePrefix_bind]
  have literal := path.literal
  change runStatePrefix _ _ _ _=_ at literal
  rw [literal]
  rfl

def TakeStopped (history : List Event) (pid : PeerId) (w : WGWorld) (a : Ambient) : Prop :=
  ∃ stop, ((Take.takePrefix pid).run w).run a=.error stop ∧
    runWGPrefix (Driver.stagingObserved hooks pid) w a history=(.error stop,history)

def BorrowStopped (history : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (w : WGWorld) (a : Ambient) : Prop :=
  ∃ (r : Take.Receipt) (peer : Peer) (after : Ledger) (generation : Nat) (stop : Stop),
    r.pid=pid ∧ r.run.before=w ∧ r.run.ambientBefore=a ∧ r.Valid ∧ r.run.value=some peer ∧
    after=transferLocation (.staged generation pid peer.internalId) (.selected history.length) ledger ∧
    CompleteSelected.Ready after debts locals generation pid peer history.length
      (history++[.stagingTaken r]) r.run.after r.run.ambientAfter ∧
    ((Take.borrow (some peer)).run r.run.after).run r.run.ambientAfter=.error stop ∧
    runWGPrefix (Driver.stagingObserved hooks pid) w a history=(.error stop,history++[.stagingTaken r])

/-- This is a failed concrete guard/nonce/owner-acquisition prefix from its
actual selected entry. It does not invent a WGWorld at an Except error. -/
def GuardStopped (history : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (w : WGWorld) (a : Ambient) : Prop :=
  ∃ peer keypair selectedHistory selectedWorld selectedClock after generation stop last,
    Selected history ledger debts locals pid w a peer keypair selectedHistory selectedWorld selectedClock after generation ∧
    runWGPrefix (CausalJournal.selection pid) w a history=
      (.ok ((some (peer,keypair),selectedWorld),selectedClock),selectedHistory) ∧
    runWGPrefix (allocationPrefix pid peer keypair) selectedWorld selectedClock selectedHistory=(.error stop,last) ∧
    CompleteSelected.Active after debts generation pid peer history.length last ∧
    runWGPrefix (Driver.stagingObserved hooks pid) w a history=(.error stop,last)

def Callback (history : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId) (w : WGWorld) (a : Ambient) : Prop :=
  ∃ peer keypair selectedHistory selectedWorld selectedClock after generation decision h v b,
    CallbackPath history ledger debts locals pid w a peer keypair selectedHistory selectedWorld selectedClock
      after generation decision h v b

/-- Exhaustive classification from the incoming concrete account. The
guarded entry does not require a successful staging or allocation premise. -/
theorem caller_cases (before : Accounted history ledger debts locals w) (pid : PeerId) (a : Ambient) :
    TakeStopped history pid w a ∨
    BorrowStopped history ledger debts locals pid w a ∨
    GuardStopped history ledger debts locals pid w a ∨
    (∃ v b h, runWGPrefix (Driver.stagingObserved hooks pid) w a history=(.ok (((),v),b),h) ∧
      Accounted h ledger debts locals v) ∨
    Callback history ledger debts locals pid w a := by
  rcases selection_cases before pid a with taken|idle|borrowed|selected
  · obtain ⟨stop,native,run⟩:=taken
    refine Or.inl ⟨stop,native,?_⟩
    rw [allocation_factor]
    change runStatePrefix (_ >>= _) w a history=_
    rw [runStatePrefix_bind]
    change runStatePrefix _ _ _ _=_ at run
    rw [run]
  · obtain ⟨v,b,h,run,accounted⟩:=idle
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨v,b,h,?_,accounted⟩)))
    rw [allocation_factor]
    change runStatePrefix (_ >>= _) w a history=_
    rw [runStatePrefix_bind]
    change runStatePrefix _ _ _ _=_ at run
    rw [run]
    rfl
  · obtain ⟨r,peer,after,generation,stop,pidEq,worldEq,clockEq,valid,chosen,assigned,ready,failed,run⟩:=borrowed
    refine Or.inr (Or.inl ⟨r,peer,after,generation,stop,pidEq,worldEq,clockEq,valid,chosen,assigned,ready,failed,?_⟩)
    rw [allocation_factor]
    change runStatePrefix (_ >>= _) w a history=_
    rw [runStatePrefix_bind]
    change runStatePrefix _ _ _ _=_ at run
    rw [run]
  · obtain ⟨peer,keypair,h,u,c,after,generation,selectedRun,path⟩:=selected
    have ready := path.choose_spec.2.2.2.2.2.2.2.2
    have checked := allocation_checked after debts locals generation pid peer history.length keypair u c h ready
    cases outcome : runWGPrefix (allocationPrefix pid peer keypair) u c h with
    | mk result last=>
      cases result with
      | error stop=>
        obtain ⟨_,_,safe,_⟩:=checked
        change runPrefix ((allocationPrefix pid peer keypair).run u) c h=_ at outcome
        rw [outcome] at safe
        refine Or.inr (Or.inr (Or.inl ⟨peer,keypair,h,u,c,after,generation,stop,last,path,selectedRun,outcome,safe,?_⟩))
        rw [allocation_factor]
        change runStatePrefix (_ >>= _) w a history=_
        rw [runStatePrefix_bind]
        change runStatePrefix _ _ _ _=_ at selectedRun
        rw [selectedRun]
        change runStatePrefix (_ >>= _) u c h=_
        rw [runStatePrefix_bind]
        change runStatePrefix _ _ _ _=_ at outcome
        rw [outcome]
      | ok out=>
        obtain ⟨⟨decision,v⟩,b⟩:=out
        have afterGuard:=normal (allocation_checked after debts locals generation pid peer history.length keypair) ready outcome
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨peer,keypair,h,u,c,after,generation,decision,last,v,b,
          path,selectedRun,outcome,afterGuard.1,afterGuard.2⟩)))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Staging
