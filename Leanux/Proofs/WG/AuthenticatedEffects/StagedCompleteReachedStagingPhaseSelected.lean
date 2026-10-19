import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPhaseEvidence

/-! The outer selection certificate includes the take receipt, the actual
key borrow and its saved selected receipt. Each successful bind uses its
literal run; a later Stop does not discard the preceding phase evidence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal
open Staged.Obligations CompleteCarrier Staging.Points HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

theorem receipt_normal {body : WGPrefix Event α} {record : WGRunWitness α → Event}
    (run : runWGPrefix (receiptWGObserved body record) w a h=(.ok ((value,v),b),last)) :
    ∃ middle,runWGPrefix body w a h=(.ok ((value,v),b),middle) ∧
      last=middle++[record ⟨value,w,v,a,b⟩] := by
  rw [runWGPrefix_receiptWGObserved] at run
  cases performed : runWGPrefix body w a h with
  | mk out middle=>
    rw [performed] at run
    cases out with
    | error=>cases run
    | ok pair=>obtain ⟨⟨returned,u⟩,c⟩:=pair; cases run; exact ⟨middle,rfl,rfl⟩

theorem take_none_account (before : Accounted h ledger debts locals w)
    (native : ((Take.takePrefix pid).run w).run a=.ok ((none,v),b)) :
    Accounted (h++[.stagingTaken ⟨pid,⟨none,w,v,a,b⟩⟩]) ledger debts locals v := by
  have casesNative:=StagingInterior.take_cases pid w a
  rw [native] at casesNative
  cases casesNative with
  | empty device resident empty=>
    exact before.append_quiet _ (by intro e member; cases List.mem_singleton.mp member; rfl)
      (by intro e member; cases List.mem_singleton.mp member; intro position; rfl)

theorem selection_normal_evidence (before : Accounted h ledger debts locals w)
    (steps : Staged.Obligations.Step root ledger)
    (run : runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((value,v),b),last)) :
    Evidence root debts locals last v b := by
  rcases Staging.selection_cases before pid a with failed|idle|borrowed|chosen
  · obtain ⟨stop,_,actual⟩:=failed
    rw [run] at actual
    cases actual
  · obtain ⟨u,c,middle,actual,account⟩:=idle
    rw [run] at actual
    cases actual
    exact .accounted ledger steps account
  · obtain ⟨r,peer,after,generation,stop,_,_,_,_,_,_,_,_,actual⟩:=borrowed
    rw [run] at actual
    cases actual
  · obtain ⟨peer,key,middle,u,c,after,generation,actual,path⟩:=chosen
    rw [run] at actual
    cases actual
    obtain ⟨r,_,_,_,_,_,assigned,_,_,ready⟩:=path
    exact .selected after (steps.trans (assigned.symm ▸ transferLocation_step _ _ _)) ready

theorem selection_covers (before : Accounted h ledger debts locals w)
    (steps : Staged.Obligations.Step root ledger) (pid : PeerId) (a : Ambient) :
    Covers (Evidence root debts locals) (selectionShape pid) w a h := by
  unfold selectionShape
  change Covers _ (.receipt _ (.bind (.receipt _ (takeShape pid)) borrowShape)) w a h
  constructor
  · have first : Covers (Evidence root debts locals)
        (.receipt (fun r=>Event.stagingTaken ⟨pid,r⟩) (takeShape pid)) w a h := by
      refine ⟨(take_covers before pid a).mono (fun _ _ _ phase=>take_evidence steps phase),?_⟩
      intro value u b middle run
      obtain ⟨native,rfl⟩:=lift_success run
      cases value with
      | none=>exact .accounted ledger steps (take_none_account before native)
      | some peer=>
        obtain ⟨after,generation,transfer,_,ready⟩:=CompleteSelected.taken ⟨pid,⟨some peer,w,u,a,b⟩⟩ native rfl before
        exact .selected after (steps.trans transfer) ready
    apply covers_bind first
    intro value u b middle run
    obtain ⟨events,performed,recorded⟩:=receipt_normal run
    obtain ⟨native,rfl⟩:=lift_success performed
    subst middle
    cases value with
    | none=>exact .accounted ledger steps (take_none_account before native)
    | some peer=>
      obtain ⟨after,generation,transfer,_,ready⟩:=CompleteSelected.taken ⟨pid,⟨some peer,w,u,a,b⟩⟩ native rfl before
      exact (borrow_covers ready).mono (fun _ _ _ selected=>.selected after (steps.trans transfer) selected)
  · intro value v b middle performed
    apply selection_normal_evidence (value:=value) before steps
    change runWGPrefix (receiptWGObserved (Take.observed Event.stagingTaken pid) _) w a h=_
    change runWGPrefix (Take.observed Event.stagingTaken pid) w a h=_ at performed
    rw [runWGPrefix_receiptWGObserved,performed]

theorem selection_every_point (before : Accounted h ledger debts locals w)
    (point : Point (selectionShape pid) w a h leaf v b middle remaining) :
    Evidence ledger debts locals middle v b ∧
      runWGPrefix (CausalJournal.selection pid) w a h=runWGPrefix remaining v b middle :=
  ⟨(selection_covers before (.refl _) pid a).point point,point.residual⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingPhase
