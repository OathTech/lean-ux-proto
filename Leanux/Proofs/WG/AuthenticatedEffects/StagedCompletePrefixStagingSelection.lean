import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixStagingRestore
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteSelectedSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntrySelection

/-! The native selection emits its take before borrowing and its outer receipt
only after borrowing returns. Each of these actual cuts receives its own
certificate, including a stopped borrow's selected ledger and native anchor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open CompleteCarrier AllocatedObligation HandshakeSecurity.StagedConservation

theorem idle_accounted (r : Take.Receipt) (native : r.Valid) (empty : r.run.value=none)
    (before : Accounted h ledger debts locals r.run.before) :
    Accounted (h++[Event.stagingTaken r]) ledger debts locals r.run.after :=
  ⟨(StagedEntry.idle r native empty before.entry).1,before.complete.append_quiet
    (fun _ member=>by cases List.mem_singleton.mp member; intro position; rfl)⟩

theorem borrow (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat) :
    StateEnsures (CompleteSelected.Ready ledger debts locals generation pid peer position)
      CompleteProduct.Safe (liftWGPrefix (Take.borrow (some peer)))
      (fun selected h w a=>∃ keypair, selected=some (peer,keypair) ∧
        CompleteSelected.Ready ledger debts locals generation pid peer position h w a) := by
  apply single
  · exact CompleteSelected.borrow ledger debts locals generation pid peer position CompleteProduct.Safe
      (fun h before=>⟨debts,.selected ledger generation pid peer position h before⟩)
  · intro h w a before
    exact ready_safe before
  · intro w a h _
    exact Or.inl rfl

def SelectionResult (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (result : Option (Peer × Option KeypairId))
    (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  match result with
  | none=>Accounted h ledger debts locals w
  | some (peer,_)=>∃ after generation position,
      Staged.Obligations.Step ledger after ∧
      after=transferLocation (.staged generation pid peer.internalId) (.selected position) ledger ∧
      CompleteSelected.Ready after debts locals generation pid peer position h w a

/-- A stopped borrow has an actual retained take cut. The selected carrier
is at that native cut's world; it does not pretend to describe an unreturned
world at the later Stop. -/
theorem selection_borrow_stop (r : Take.Receipt) (native : r.Valid)
    (chosen : r.run.value=some peer)
    (before : Accounted h ledger debts locals r.run.before)
    (previous : All CompleteProduct.Safe h)
    (stopped : ((Take.borrow r.run.value).run r.run.after).run r.run.ambientAfter=.error stop) :
    runWGPrefix (CausalJournal.selection r.pid) r.run.before r.run.ambientBefore h=
        (.error stop,h++[Event.stagingTaken r]) ∧
      ∃ after generation, Staged.Obligations.Step ledger after ∧
        after=transferLocation (.staged generation r.pid peer.internalId) (.selected h.length) ledger ∧
        CompleteSelected.Ready after debts locals generation r.pid peer h.length
          (h++[Event.stagingTaken r]) r.run.after r.run.ambientAfter ∧
        All CompleteProduct.Safe (h++[Event.stagingTaken r]) := by
  obtain ⟨after,generation,step,transfer,ready⟩ := CompleteSelected.taken r native chosen before
  exact ⟨TransmitSecurity.Staged.Obligations.selection_borrow_stop r native stopped h,
    after,generation,step,transfer,ready,previous.append (Cuts.singleton previous.last (ready_safe ready))⟩

/-- Full actual selection, with no successful-take or borrow premise. Failed
reads retain the input prefix; empty queues retain the same idle ledger;
nonempty queues transfer exactly to their native take position. -/
theorem selection (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) :
    StateEnsures (fun h w _=>Accounted h ledger debts locals w) CompleteProduct.Safe
      (CausalJournal.selection pid) (SelectionResult ledger debts locals pid) := by
  intro w a h before
  cases native : ((Take.takePrefix pid).run w).run a with
  | error stop=>
    have actual := (StagedEntry.selection_take_stop pid before.1.entry a native).1
    change runPrefix ((CausalJournal.selection pid).run w) a h=_ at actual
    rw [actual]
    exact ⟨[],by simp,before.2,True.intro⟩
  | ok out=>
    obtain ⟨⟨value,v⟩,b⟩ := out
    let r : Take.Receipt := ⟨pid,⟨value,w,v,a,b⟩⟩
    have valid : r.Valid := native
    cases value with
    | none=>
      have first := idle_accounted r valid rfl before.1
      have firstSafe : CompleteProduct.Safe (h++[Event.stagingTaken r]) :=
        ⟨debts,.accounted ledger locals _ v first⟩
      obtain ⟨actual,entry⟩ := StagedEntry.selection_idle r valid rfl before.1.entry
      have complete := first.complete.append_quiet
        (suffix := [Event.old (.responder (.selected pid ⟨none,w,v,a,b⟩))])
        (fun _ member=>by cases List.mem_singleton.mp member; intro position; rfl)
      have last : Accounted ((h++[Event.stagingTaken r])++
          [Event.old (.responder (.selected pid ⟨none,w,v,a,b⟩))]) ledger debts locals v :=
        ⟨entry,complete⟩
      have all := (before.2.append (Cuts.singleton before.2.last firstSafe)).append
        (Cuts.singleton firstSafe (show CompleteProduct.Safe _ from ⟨debts,.accounted _ _ _ v last⟩))
      change runPrefix ((CausalJournal.selection pid).run w) a h=_ at actual
      rw [actual]
      exact ⟨[.stagingTaken r,.old (.responder (.selected pid ⟨none,w,v,a,b⟩))],
        by simp [r,List.append_assoc],all,last,all⟩
    | some peer=>
      obtain ⟨after,generation,step,transfer,ready⟩ := CompleteSelected.taken r valid rfl before.1
      have firstAll := before.2.append (Cuts.singleton before.2.last (ready_safe ready))
      have source := StagedEntry.selection_continuation r valid before.1.entry
      change runWGPrefix (CausalJournal.selection pid) w a h=_ at source
      obtain ⟨_,_,_,post⟩ := borrow after debts locals generation pid peer h.length v b
        (h++[Event.stagingTaken r]) ⟨ready,firstAll⟩
      cases borrowed : ((Take.borrow (some peer)).run v).run b with
      | error stop=>
        change runWGPrefix (CausalJournal.selection pid) w a h =
          (match ((Take.borrow (some peer)).run v).run b with
            | .error reason=>(.error reason,h++[Event.stagingTaken r])
            | .ok ((result,u),c)=>(.ok ((result,u),c),(h++[Event.stagingTaken r])++
                [.old (.responder (.selected pid ⟨result,w,u,a,c⟩))])) at source
        rw [borrowed] at source
        change runPrefix ((CausalJournal.selection pid).run w) a h=_ at source
        rw [source]
        exact ⟨[.stagingTaken r],rfl,firstAll,True.intro⟩
      | ok out=>
        obtain ⟨⟨result,u⟩,c⟩ := out
        have performed : runPrefix ((liftWGPrefix (Take.borrow (some peer))).run v) b
            (h++[Event.stagingTaken r]) = (.ok ((result,u),c),h++[Event.stagingTaken r]) := by
          change (((Take.borrow (some peer)).run v).run b,_) = _
          rw [borrowed]
        rw [performed] at post
        obtain ⟨⟨keypair,chosen,held⟩,_⟩ := post
        have final := CompleteSelected.selected_event held ⟨result,w,u,a,c⟩
        have all := firstAll.append (Cuts.singleton firstAll.last (ready_safe final))
        change runWGPrefix (CausalJournal.selection pid) w a h =
          (match ((Take.borrow (some peer)).run v).run b with
            | .error reason=>(.error reason,h++[Event.stagingTaken r])
            | .ok ((result,u),c)=>(.ok ((result,u),c),(h++[Event.stagingTaken r])++
                [.old (.responder (.selected pid ⟨result,w,u,a,c⟩))])) at source
        rw [borrowed] at source
        change runPrefix ((CausalJournal.selection pid).run w) a h=_ at source
        rw [source]
        refine ⟨[.stagingTaken r,.old (.responder (.selected pid ⟨result,w,u,a,c⟩))],
          by simp [List.append_assoc],all,?_,all⟩
        rw [chosen]
        exact ⟨after,generation,h.length,step,transfer,by simpa only [chosen] using final⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Staging
