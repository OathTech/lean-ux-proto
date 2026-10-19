import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingInteriorKeepaliveReceipt

/-! Existing observed source boundaries preserve their exact suffixes.
Selection retains the original borrow and emits its outer receipt only on
normal return; restoration and keepalive emit only completed native calls. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Obligations Staged.Origins CausalJournal CompleteCarrier
open HandshakeSecurity.StagedConservation RetirementSecurity
set_option maxHeartbeats 600000

theorem selection_after_take {taken : Option Peer}
    (native : ((Take.takePrefix pid).run w).run a=.ok ((taken,v),b)) :
    runWGPrefix (CausalJournal.selection pid) w a h=
      match ((Take.borrow taken).run v).run b with
      | .error stop => (.error stop,h++[.stagingTaken ⟨pid,⟨taken,w,v,a,b⟩⟩])
      | .ok ((choice,q),c) => (.ok ((choice,q),c),(h++[.stagingTaken ⟨pid,⟨taken,w,v,a,b⟩⟩])++
          [.old (.responder (.selected pid ⟨choice,w,q,a,c⟩))]) := by
  change runWGPrefix (receiptWGObserved (Take.observed Event.stagingTaken pid)
    (fun run=>Event.old (.responder (.selected pid run)))) w a h=_
  rw [runWGPrefix_receiptWGObserved,Take.observed_after_take Event.stagingTaken pid w v a b h taken native,
    runWGPrefix_lift]
  cases borrowed : ((Take.borrow taken).run v).run b with
  | error stop => rfl
  | ok out => obtain ⟨⟨choice,q⟩,c⟩:=out; rfl

theorem selection_read_stopped (failed : ((getPeer pid).run w).run a=.error stop) :
    runWGPrefix (CausalJournal.selection pid) w a h=(.error stop,h) := by
  have inner : runWGPrefix (Take.observed Event.stagingTaken pid) w a h=(.error stop,h) := by
    unfold Take.observed
    rw [runWGPrefix,runStatePrefix_bind]
    have captured := runWGPrefix_receiptWGObserved (liftWGPrefix (Take.takePrefix pid))
      (fun run=>Event.stagingTaken ⟨pid,run⟩) w a h
    rw [runWGPrefix_lift,take_read_stopped failed] at captured
    change runStatePrefix _ w a h=_ at captured
    rw [captured]
  change runWGPrefix (receiptWGObserved (Take.observed Event.stagingTaken pid)
    (fun run=>Event.old (.responder (.selected pid run)))) w a h=_
  rw [runWGPrefix_receiptWGObserved,inner]

/-- This source record retains every actual native take branch. It does not
select an arbitrary world after a failed selection endpoint. -/
theorem selection_cases (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    (∃ stop, ((getPeer pid).run w).run a=.error stop ∧
      runWGPrefix (CausalJournal.selection pid) w a h=(.error stop,h)) ∨
    (∃ taken v b, TakeCase pid w a (.ok ((taken,v),b)) ∧
      runWGPrefix (CausalJournal.selection pid) w a h=
        match ((Take.borrow taken).run v).run b with
        | .error stop => (.error stop,h++[.stagingTaken ⟨pid,⟨taken,w,v,a,b⟩⟩])
        | .ok ((choice,q),c) => (.ok ((choice,q),c),(h++[.stagingTaken ⟨pid,⟨taken,w,v,a,b⟩⟩])++
            [.old (.responder (.selected pid ⟨choice,w,q,a,c⟩))])) := by
  have path := take_cases pid w a
  generalize native : ((Take.takePrefix pid).run w).run a=result at path
  cases path with
  | readStopped failed => exact Or.inl ⟨_,failed,selection_read_stopped failed⟩
  | empty device resident empty => exact Or.inr ⟨none,w,clock a .stagedEmpty true,
      .empty device resident empty,selection_after_take (take_empty device resident empty)⟩
  | taken device resident nonempty => exact Or.inr ⟨some _,_,_,
      .taken device resident nonempty,selection_after_take (take_nonempty device resident nonempty)⟩

theorem restore_projection (rho : Event → Option E)
    (quiet : ∀ v b, rho (.stagedRestored ⟨pid,packets,⟨(),w,v,a,b⟩⟩)=none) :
    ((runWGPrefix (CausalJournal.stagedRestore pid packets) w a h).2.filterMap rho)=h.filterMap rho := by
  have path := restore_cases pid packets w a
  generalize native : ((Restore.nativeRestore pid packets).run w).run a=result at path
  cases path with
  | readStopped failed => rw [restore_stopped failed]
  | restored device resident =>
    rw [restore_recorded device resident]
    simp [List.filterMap_append,quiet]

theorem keepalive_projection (rho : Event → Option E)
    (quiet : ∀ ready v b, rho (keepaliveEvent pid ready w v a b)=none) :
    ((runWGPrefix (CausalJournal.keepalivePrepare pid) w a h).2.filterMap rho)=h.filterMap rho := by
  cases native : ((OccurrenceHandshake.keepalivePrepare pid).run w).run a with
  | error stop => rw [keepalive_stopped native]
  | ok out =>
    obtain ⟨⟨ready,v⟩,b⟩:=out
    rw [keepalive_recorded native]
    simp [List.filterMap_append,quiet]

inductive ObservedKeepalive (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    Except Stop ((Bool × WGWorld) × Ambient) × List Event → Prop where
  | stopped (path : KeepaliveCase pid w a (.error stop)) : ObservedKeepalive pid w a h (.error stop,h)
  | returned (path : KeepaliveCase pid w a (.ok ((ready,v),b))) :
      ObservedKeepalive pid w a h (.ok ((ready,v),b),h++[keepaliveEvent pid ready w v a b])

theorem observed_keepalive_cases (pid : PeerId) (w : WGWorld) (a : Ambient) (h : List Event) :
    ObservedKeepalive pid w a h (runWGPrefix (CausalJournal.keepalivePrepare pid) w a h) := by
  have path := keepalive_cases pid w a
  cases native : ((OccurrenceHandshake.keepalivePrepare pid).run w).run a with
  | error stop => rw [keepalive_stopped native]; exact .stopped (native ▸ path)
  | ok out =>
    obtain ⟨⟨ready,v⟩,b⟩:=out
    rw [keepalive_recorded native]
    exact .returned (native ▸ path)

/-- The original selected take receipt survives a failed native key borrow;
its full selected carrier is at that actual clear/receipt cut. -/
theorem selected_borrow_stopped (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (nonempty : p.staged.isEmpty=false)
    (failed : ((Take.borrow (some p)).run (queueWorld pid p [] d w)).run (clock a .stagedEmpty false)=.error stop) :
    let r : Take.Receipt := ⟨pid,⟨some p,w,queueWorld pid p [] d w,a,clock a .stagedEmpty false⟩⟩
    runWGPrefix (CausalJournal.selection pid) w a h=(.error stop,h++[.stagingTaken r]) ∧
      ∃ after generation, after=transferLocation (.staged generation pid p.internalId) (.selected h.length) ledger ∧
        CompleteSelected.Ready after debts locals generation pid p h.length
          (h++[.stagingTaken r]) (queueWorld pid p [] d w) (clock a .stagedEmpty false) := by
  obtain ⟨after,generation,_,transfer,ready,_⟩:=take_recorded before device resident nonempty (a:=a)
  refine ⟨?_,after,generation,transfer,ready⟩
  rw [selection_after_take (take_nonempty device resident nonempty),failed]

/-- Empty take is a normal idle invocation; both its actual take and outer
selection receipts retain the same native world and unchanged ledger. -/
theorem empty_selection_accounted (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (empty : p.staged.isEmpty=true) :
    let b := clock a .stagedEmpty true
    let r : Take.Receipt := ⟨pid,⟨none,w,w,a,b⟩⟩
    let history := (h++[.stagingTaken r])++[.old (.responder (.selected pid ⟨none,w,w,a,b⟩))]
    Accounted history ledger debts locals w ∧
      runWGPrefix (CausalJournal.selection pid) w a h=(.ok ((none,w),b),history) := by
  let r : Take.Receipt := ⟨pid,⟨none,w,w,a,clock a .stagedEmpty true⟩⟩
  have first := before.append_quiet [Event.stagingTaken r]
    (fun _ member=>by cases List.mem_singleton.mp member; rfl)
    (fun _ member=>by cases List.mem_singleton.mp member; intro position; rfl)
  have last := first.append_quiet [.old (.responder (.selected pid ⟨none,w,w,a,clock a .stagedEmpty true⟩))]
    (fun _ member=>by cases List.mem_singleton.mp member; rfl)
    (fun _ member=>by cases List.mem_singleton.mp member; intro position; rfl)
  refine ⟨last,?_⟩
  rw [selection_after_take (take_empty device resident empty)]
  rfl

/-- The original keepalive invocation continues into the actual staging
callback only after the completed preparation receipt. Later Stop retains
that same source continuation, rather than changing the preparation cut. -/
theorem keepalive_continuation
    (native : ((OccurrenceHandshake.keepalivePrepare pid).run w).run a=.ok ((ready,v),b)) :
    runWGPrefix (Driver.keepaliveObserved CausalJournal.hooks pid) w a h=
      if ready then runWGPrefix (Driver.stagingObserved CausalJournal.hooks pid) v b
        (h++[keepaliveEvent pid ready w v a b])
      else (.ok (((),v),b),h++[keepaliveEvent pid ready w v a b]) := by
  unfold Driver.keepaliveObserved
  rw [runWGPrefix,runStatePrefix_bind]
  have first := keepalive_recorded (h:=h) native
  change runStatePrefix (CausalJournal.hooks.keepalivePrepare pid) w a h=_ at first
  rw [first]
  cases ready <;> rfl

theorem restore_old :
    ((runWGPrefix (CausalJournal.stagedRestore pid packets) w a h).2.filterMap old?)=h.filterMap old? :=
  restore_projection old? (by intros; rfl)

theorem keepalive_old :
    ((runWGPrefix (CausalJournal.keepalivePrepare pid) w a h).2.filterMap old?)=h.filterMap old? :=
  keepalive_projection old? (by intros; rfl)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
