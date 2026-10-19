import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingInteriorFrames

/-! The clear write precedes the take receipt. The original ordered cohort
is retained as an entry obligation during this silent interval, then moves
to the selected location at the actual receipt before key borrowing. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity Staged.Obligations Staged.Origins CausalJournal CompleteCarrier
open HandshakeSecurity.StagedConservation
set_option maxHeartbeats 600000

theorem take_empty (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (empty : p.staged.isEmpty=true) :
    ((Take.takePrefix pid).run w).run a=.ok ((none,w),clock a .stagedEmpty true) := by
  rw [take_factor]
  simp only [StateT.run_bind,take_read device resident,empty]
  rfl

theorem take_nonempty (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (nonempty : p.staged.isEmpty=false) :
    ((Take.takePrefix pid).run w).run a=
      .ok ((some p,queueWorld pid p [] d w),clock a .stagedEmpty false) := by
  rw [take_factor,MaterialOrigin.bind_ok_ambient]
  refine ⟨(p,false),w,clock a .stagedEmpty false,?_,?_⟩
  · simpa only [nonempty] using take_read (a:=a) device resident
  · unfold takeTail
    simp only [Bool.false_eq_true,ite_false]
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨(),_,_,take_write device,rfl⟩

theorem take_read_stopped (failed : ((getPeer pid).run w).run a=.error stop) :
    ((Take.takePrefix pid).run w).run a=.error stop := by
  unfold Take.takePrefix
  simp only [StateT.run_bind,failed]
  rfl

inductive TakeCase (pid : PeerId) (w : WGWorld) (a : Ambient) :
    Except Stop ((Option Peer × WGWorld) × Ambient) → Prop where
  | readStopped (failed : ((getPeer pid).run w).run a=.error stop) : TakeCase pid w a (.error stop)
  | empty (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (empty : p.staged.isEmpty=true) : TakeCase pid w a (.ok ((none,w),clock a .stagedEmpty true))
  | taken (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (nonempty : p.staged.isEmpty=false) : TakeCase pid w a
        (.ok ((some p,queueWorld pid p [] d w),clock a .stagedEmpty false))

theorem TakeCase.literal (path : TakeCase pid w a result) : ((Take.takePrefix pid).run w).run a=result := by
  cases path with
  | readStopped failed => exact take_read_stopped failed
  | empty device resident empty => exact take_empty device resident empty
  | taken device resident nonempty => exact take_nonempty device resident nonempty

theorem take_cases (pid : PeerId) (w : WGWorld) (a : Ambient) :
    TakeCase pid w a (((Take.takePrefix pid).run w).run a) := by
  cases read : ((getPeer pid).run w).run a with
  | error stop => rw [take_read_stopped read]; exact .readStopped read
  | ok out =>
    obtain ⟨⟨p,v⟩,b⟩:=out
    obtain ⟨rfl,rfl,d,device,resident⟩:=Origins.getPeer_return pid w v p a b read
    cases empty : p.staged.isEmpty with
    | false => rw [take_nonempty device resident empty]; exact .taken device resident empty
    | true => rw [take_empty device resident empty]; exact .empty device resident empty

/-- Ticket identity and order remain the original cohort at the cleared
pre-receipt cut; absence of the native queue does not erase obligations. -/
theorem take_pending (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (nonempty : p.staged.isEmpty=false) :
    ((Take.takePrefix pid).run w).run a=
      .ok ((some p,queueWorld pid p [] d w),clock a .stagedEmpty false) ∧
    Aligned (Born h d.ifindex pid p.internalId) (pendingAt (.staged d.ifindex pid p.internalId) ledger) p.staged ∧
    Staged.stagedAt (queueWorld pid p [] d w) pid=some (p.internalId,[]) ∧
    Staged.dropped (queueWorld pid p [] d w)=Staged.dropped w := by
  have aligned := before.entry.core.queues d.ifindex pid p.internalId
  refine ⟨take_nonempty device resident nonempty,?_,(queue_geometry device).1,(queue_geometry device).2.1⟩
  simpa [stagedPackets,Packets.epoch,Staged.stagedAt,device,resident] using aligned

/-- The selected carrier is obtained at this exact receipt/world, with the
native take anchor. The succeeding key-borrow call is still the real child. -/
theorem take_recorded (before : Accounted h ledger debts locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) (nonempty : p.staged.isEmpty=false) :
    let v := queueWorld pid p [] d w
    let b := clock a .stagedEmpty false
    let r : Take.Receipt := ⟨pid,⟨some p,w,v,a,b⟩⟩
    ∃ after generation, Staged.Obligations.Step ledger after ∧
      after=transferLocation (.staged generation pid p.internalId) (.selected h.length) ledger ∧
      CompleteSelected.Ready after debts locals generation pid p h.length (h++[.stagingTaken r]) v b ∧
      StagedEntry.SelectionContinuation r h := by
  let r : Take.Receipt := ⟨pid,⟨some p,w,queueWorld pid p [] d w,a,clock a .stagedEmpty false⟩⟩
  have native : r.Valid:=take_nonempty device resident nonempty
  obtain ⟨after,generation,step,transfer,ready⟩:=CompleteSelected.taken r native rfl before
  exact ⟨after,generation,step,transfer,ready,StagedEntry.selection_continuation r native before.entry⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.StagingInterior
