import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontResidualPath
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixAdmissionCheckpoint
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteOriginalRelease

/-! The pending overflow and routed receipts belong to the same completed
native runs as their silent cuts. Splice positions remain unrecorded births
until the original routed receipt; native stops never invent an error world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity Staged.Obligations CausalJournal CompleteCarrier
set_option maxHeartbeats 600000

def overflowHistory (pid : PeerId) (w v : WGWorld) (a b : Ambient) (h : List Event) : List Event :=
  h++[.stagedDisposal (.overflow pid ⟨(),w,v,a,b⟩)]

/-- The receipt settles the exact native removed prefix, at this history
position. The complete carrier is restored at this actual receipt cut. -/
theorem trim_account (before : Accounted h ledger debts locals w)
    (run : ((xmitTrim pid).run w).run a=.ok (((),v),b)) :
    ∃ after, Accounted (overflowHistory pid w v a b h) after debts locals v ∧
      Staged.Obligations.Step ledger after ∧
      runWGPrefix (StagedAdmission.Front.ops.trim pid) w a h=
        (.ok (((),v),b),overflowHistory pid w v a b h) := by
  let r : WGRunWitness Unit:=⟨(),w,v,a,b⟩
  obtain ⟨partition⟩:=HandshakeSecurity.StagedDisposal.overflow_exact pid r run
  obtain ⟨d,device⟩ : ∃ d, w.dev=some d := by
    cases found : w.dev with
    | none => have impossible:=partition.before; simp [Staged.stagedAt,r,found] at impossible
    | some d => exact ⟨d,rfl⟩
  have epoch : Packets.epoch w=some d.ifindex := by simp [Packets.epoch,device]
  have cut := StagedAdmission.Front.Checkpoint.trimmed
    (entry:=StagedAdmission.Front.coreEntry before.entry.core) pid r run partition d.ifindex epoch before.entry.core.queues
  have material := (ProjectedAction.iff_run_ambient _ _ _).mp
    (StagedAdmission.Front.Material.trim pid) w a () v b run
  have ownership := (ProjectedAction.iff_run_ambient _ _ _).mp
    (StagedAdmission.Front.Ownership.trim pid) w a () v b run
  refine ⟨_,CompletePrefix.Admission.checkpoint_accounted cut rfl before material ownership,
    cut.accounted.1,?_⟩
  rw [StagedAdmission.Front.trim_run,run]
  rfl

/-- After the actual trim receipt, the next silent splice is the original
source call and the continuation is still the original routed result. -/
theorem splice_resolve_run
    (trim : ((xmitTrim pid).run w).run a=.ok (((),v),b)) :
    runWGPrefix (Front.resolve input (.splice pid packets)) w a h=
      let history:=overflowHistory pid w v a b h
      match ((xmitSplice pid packets).run v).run b with
      | .error stop => (.error stop,history)
      | .ok (((),q),c) => (.ok ((.ok pid,q),c),history) := by
  rw [Front.resolve_splice]
  change runStatePrefix (_ >>= _) w a h=_
  rw [runStatePrefix_bind]
  have recorded := StagedAdmission.Front.trim_run pid w a h
  rw [trim] at recorded
  change runStatePrefix _ _ _ _=_ at recorded
  rw [recorded]
  change runStatePrefix (_ >>= _) v b (overflowHistory pid w v a b h)=_
  rw [runStatePrefix_bind,liftWGPrefix,runStatePrefix_lift]
  cases native : ((xmitSplice pid packets).run v).run b with
  | error stop => rfl
  | ok out => obtain ⟨⟨value,q⟩,c⟩:=out; cases value; rfl

/-- Exact same-source bridge back to the original whole front, before its
routed birth receipt. Input and overflow positions are both retained. -/
theorem selected_splice
    (selected : Front.Selected input (inputHistory input h) w a (.splice pid packets) u c)
    (trim : ((xmitTrim pid).run u).run c=.ok (((),v),b))
    (spliced : ((xmitSplice pid packets).run v).run b=.ok (((),q),z)) :
    Transmit.Path input h w a (.ok pid) q z (overflowHistory pid u v c b (inputHistory input h)) := by
  constructor
  rw [selected.continuation,splice_resolve_run trim,spliced]

/-- Every new queue position is the corresponding actual input occurrence;
the old queue length distinguishes a duplicate payload from a new position. -/
theorem splice_position (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (position : packets[ordinal]?=some packet) :
    ((xmitSplice pid packets).run w).run a=.ok (((),splicedWorld pid p packets d w),a) ∧
    (stagedPackets d.ifindex pid p.internalId (splicedWorld pid p packets d w))[p.staged.length+ordinal]?=some packet := by
  refine ⟨splice_run device resident,?_⟩
  simp only [stagedPackets,Packets.epoch,splicedWorld,Option.map_some,ite_true,
    Staged.stagedAt,Option.bind_some,Std.TreeMap.getElem?_insert_self,Option.map_some]
  rw [List.getElem?_append_right (by omega)]
  simpa only [Nat.add_sub_cancel_left] using position

/-- A genuine failed splice is a failed native peer read, after the actual
trim receipt. There is no partially returned world hidden behind the error. -/
theorem splice_failed (run : ((xmitSplice pid packets).run w).run a=.error stop) :
    ((getPeer pid).run w).run a=.error stop := by
  cases read : ((getPeer pid).run w).run a with
  | error reason =>
    unfold xmitSplice at run
    simp only [StateT.run_bind,read] at run
    cases run
    rfl
  | ok out =>
    obtain ⟨⟨peer,v⟩,b⟩:=out
    obtain ⟨rfl,rfl,d,device,resident⟩:=Origins.getPeer_return pid w v peer a b read
    rw [splice_run device resident] at run
    cases run

/-- The release residual exposes the actual release-cut receipt and native
finish, rather than an unrelated checkpoint world. Primitive interiors of
releaseCut itself remain a separate source coverage obligation. -/
theorem release_cases (before : Accounted h ledger debts locals w) (peer : Option PeerId) :
    match (runWGPrefix (StagedAdmission.Front.ops.put peer) w a h).1 with
    | .error stop => StagedTerminalComplete.Source.Original.Frontier ledger debts locals peer w a h stop
        (runWGPrefix (StagedAdmission.Front.ops.put peer) w a h).2
    | .ok (((),v),_) => StagedTerminalComplete.Source.Original.Returned ledger debts locals peer w a h
        (runWGPrefix (StagedAdmission.Front.ops.put peer) w a h).2 v :=
  StagedTerminalComplete.Source.Original.actual_cases peer a before.entry before.complete

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual
