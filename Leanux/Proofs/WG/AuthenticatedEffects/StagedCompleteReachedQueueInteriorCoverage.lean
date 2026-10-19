import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueueInteriorFrames

/-! Exhaustive native queue cases retain the actual failing first read or
queue choice. A successful choice fixes all later reads and writes; there
is no invented final world for either Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompleteCarrier

theorem drop_read_stopped (failed : ((getPeer pid).run w).run a=.error stop) :
    ((txDropSource pid).run w).run a=.error stop := by
  simp only [txDropSource,StateT.run_bind,failed]
  rfl

theorem peek_read_stopped (failed : ((getPeer pid).run w).run a=.error stop) :
    ((txPeekSource pid).run w).run a=.error stop := by
  simp only [txPeekSource,StateT.run_bind,failed]
  rfl

theorem peek_choice_stopped (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (failed : ((p.txQueue.peek).run w).run a=.error stop) :
    ((txPeekSource pid).run w).run a=.error stop := by
  simp only [txPeekSource,StateT.run_bind,read_peer device resident]
  change (do let out ← ((p.txQueue.peek).run w).run a; _) = _
  rw [failed]
  rfl

inductive DropCase (pid : PeerId) (w : WGWorld) (a : Ambient) :
    Except Stop ((Unit × WGWorld) × Ambient) → Prop where
  | stopped (failed : ((getPeer pid).run w).run a=.error stop) : DropCase pid w a (.error stop)
  | returned (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
      DropCase pid w a (.ok (((),replacePeer w d pid {p with txQueue := p.txQueue.dropPeeked}),a))

theorem DropCase.literal (path : DropCase pid w a result) : ((txDropSource pid).run w).run a=result := by
  cases path with
  | stopped failed => exact drop_read_stopped failed
  | returned device resident => exact drop_run device resident

theorem drop_cases (pid : PeerId) (w : WGWorld) (a : Ambient) :
    DropCase pid w a (((txDropSource pid).run w).run a) := by
  cases read : ((getPeer pid).run w).run a with
  | error stop => rw [drop_read_stopped read]; exact .stopped read
  | ok out =>
    obtain ⟨⟨p,v⟩,b⟩ := out
    obtain ⟨same,clock,d,device,resident⟩ := Origins.getPeer_return pid w v p a b read
    subst v
    subst b
    rw [drop_run device resident]
    exact .returned device resident

inductive PeekCase (pid : PeerId) (w : WGWorld) (a : Ambient) :
    Except Stop ((Option (List SkbId) × WGWorld) × Ambient) → Prop where
  | readStopped (failed : ((getPeer pid).run w).run a=.error stop) : PeekCase pid w a (.error stop)
  | choiceStopped (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (failed : ((p.txQueue.peek).run w).run a=.error stop) : PeekCase pid w a (.error stop)
  | returned (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (chosen : ((p.txQueue.peek).run w).run a=.ok (((first,queue),w),b)) :
      PeekCase pid w a (.ok ((first,replacePeer w d pid {p with txQueue := queue}),b))

theorem PeekCase.literal (path : PeekCase pid w a result) : ((txPeekSource pid).run w).run a=result := by
  cases path with
  | readStopped failed => exact peek_read_stopped failed
  | choiceStopped device resident failed => exact peek_choice_stopped device resident failed
  | returned device resident chosen => exact peek_run device resident chosen

theorem peek_cases (pid : PeerId) (w : WGWorld) (a : Ambient) :
    PeekCase pid w a (((txPeekSource pid).run w).run a) := by
  cases read : ((getPeer pid).run w).run a with
  | error stop => rw [peek_read_stopped read]; exact .readStopped read
  | ok out =>
    obtain ⟨⟨p,v⟩,b⟩ := out
    obtain ⟨same,clock,d,device,resident⟩ := Origins.getPeer_return pid w v p a b read
    subst v
    subst b
    cases choice : ((p.txQueue.peek).run w).run a with
    | error stop =>
      rw [peek_choice_stopped device resident choice]
      exact .choiceStopped device resident choice
    | ok out =>
      obtain ⟨⟨⟨first,queue⟩,v⟩,b⟩ := out
      have same := (prev_peek_normal p.txQueue w v a b first queue choice).2.2.2
      subst v
      rw [peek_run device resident choice]
      exact .returned device resident choice

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
