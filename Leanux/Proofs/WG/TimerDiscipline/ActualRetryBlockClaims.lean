import Leanux.Proofs.WG.TimerDiscipline.ActualRetryBlockModel
import Leanux.Proofs.WG.TimerDiscipline.OuterAdjacentClaims
import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Env

/-- The existing actual dispatch certificate gives the peer's per-pair effect;
no new ownership, positive-reference, readiness or rearm assumption is added. -/
theorem actualRetryPair_effect (jPass : UInt64) (pid : PeerId) (pair : ActualRetryPair)
    (matched : ActualRetryPairMatches jPass pid pair)
    (certified : OuterAdjacentRetryPair jPass pair.1 pair.2) : ActualRetryBlockEffect pid pair [] := by
  obtain ⟨d,after,we,device,empty,selected,site,afterDevice,nonempty⟩ := matched
  obtain ⟨observation,certificate,_,_⟩ := certified d after pid we device empty selected site afterDevice nonempty
  obtain ⟨cut,send,p,seen,timer,inspection,sent,cutDevice,resident,limit,completed⟩ := certificate
  obtain ⟨queuedDev,queued,queuedDevice,queue,stored,fresh,picked,worker,view,work⟩ := completed
  have initial : pair.1.before.toSnapshot.peerAt pid = some p := by
    simp only [Campaign2.Snapshot.peerAt,device,Option.bind_some,resident]
  have finalQueue := congrArg Prod.fst work
  change pair.2.after.wg.device.map Device.sendWorkQueue = some [] at finalQueue
  cases outDevice : pair.2.after.wg.device with
  | none => simp [outDevice] at finalQueue
  | some out =>
    cases outPeer : out.peers[pid]? with
    | none => simp [workerObservation,Campaign2.Snapshot.peerAt,outDevice,outPeer] at view
    | some q =>
      have fields : q.internalId = p.internalId ∧
          q.timerHandshakeAttempts = p.timerHandshakeAttempts + 1 ∧ q.refcount = p.refcount := by
        simpa [workerObservation,Campaign2.Snapshot.peerAt,outDevice,outPeer,workerView] using view
      have pending : q.handshakePending = false := by
        have flag := congrArg Prod.snd work
        simpa [workObservation,outDevice,outPeer] using flag
      refine ⟨p,q,initial,?_,fields.1,fields.2.1,fields.2.2,pending,?_,finalQueue⟩
      · simp [actualRetryBlockExit,Campaign2.Snapshot.peerAt,outDevice,outPeer]
      · omega

private theorem outerTimerChain_head_before (jPass : UInt64)
    (entry final : Campaign2.Product.Snapshot) (control last : TimerOuterControl)
    (indices : List Nat) (head : OuterTimerTurnReceipt) (tail : List OuterTimerTurnReceipt)
    (chain : OuterTimerChain jPass entry control indices (head :: tail) final last) : head.before = entry := by
  cases chain <;> rfl

/-- Only continuity is taken from the projected chain. The retry certificates
used below still come from the actual normal observer execution. -/
theorem outerTimerChain_adjacent (jPass : UInt64)
    (entry final : Campaign2.Product.Snapshot) (control last : TimerOuterControl)
    (indices : List Nat) (receipts front suffix : List OuterTimerTurnReceipt)
    (left right : OuterTimerTurnReceipt)
    (chain : OuterTimerChain jPass entry control indices receipts final last)
    (adjacent : receipts = front ++ left :: right :: suffix) : left.after = right.before := by
  induction chain generalizing front with
  | nil entry control =>
    have count := congrArg List.length adjacent
    simp only [List.length_nil,List.length_append,List.length_cons] at count
    omega
  | done head rest control step valid =>
    have count := congrArg List.length adjacent
    simp only [List.length_nil,List.length_append,List.length_cons] at count
    omega
  | yield head rest control last tail final step valid tailChain ih =>
    cases front with
    | nil =>
      simp only [List.nil_append,List.cons.injEq] at adjacent
      obtain ⟨rfl,rfl⟩ := adjacent
      exact (outerTimerChain_head_before jPass _ _ _ _ _ right suffix tailChain).symm
    | cons before front =>
      simp only [List.cons_append,List.cons.injEq] at adjacent
      exact ih front adjacent.2

/-- Compose only certificates obtained for adjacent actual receipts. The chain
supplies equal observation boundaries, never a replacement execution. -/
theorem actualRetryBlock_effect_of_receipts (jPass : UInt64) (pid : PeerId)
    (receipts : List OuterTimerTurnReceipt)
    (continuous : ∀ front suffix left right,
      receipts = front ++ left :: right :: suffix → left.after = right.before)
    (certified : ∀ front suffix left right,
      receipts = front ++ left :: right :: suffix → OuterAdjacentRetryPair jPass left right)
    (first : ActualRetryPair) (rest : List ActualRetryPair)
    (front suffix : List OuterTimerTurnReceipt)
    (turns : receipts = front ++ actualRetryBlockTurns (first :: rest) ++ suffix)
    (eligible : ∀ pair ∈ first :: rest, ActualRetryPairMatches jPass pid pair) :
    ActualRetryBlockEffect pid first rest := by
  induction rest generalizing first front with
  | nil =>
    apply actualRetryPair_effect jPass pid first (eligible first (by simp))
    apply certified front suffix first.1 first.2
    simpa [actualRetryBlockTurns,List.append_assoc] using turns
  | cons next rest ih =>
    have headTurns : receipts = front ++ first.1 :: first.2 ::
        (actualRetryBlockTurns (next :: rest) ++ suffix) := by
      simpa [actualRetryBlockTurns,List.append_assoc] using turns
    have headEffect := actualRetryPair_effect jPass pid first (eligible first (by simp))
      (certified front (actualRetryBlockTurns (next :: rest) ++ suffix) first.1 first.2 headTurns)
    have tailTurns : receipts = (front ++ [first.1,first.2]) ++
        actualRetryBlockTurns (next :: rest) ++ suffix := by
      simpa [actualRetryBlockTurns,List.append_assoc] using turns
    have tailEffect := ih next (front ++ [first.1,first.2]) tailTurns
      (fun pair member => eligible pair (List.mem_cons_of_mem first member))
    have touching : first.2.after = next.1.before := by
      apply continuous (front ++ [first.1])
        (next.2 :: (actualRetryBlockTurns rest ++ suffix)) first.2 next.1
      simpa [actualRetryBlockTurns,List.append_assoc] using turns
    obtain ⟨p,q,start,headEnd,headId,headCount,headRefs,_,_,_⟩ := headEffect
    obtain ⟨p',q',tailStart,finish,tailId,tailCount,tailRefs,pending,bound,queue⟩ := tailEffect
    change first.2.after.toSnapshot.peerAt pid = some q at headEnd
    rw [touching,tailStart] at headEnd
    have same : p' = q := Option.some.inj headEnd
    subst p'
    refine ⟨p,q',start,finish,tailId.trans headId,?_,tailRefs.trans headRefs,pending,bound,queue⟩
    simp only [List.length_nil] at headCount
    simp only [List.length_cons]
    omega

/-- A contiguous nonempty same-peer retry block is counted at its last send
exit. Pair eligibility is read from the actual receipt history; its execution
and certificates follow from the same normal whole-episode observer run. -/
theorem runTimers_actual_retry_block_counts (jPass : UInt64) :
    Campaign2.Product.Ensures (observedRunTimersEpisode jPass) (fun _ => True)
      (fun result _ => ∀ front suffix first rest pid,
        result.1.turns = front ++ actualRetryBlockTurns (first :: rest) ++ suffix →
        (∀ pair ∈ first :: rest, ActualRetryPairMatches jPass pid pair) →
        ActualRetryBlockEffect pid first rest) := by
  intro initial result final _ run front suffix first rest pid turns eligible
  have pairs := runTimers_adjacent_retry_pairs jPass initial result final True.intro run
  have episode := runTimers_episode_receipt jPass (Campaign2.Product.snapshot initial)
    initial result final rfl run
  rcases episode with ⟨reset,valid⟩
  split at valid
  · have empty := valid.2.1
    have count := congrArg List.length turns
    simp only [empty,List.length_nil,List.length_append,actualRetryBlockTurns,
      List.flatMap_cons,List.length_cons,List.length_append,List.length_nil] at count
    omega
  · have chain := valid.2.1
    apply actualRetryBlock_effect_of_receipts jPass pid result.1.turns
      (fun front suffix left right eq => outerTimerChain_adjacent jPass _ _ _ _ _ _
        front suffix left right chain eq) pairs first rest front suffix turns eligible

end Leanux.Proofs.WG.TimerDiscipline
