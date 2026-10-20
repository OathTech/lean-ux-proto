import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointSource

/-! Canonical witnesses are constructed from each literal worker branch,
including the nested encryption iteration and every crypt-ahead guard. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

private noncomputable def nativeBindShape (body : Leanux.M α) (next : α → Leanux.M β)
    (head : Shape (liftPrefix body)) (tail : ∀ value, Shape (liftPrefix (next value))) :
    Shape (liftPrefix (body >>= next)) := by
  have equation : (liftPrefix (body >>= next) : PrefixM Event β) =
      (liftPrefix body >>= fun value => liftPrefix (next value)) := by
    funext w h
    change ((body >>= next).run w,h) = runPrefix (liftPrefix body >>= fun value => liftPrefix (next value)) w h
    rw [runPrefix_bind,runPrefix_lift]
    cases run : body.run w <;> simp only [StateT.run_bind,run,runPrefix_lift] <;> rfl
  rw [equation]
  exact .bind head tail

noncomputable def condReschedShape (worker : Worker) : Shape (liftPrefix (Env.condResched worker)) := by
  unfold Env.condResched
  cases worker.resched? with
  | none => exact .native (.invariant _)
  | some site =>
      apply nativeBindShape _ _ (.native .hiddenSite)
      intro next
      split
      · exact .pure false
      · apply nativeBindShape _ _ (.native (.ambientAction (AmbientM.hidden site)))
        intro ignored
        exact .pure true

noncomputable def reschedShape (worker : Worker) (site : Decision) :
    Shape (Driver.reschedObserved worker site) :=
  .marked (.resched worker site) (.bind (condReschedShape worker) (fun yes => .native (.branch site yes)))

noncomputable def workerShape (worker : Worker) (pid : Option Nat)
    (step afterItem : PrefixM Event Bool) (before : Shape step) (after : Shape afterItem) :
    Shape (workerIterPrefix worker pid step afterItem) := by
  unfold workerIterPrefix
  apply Shape.bind before
  intro more
  cases more with
  | false => exact .pure _
  | true => exact .bind after (fun yes => .pure (if yes then IterResult.yielded else IterResult.continued))

noncomputable def encryptTailShape (item : Option (List SkbId)) : Shape (Driver.encryptTailObserved hooks item) :=
  .marked (.encryptTail item) (workerShape _ _ _ _ (.child (.encrypt item)) (reschedShape _ _))

noncomputable def encryptShape : Shape (Driver.encryptIterObserved hooks) :=
  .marked .encrypt (.bind (.child .poll) (fun item => .bind (.child .softirq) (fun _ => encryptTailShape item)))

noncomputable def txShape (pid : PeerId) : Shape (Driver.txIterObserved hooks pid) :=
  .marked (.tx pid) (workerShape _ _ _ _ (.child (.transmit pid)) (reschedShape _ _))

noncomputable def decryptStepShape : Shape (Driver.decryptStepObserved hooks) := by
  unfold Driver.decryptStepObserved RxWorkers.decryptWith
  apply Shape.bind (.child .softirq)
  intro ignored
  apply Shape.bind (.child .prepare)
  intro peer
  cases peer with
  | none => exact .pure false
  | some pid => exact .bind (.child .irqExit) (fun _ =>
      .bind (.child (.release pid)) (fun _ => .bind (.child .softirq) (fun _ => .pure true)))

noncomputable def decryptShape : Shape (Driver.decryptIterObserved hooks) :=
  .marked .decrypt (workerShape _ _ _ _ decryptStepShape (reschedShape _ _))

noncomputable def receiveShape : Shape (Driver.receiveIterObserved hooks) :=
  .marked .receive (workerShape _ _ _ _ (.child .handshake) (condReschedShape .receiveWorker))

noncomputable def aheadPrefixShape (pid : PeerId) : Shape (EncryptionEntry.aheadPrefix pid) := by
  apply Shape.marked (.aheadPrefix pid)
  unfold EncryptionEntry.aheadPrefix
  apply Shape.bind (.native .ambient)
  intro ambient
  split
  · exact .pure none
  · apply Shape.bind (.native (.peer pid))
    intro peer
    cases head : peer.txQueue.all.head? with
    | none => exact .pure none
    | some item =>
      dsimp only
      cases first : item.head? with
      | none => exact .native (.invariant _)
      | some skb =>
        apply Shape.bind (.native (.packet skb))
        intro packet
        split
        · exact .pure none
        · apply Shape.bind (.native .hiddenSite)
          intro site
          split
          · apply Shape.bind (.native .ambient)
            intro state
            cases selected : state.suspended.find? (·.worker == .encryptWorker) with
            | none => exact .native (.stopped _)
            | some enc => exact .bind (.native (.appendWork pid)) (fun _ => .pure (some enc))
          · exact .pure none

noncomputable def aheadFinishShape (pid : PeerId) (selected : Activation) (result : IterResult) :
    Shape (EncryptionEntry.aheadFinish pid selected result) := by
  apply Shape.marked (.aheadFinish pid selected result)
  unfold EncryptionEntry.aheadFinish
  apply Shape.bind (.native (.eraseWork pid))
  intro ignored
  cases result with
  | continued => exact .native (.advance selected)
  | ended => exact .native (.stopped _)
  | yielded => exact .native (.invariant _)

noncomputable def aheadBranchShape (pid : PeerId) (selected : Option Activation) :
    Shape (EncryptionEntry.aheadBranch pid selected) := by
  cases selected with
  | none => exact .pure ()
  | some enc => exact .bind encryptShape (aheadFinishShape pid enc)

noncomputable def aheadShape (pid : PeerId) : Shape (Driver.cryptAheadObserved hooks pid) := by
  apply Shape.marked (.ahead pid)
  rw [EncryptionEntry.ahead_factor]
  exact .bind (aheadPrefixShape pid) (aheadBranchShape pid)

noncomputable def iterationShape (activation : Activation) : Shape (Driver.iterationObserved hooks activation) := by
  apply Shape.marked (.iteration activation)
  unfold Driver.iterationObserved
  cases activation.worker with
  | encryptWorker => exact encryptShape
  | decryptWorker => exact decryptShape
  | receiveWorker => exact receiveShape
  | txWorker =>
    cases activation.pid with
    | none => exact .native (.invariant _)
    | some pid => exact .bind (aheadShape pid) (fun _ => txShape pid)
  | _ => exact .native (.invariant _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Iteration.Points
