import Leanux.Proofs.WG.Queues.RxRingEntry

/-! Complete original decrypt worker, with callbacks allowed to perform
their own refined ring operations. Softirq runs before the ring is read.
The consumed-ring event precedes packet lookup/decryption/publication, so a
later Stop retains it. This is not packet-store or peer-queue conservation. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def stepSource (softirq irq : M Unit) : M Bool := do
  softirq
  match ← pollSource with
  | none => return false
  | some id =>
    let decrypted ← decryptPacket (← getRxSkb id)
    if ← branch .decWorkerDecrypted decrypted.isSome then
      let some d := decrypted | invariant "unreachable"
      setRxSkb id fun _ => d
      enqueuePerPeerRx irq id .crypted
    else enqueuePerPeerRx irq id .dead
    softirq
    return true

private theorem bind_congr (a : M α) (f g : α → M β) (h : ∀ x, f x = g x) :
    (a >>= f) = (a >>= g) := congrArg (fun k => a >>= k) (funext h)

theorem stepSource_eq (softirq irq : M Unit) : stepSource softirq irq = decryptStep softirq irq := by
  unfold stepSource pollSource decryptStep
  simp only [bind_assoc]
  apply bind_congr
  intro _
  apply bind_congr
  intro d
  cases hc : d.decryptQueue.consume with
  | mk item ring =>
    cases item <;> simp only [bind_assoc, pure_bind]
    all_goals
      repeat' first
        | rfl
        | apply bind_congr
        | intro x
        | split

def step (softirq irq : Obs Unit) : Obs Bool := do
  softirq
  match ← poll with
  | none => return false
  | some id =>
    let decrypted ← liftPrefix (decryptPacket (← liftPrefix (getRxSkb id)))
    if ← liftPrefix (branch .decWorkerDecrypted decrypted.isSome) then
      let some d := decrypted | liftPrefix (invariant "unreachable")
      liftPrefix (setRxSkb id fun _ => d)
      enqueuePeer irq id .crypted
    else enqueuePeer irq id .dead
    softirq
    return true

def iter (softirq irq : Obs Unit) (needResched : Obs Bool) : Obs IterResult :=
  workerIterPrefix .decryptWorker none (step softirq irq)
    (do liftPrefix (branch .decWorkerNeedResched (← needResched)))

theorem step_erases (hs : ErasesPrefix softirq originalSoftirq) (hi : ErasesPrefix irq originalIrq) :
    ErasesPrefix (step softirq irq) (decryptStep originalSoftirq originalIrq) := by
  rw [← stepSource_eq]
  unfold step stepSource
  repeat' first
    | with_reducible exact hs
    | with_reducible exact poll_erases
    | with_reducible exact enqueuePeer_erases hi _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem iter_erases (hs : ErasesPrefix softirq originalSoftirq)
    (hi : ErasesPrefix irq originalIrq) (hr : ErasesPrefix needResched originalResched) :
    ErasesPrefix (iter softirq irq needResched) (decryptIter originalSoftirq originalIrq originalResched) := by
  unfold iter decryptIter
  exact workerIterPrefix_erases _ _ (step_erases hs hi)
    (erasesPrefix_bind hr (fun _ => erasesPrefix_lift _))

theorem step_preserves (hs : PrefixPreserves (Inv deviceIndex initial) (Safe initial) softirq)
    (hi : PrefixPreserves (Inv deviceIndex initial) (Safe initial) irq) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (step softirq irq) := by
  unfold step
  repeat' first
    | with_reducible exact hs
    | with_reducible exact poll_preserves
    | with_reducible exact enqueuePeer_preserves hi _ _
    | with_reducible exact lift_frame (getRx_frame _)
    | with_reducible exact lift_frame (decryptPacket_frame _)
    | with_reducible exact lift_frame (setRx_frame _ _)
    | with_reducible exact lift_frame (kernel (sameKernel_branch _ _))
    | with_reducible exact lift_frame (invariant_frame _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem iter_preserves (hs : PrefixPreserves (Inv deviceIndex initial) (Safe initial) softirq)
    (hi : PrefixPreserves (Inv deviceIndex initial) (Safe initial) irq)
    (hr : PrefixPreserves (Inv deviceIndex initial) (Safe initial) needResched) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (iter softirq irq needResched) := by
  unfold iter
  apply workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) (step_preserves hs hi)
  exact PrefixPreserves.bind hr (fun _ => lift_frame (kernel (sameKernel_branch _ _)))

/-- For any composed observer with this contract, every reached event prefix
has an original finite-ring execution witness. Normal completion additionally
identifies that replay ring with the actual device ring at the same interface index. Lifecycle-reset composition remains open. -/
theorem from_initial {g : Obs α}
    (hg : PrefixPreserves (Inv deviceIndex (PtrRing.init n)) (Safe (PtrRing.init n)) g)
    (hc : cell w = some (deviceIndex, PtrRing.init n)) :
    Safe (PtrRing.init n) (runPrefix g w []).2 ∧
      match (runPrefix g w []).1 with
      | .error _ => True
      | .ok (_, v) => Inv deviceIndex (PtrRing.init n) (runPrefix g w []).2 v := by
  obtain ⟨_, _, hs, ho⟩ := hg w [] (initial_inv hc)
  exact ⟨hs, ho⟩

/-- The four concrete source calls in this slice. Callback arguments are
used only by the worker constructors; entry calls discharge all their leaves. -/
inductive Call : Type → Type
  | enqueue (id : SkbId) : Call Int
  | consume (msg : List UInt8) (src : SkbSource) (ds : Nat) : Call Unit
  | step : Call Bool
  | iter : Call IterResult

def Call.observe (c : Call α) (softirq irq : Obs Unit) (resched : Obs Bool) : Obs α :=
  match c with
  | .enqueue id => RxRing.enqueue id
  | .consume msg src ds => RxRing.consume msg src ds
  | .step => RxRing.step softirq irq
  | .iter => RxRing.iter softirq irq resched

theorem Call.preserves (c : Call α)
    (hs : PrefixPreserves (Inv deviceIndex initial) (Safe initial) softirq)
    (hi : PrefixPreserves (Inv deviceIndex initial) (Safe initial) irq)
    (hr : PrefixPreserves (Inv deviceIndex initial) (Safe initial) resched) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (c.observe softirq irq resched) := by
  cases c with
  | enqueue id => exact enqueue_preserves id
  | consume msg src ds => exact consume_preserves msg src ds
  | step => exact step_preserves hs hi
  | iter => exact iter_preserves hs hi hr

/-- All outcomes have initialized ring conservation and ordinal refinement.
Only a normal return identifies the replay endpoint with a returned World. -/
theorem Call.initialized (c : Call α)
    (hs : PrefixPreserves (Inv deviceIndex (PtrRing.init n)) (Safe (PtrRing.init n)) softirq)
    (hi : PrefixPreserves (Inv deviceIndex (PtrRing.init n)) (Safe (PtrRing.init n)) irq)
    (hr : PrefixPreserves (Inv deviceIndex (PtrRing.init n)) (Safe (PtrRing.init n)) resched)
    (hc : cell w = some (deviceIndex, PtrRing.init n)) :
    let out := runPrefix (c.observe softirq irq resched) w []
    ∃ r, Initialized n out.2 r ∧
      match out.1 with
      | .error _ => True
      | .ok (_, v) => cell v = some (deviceIndex, r) := by
  obtain ⟨safe, done⟩ := from_initial (c.preserves hs hi hr) hc
  cases hout : (runPrefix (c.observe softirq irq resched) w []).1 with
  | error e =>
    obtain ⟨r, hj⟩ := safe
    exact ⟨r, hj.initialized, by simp [hout]⟩
  | ok result =>
    rcases result with ⟨x, v⟩
    simp only [hout] at done
    obtain ⟨r, hj, he⟩ := done
    exact ⟨r, hj.initialized, by simpa only [hout] using he⟩

end Leanux.Proofs.WG.Queues.RxRing
