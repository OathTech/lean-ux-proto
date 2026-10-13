import Leanux.Proofs.WG.Lifetimes.Decrypt
import Leanux.Proofs.Logged.PrefixWorkers

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! The original decrypt worker's step and scheduler iteration. Callback
observations are explicit and may change identities while preserving MixedInv. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def decryptStepPrefix (softirq irq : MixedM Unit) : MixedM Bool := do
  softirq
  match (← liftPrefix getDev).decryptQueue.consume with
  | (none, _) =>
    _ ← liftPrefix (branch .decWorkerConsumed false)
    return false
  | (some id, ring) =>
    _ ← liftPrefix (branch .decWorkerConsumed true)
    liftPrefix (modifyDev fun d => {d with decryptQueue := ring})
    let decrypted ← decryptPacketPrefix (← getRxSkbPrefix id)
    if ← liftPrefix (branch .decWorkerDecrypted decrypted.isSome) then
      let some d := decrypted | liftPrefix (invariant "unreachable")
      setRxSkbPrefix id fun _ => d
      enqueuePerPeerRxPrefix irq id .crypted
    else enqueuePerPeerRxPrefix irq id .dead
    softirq
    return true

def decryptIterPrefix (softirq irq : MixedM Unit) (needResched : MixedM Bool) : MixedM IterResult :=
  workerIterPrefix .decryptWorker none (decryptStepPrefix softirq irq)
    (do liftPrefix (branch .decWorkerNeedResched (← needResched)))

theorem decryptStepPrefix_erases (hs : ErasesPrefix softirq originalSoftirq)
    (hi : ErasesPrefix irq originalIrq) :
    ErasesPrefix (decryptStepPrefix softirq irq) (decryptStep originalSoftirq originalIrq) := by
  unfold decryptStepPrefix decryptStep
  apply erasesPrefix_bind hs
  intro _
  apply erasesPrefix_bind (erasesPrefix_lift getDev)
  intro dev
  generalize hconsume : dev.decryptQueue.consume = consumed
  rcases consumed with ⟨item, ring⟩
  cases item with
  | none =>
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    exact erasesPrefix_pure _
  | some id =>
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    apply erasesPrefix_bind (getRxSkbPrefix_erases _)
    intro pkt
    apply erasesPrefix_bind (decryptPacketPrefix_erases pkt)
    intro decrypted
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro yes
    dsimp only
    cases decrypted <;> cases yes
    all_goals simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals repeat' first
      | exact hs
      | exact erasesPrefix_lift _
      | exact erasesPrefix_pure _
      | exact setRxSkbPrefix_erases _ _
      | exact enqueuePerPeerRxPrefix_erases hi _ _
      | apply erasesPrefix_bind
      | intro x
    all_goals rfl

theorem decryptIterPrefix_erases (hs : ErasesPrefix softirq originalSoftirq)
    (hi : ErasesPrefix irq originalIrq) (hr : ErasesPrefix needResched originalResched) :
    ErasesPrefix (decryptIterPrefix softirq irq needResched)
      (decryptIter originalSoftirq originalIrq originalResched) := by
  unfold decryptIterPrefix decryptIter
  apply workerIterPrefix_erases
  · exact decryptStepPrefix_erases hs hi
  · exact erasesPrefix_bind hr (fun _ => erasesPrefix_lift _)

theorem getDev_sameKernel : SameKernel getDev := by
  apply sameKernel_of_wp
  intro k
  mvcgen [getDev, getK, invariant]

theorem getDev_identity : SameView identityView getDev :=
  identity_sameKernel getDev_sameKernel

theorem decryptQueue_identity (ring : PtrRing SkbId) :
    SameView identityView (modifyDev fun d => {d with decryptQueue := ring}) := by
  intro w x v hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents
  simp [Option.bind_map, Function.comp_def]

theorem decryptStepPrefix_preserves_ambient (c : AmbientContracts I)
    (hq : ∀ ring, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptQueue := ring})))
    (hs : PrefixPreserves I LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves I LifetimeEvent.Safe irq) :
    PrefixPreserves I LifetimeEvent.Safe (decryptStepPrefix softirq irq) := by
  unfold decryptStepPrefix
  apply PrefixPreserves.bind hs
  intro _
  apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) getDev getDev_sameKernel))
  intro dev
  split
  · apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro _
    exact PrefixPreserves.pure (fun h w hi => c.safe h w hi) _
  · apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro _
    apply PrefixPreserves.bind (hq _)
    intro _
    apply PrefixPreserves.bind (AmbientContracts.drop (c.getRx (fun _ => True) _))
    intro pkt
    apply PrefixPreserves.bind (AmbientContracts.drop (decryptPacketPrefix_spec_ambient c (fun _ => True) pkt))
    intro decrypted
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro yes
    dsimp only
    split
    · split
      · apply PrefixPreserves.bind (AmbientContracts.drop (c.setRx (fun _ => True) _ _))
        intro _
        apply PrefixPreserves.bind (enqueuePerPeerRxPrefix_preserves_ambient c hi _ _)
        intro _
        apply PrefixPreserves.bind hs
        intro _
        exact PrefixPreserves.pure (fun h w hi => c.safe h w hi) _
      · exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    · apply PrefixPreserves.bind (enqueuePerPeerRxPrefix_preserves_ambient c hi _ _)
      intro _
      apply PrefixPreserves.bind hs
      intro _
      exact PrefixPreserves.pure (fun h w hi => c.safe h w hi) _

theorem decryptIterPrefix_preserves_ambient (c : AmbientContracts I)
    (hq : ∀ ring, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptQueue := ring})))
    (hs : PrefixPreserves I LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves I LifetimeEvent.Safe irq)
    (hr : PrefixPreserves I LifetimeEvent.Safe needResched) :
    PrefixPreserves I LifetimeEvent.Safe (decryptIterPrefix softirq irq needResched) := by
  apply workerIterPrefix_preserves _ _ (fun h w hi => c.safe h w hi)
    (decryptStepPrefix_preserves_ambient c hq hs hi)
  exact PrefixPreserves.bind hr (fun _ => AmbientContracts.drop (c.branch (fun _ => True) _ _))

theorem decryptStepPrefix_preserves
    (hs : PrefixPreserves MixedInv LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves MixedInv LifetimeEvent.Safe irq) :
    PrefixPreserves MixedInv LifetimeEvent.Safe (decryptStepPrefix softirq irq) :=
  decryptStepPrefix_preserves_ambient mixedAmbient
    (fun ring => mixed_drop (mixed_lift (fun _ => True) _ (decryptQueue_identity ring))) hs hi

theorem decryptIterPrefix_preserves
    (hs : PrefixPreserves MixedInv LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves MixedInv LifetimeEvent.Safe irq)
    (hr : PrefixPreserves MixedInv LifetimeEvent.Safe needResched) :
    PrefixPreserves MixedInv LifetimeEvent.Safe (decryptIterPrefix softirq irq needResched) :=
  decryptIterPrefix_preserves_ambient mixedAmbient
    (fun ring => mixed_drop (mixed_lift (fun _ => True) _ (decryptQueue_identity ring))) hs hi hr

theorem decryptIterPrefix_pure_erases (resched : Bool) :
    ErasesPrefix (decryptIterPrefix (pure ()) (pure ()) (pure resched))
      (decryptIter (pure ()) (pure ()) (pure resched)) :=
  decryptIterPrefix_erases (erasesPrefix_pure ()) (erasesPrefix_pure ()) (erasesPrefix_pure resched)

theorem decryptIterPrefix_pure_preserves (resched : Bool) :
    PrefixPreserves MixedInv LifetimeEvent.Safe
      (decryptIterPrefix (pure ()) (pure ()) (pure resched)) :=
  decryptIterPrefix_preserves
    (PrefixPreserves.pure (fun _ _ hi => hi.safe) ())
    (PrefixPreserves.pure (fun _ _ hi => hi.safe) ())
    (PrefixPreserves.pure (fun _ _ hi => hi.safe) resched)

end Leanux.Proofs.WG.Lifetimes
