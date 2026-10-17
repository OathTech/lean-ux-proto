import Leanux.Proofs.WG.Lifetimes.Decrypt
import Leanux.Proofs.Logged.PrefixWorkers

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! The original decrypt worker's step and scheduler iteration. Callback
observations are explicit and may change identities while preserving MixedInv. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def decryptStepPrefix (softirq irq : PrefixM LifetimeEvent Unit) : PrefixM LifetimeEvent Bool := do
  softirq
  match (← liftWGObserver (liftWGPrefix getDev)).decryptQueue.consume with
  | (none, _) =>
    _ ← liftPrefix (branch .decWorkerConsumed false)
    return false
  | (some id, ring) =>
    _ ← liftPrefix (branch .decWorkerConsumed true)
    liftWGObserver (liftWGPrefix (modifyDev fun d => {d with decryptQueue := ring}))
    let decrypted ← liftWGObserver (decryptPacketPrefix (← liftWGObserver (getRxSkbPrefix id)))
    if ← liftPrefix (branch .decWorkerDecrypted decrypted.isSome) then
      let some d := decrypted | liftPrefix (invariant "unreachable")
      liftWGObserver (setRxSkbPrefix id fun _ => d)
      enqueuePerPeerRxPrefix irq id .crypted
    else enqueuePerPeerRxPrefix irq id .dead
    softirq
    return true

def decryptIterPrefix (softirq irq : PrefixM LifetimeEvent Unit) (needResched : PrefixM LifetimeEvent Bool) : PrefixM LifetimeEvent IterResult :=
  workerIterPrefix .decryptWorker none (decryptStepPrefix softirq irq)
    (do liftPrefix (branch .decWorkerNeedResched (← needResched)))

theorem decryptStepPrefix_erases (hs : ErasesPrefix softirq originalSoftirq)
    (hi : ErasesPrefix irq originalIrq) :
    ErasesPrefix (decryptStepPrefix softirq irq) (decryptStep originalSoftirq originalIrq) := by
  unfold decryptStepPrefix decryptStep
  apply erasesPrefix_bind hs
  intro _
  apply erasesPrefix_bind (liftWGObserver_erases (erasesStatePrefix_lift getDev))
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
    apply erasesPrefix_bind (liftWGObserver_erases (erasesStatePrefix_lift _))
    intro _
    apply erasesPrefix_bind (liftWGObserver_erases (getRxSkbPrefix_erases _))
    intro pkt
    apply erasesPrefix_bind (liftWGObserver_erases (decryptPacketPrefix_erases pkt))
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
      | exact liftWGObserver_erases (setRxSkbPrefix_erases _ _)
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

theorem getDev_sameWGStore : SameWGStore getDev := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient d v ambient' hp hr
  cases hd : w.dev with
  | none =>
    simp [getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some dev =>
    simp [getDev, hd] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact hp

theorem getDev_identity : SameView identityView getDev :=
  identity_sameWGStore (project := id) getDev_sameWGStore

theorem decryptQueue_identity (ring : PtrRing SkbId) :
    SameView identityView (modifyDev fun d => {d with decryptQueue := ring}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents
  simp [Option.bind_map, Function.comp_def]

theorem decryptStepPrefix_preserves_ambient (c : ProductAmbientContracts I)
    (hq : ∀ ring, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with decryptQueue := ring}))))
    (hs : PrefixPreserves I LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves I LifetimeEvent.Safe irq) :
    PrefixPreserves I LifetimeEvent.Safe (decryptStepPrefix softirq irq) := by
  unfold decryptStepPrefix
  apply PrefixPreserves.bind hs
  intro _
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) getDev getDev_sameWGStore))
  intro dev
  split
  · apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro _
    exact PrefixPreserves.pure (fun h w hi => c.safe h w hi) _
  · apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro _
    apply PrefixPreserves.bind (hq _)
    intro _
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getRx (fun _ => True) _))
    intro pkt
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (decryptPacketPrefix_spec_product c (fun _ => True) pkt))
    intro decrypted
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro yes
    dsimp only
    split
    · split
      · apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.setRx (fun _ => True) _ _))
        intro _
        apply PrefixPreserves.bind (enqueuePerPeerRxPrefix_preserves_ambient c hi _ _)
        intro _
        apply PrefixPreserves.bind hs
        intro _
        exact PrefixPreserves.pure (fun h w hi => c.safe h w hi) _
      · exact ProductAmbientContracts.drop (c.invariant (fun _ => True) _)
    · apply PrefixPreserves.bind (enqueuePerPeerRxPrefix_preserves_ambient c hi _ _)
      intro _
      apply PrefixPreserves.bind hs
      intro _
      exact PrefixPreserves.pure (fun h w hi => c.safe h w hi) _

theorem decryptIterPrefix_preserves_ambient (c : ProductAmbientContracts I)
    (hq : ∀ ring, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with decryptQueue := ring}))))
    (hs : PrefixPreserves I LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves I LifetimeEvent.Safe irq)
    (hr : PrefixPreserves I LifetimeEvent.Safe needResched) :
    PrefixPreserves I LifetimeEvent.Safe (decryptIterPrefix softirq irq needResched) := by
  apply workerIterPrefix_preserves _ _ (fun h w hi => c.safe h w hi)
    (decryptStepPrefix_preserves_ambient c hq hs hi)
  exact PrefixPreserves.bind hr (fun _ => ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))

theorem decryptStepPrefix_preserves
    (hs : PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe irq) :
    PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe (decryptStepPrefix softirq irq) :=
  decryptStepPrefix_preserves_ambient (ProductAmbientContracts.ofNative mixedAmbient)
    (fun ring => (AmbientContracts.drop (Q := fun _ _ => True) (mixed_state_lift (fun _ => True) _ (decryptQueue_identity ring))).liftWGObserver) hs hi

theorem decryptIterPrefix_preserves
    (hs : PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe softirq)
    (hi : PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe irq)
    (hr : PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe needResched) :
    PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe (decryptIterPrefix softirq irq needResched) :=
  decryptIterPrefix_preserves_ambient (ProductAmbientContracts.ofNative mixedAmbient)
    (fun ring => (AmbientContracts.drop (Q := fun _ _ => True) (mixed_state_lift (fun _ => True) _ (decryptQueue_identity ring))).liftWGObserver) hs hi hr

theorem decryptIterPrefix_pure_erases (resched : Bool) :
    ErasesPrefix (decryptIterPrefix (pure ()) (pure ()) (pure resched))
      (decryptIter (pure ()) (pure ()) (pure resched)) :=
  decryptIterPrefix_erases (erasesPrefix_pure ()) (erasesPrefix_pure ()) (erasesPrefix_pure resched)

theorem decryptIterPrefix_pure_preserves (resched : Bool) :
    PrefixPreserves (fun h w => MixedInv h w.wg) LifetimeEvent.Safe
      (decryptIterPrefix (pure ()) (pure ()) (pure resched)) :=
  decryptIterPrefix_preserves
    (PrefixPreserves.pure (fun _ _ hi => hi.safe) ())
    (PrefixPreserves.pure (fun _ _ hi => hi.safe) ())
    (PrefixPreserves.pure (fun _ _ hi => hi.safe) resched)

end Leanux.Proofs.WG.Lifetimes
