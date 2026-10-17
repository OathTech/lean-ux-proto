import Leanux.Proofs.WG.Queues.TxDispositionCuts

/-! The actual TX publication borrow spans CPU selection and queue-work records.
The endpoint retains every peer's full TX queue, even when the publication peer
differs from the caller's enqueue peer. This is normal-return partial correctness;
record failures after publication retain the existing observer prefix. -/
set_option maxHeartbeats 1500000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def txQueues (w : WGWorld) : PeerId → Option (PrevQueue (List SkbId)) :=
  fun pid => (PeerBorrow.resident (wgStoreView w) pid).map (·.txQueue)

def borrowView (pid : PeerId) (w : WGWorld) :=
  (txQueues w, (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount))

theorem borrow_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (pid : PeerId) (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => borrowView pid (project w)) a :=
  ha.of_factor (fun store : WGStoreView =>
      ((fun j => (PeerBorrow.resident store j).map (·.txQueue)),
        (PeerBorrow.resident store pid).map (·.refcount)))
    (fun w => borrowView pid (project w)) (fun _ => rfl)

theorem borrow_modify (pid : PeerId) (f : Device → Device)
    (h : ∀ d, (f d).peers = d.peers) : SameView (borrowView pid) (modifyDev f) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  unfold borrowView txQueues
  simp [PeerBorrow.resident, wgStoreView,
    Option.bind_map, Function.comp_def, h]

theorem cpu_borrow (pid : PeerId) : SameView (borrowView pid) (cpumaskChooseOnline pid) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  cases hd : w.dev with
  | none =>
    simp [cpumaskChooseOnline, getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [cpumaskChooseOnline, getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      by_cases invalid : 1 ≤ p.serialWorkCpu.getD 1 <;>
        simp [cpumaskChooseOnline, getPeer, getDev, setPeer, modifyDev, hd, hp,
          branch, AmbientM.branch, invalid, Nat.mod_one, List.foldlM] at hr
      all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      all_goals first
        | exact hi
        | (rw [← hi]
           clear hi
           apply Prod.ext
           · funext id
             by_cases he : pid = id <;>
               simp_all [borrowView, txQueues, PeerBorrow.resident, wgStoreView,
                 Std.TreeMap.getElem?_insert]
           · simp [borrowView, PeerBorrow.resident, wgStoreView, hd, hp])

theorem strict_acquire_queues (pid : PeerId) (q : PeerId → Option (PrevQueue (List SkbId))) :
    ⦃fun w => ⌜txQueues w = q⌝⦄ peerGet pid
    ⦃⇓? _ w => ⌜txQueues w = q ∧ ∃ n, 1 < n ∧
      (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount) = some n⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have hb := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.strict_acquire_spec pid (wgStoreView w)) w ambient result v ambient' rfl hr
  obtain ⟨d, p, hd, hp, positive, current⟩ := hb
  refine ⟨?_, p.refcount + 1, by omega, ?_⟩
  · rw [← hi]
    funext id
    simp only [txQueues, current, PeerBorrow.resident, hd, Option.bind_some]
    by_cases he : pid = id <;> simp_all [Std.TreeMap.getElem?_insert]
  · simp [current, PeerBorrow.resident]

theorem nonfinal_put_queues (pid : PeerId) (q : PeerId → Option (PrevQueue (List SkbId))) :
    ⦃fun w => ⌜txQueues w = q ∧ ∃ n, 1 < n ∧
      (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount) = some n⌝⦄ peerPut (some pid)
    ⦃⇓? _ w => ⌜txQueues w = q⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hb hr
  obtain ⟨hq, n, hn, href⟩ := hb
  cases hd : w.dev with
  | none => simp [PeerBorrow.resident, wgStoreView, hd] at href
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [PeerBorrow.resident, wgStoreView, hd, hp] at href
    | some p =>
      have hc : 1 < p.refcount := by
        have he : p.refcount = n := by simpa [PeerBorrow.resident, wgStoreView, hd, hp] using href
        omega
      have pos : 0 < p.refcount := by omega
      have nz : p.refcount ≠ 0 := by omega
      have notone : p.refcount ≠ 1 := by omega
      simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev, hd, hp,
        refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
        pos, nz, notone] at hr
      rcases hr with ⟨rfl, rfl⟩
      rw [← hq]
      funext id
      by_cases he : pid = id <;>
        simp_all [txQueues, PeerBorrow.resident, wgStoreView,
          Std.TreeMap.getElem?_insert]

def publicationMiddle (pid : PeerId) (first : SkbId) (state : PacketState) : WG.M Unit := do
  if !((← getPeer pid).txQueue.all.any (·.head? == some first)) then
    invariant "an item for the tx worker that is not on its peer's tx_queue"
  setTxSkb first fun p => {p with state}
  _ ← cpumaskChooseOnline pid
  if !(← getDev).txWorkQueue.contains pid || (← peekQueuedUnit .txWorker pid) then
    recordQueued .txWorker pid
    modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}

theorem publicationMiddle_frame (pid : PeerId) (first : SkbId) (state : PacketState) :
    SameView (borrowView pid) (publicationMiddle pid first state) := by
  intro s
  let P := fun w : WGWorld => borrowView pid w = s
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have skb {α : Type} (a : SkbM α) :
      Preserves P (liftSkb a) := by
    apply hoare_liftSkb
    intro w d store hi hd
    change borrowView pid _ = s at hi ⊢
    unfold borrowView txQueues at hi ⊢
    simpa [PeerBorrow.resident, wgStoreView, hd] using hi
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have write (f : Device → Device) (hf : ∀ d, (f d).peers = d.peers) :
      Preserves P (modifyDev f) := (borrow_modify pid f hf).wp (fun t => t = s)
  change Preserves P (publicationMiddle pid first state)
  unfold publicationMiddle getPeer getDev setTxSkb
  simp only [invariant, peekQueuedUnit, recordQueued]
  repeat' first
    | (allocation_release_head cpumaskChooseOnline; exact (cpu_borrow pid).wp (fun t => t = s))
    | (allocation_release_head modifyDev; apply write; intro; rfl)
    | (allocation_release_head liftSkb; exact skb _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step
  all_goals exact read

theorem publication_factor (item : List SkbId) (state : PacketState) :
    enqueuePerPeerTx item state = (do
      let some first := item.head? | invariant "an empty ring item"
      let pid ← IndexOwner.peerDeref (.keypair (← getTxSkb first).keypair)
      peerGet pid
      publicationMiddle pid first state
      peerPut (some pid)) := by
  simp only [enqueuePerPeerTx, publicationMiddle, bind_assoc, bind_ite, pure_bind]
  rfl

theorem publication_queues (item : List SkbId) (state : PacketState) :
    SameView txQueues (enqueuePerPeerTx item state) := by
  intro q
  rw [publication_factor]
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w => txQueues w = q) (monadLift a : WG.M α) := hoare_liftAmbient a _
  have skb {α : Type} (a : SkbM α) :
      Preserves (fun w => txQueues w = q) (liftSkb a) := by
    apply hoare_liftSkb
    intro w d store hi hd
    unfold txQueues at hi ⊢
    simpa [PeerBorrow.resident, wgStoreView, hd] using hi
  cases item.head? with
  | none => exact ambient (AmbientM.invariant _)
  | some first =>
    apply hoare_bind _ _ (skb _)
    intro packet
    apply hoare_bind _ _ (indexOwner_peerDeref_preserves _ (fun w => txQueues w = q))
    intro pid
    apply hoare_bind _ _ (strict_acquire_queues pid q)
    intro _
    apply hoare_bind _ _ ((publicationMiddle_frame pid first state).wp
      (fun t => t.1 = q ∧ ∃ n, 1 < n ∧ t.2 = some n))
    intro _
    exact nonfinal_put_queues pid q

end Leanux.Proofs.WG.Queues.TxDisposition
