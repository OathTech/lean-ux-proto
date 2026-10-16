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
  simp [PeerBorrow.resident, wgStoreView, Option.map_map,
    Option.bind_map, Function.comp_def, h]

theorem cpu_borrow (pid : PeerId) : SameView (borrowView pid) (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [cpumaskChooseOnline, getPeer, getDev, setPeer, modifyDev, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜borrowView pid w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try unfold borrowView at *
  all_goals unfold txQueues at *
  all_goals dsimp +zetaDelta only [PeerBorrow.resident, wgStoreView] at *
  all_goals simp_all [borrowView, txQueues, PeerBorrow.resident, Std.TreeMap.getElem?_insert]
  all_goals subst_vars
  all_goals try simp_all [Std.TreeMap.getElem?_insert]
  all_goals try { subst s }
  all_goals try { apply Prod.ext <;> simp_all }
  all_goals simp_all only [funext_iff]
  all_goals intro j
  all_goals by_cases hj : pid = j <;> simp_all
  all_goals rename_i h
  all_goals have he := h.1 j
  all_goals simpa [*] using he

theorem strict_acquire_queues (pid : PeerId) (q : PeerId → Option (PrevQueue (List SkbId))) :
    ⦃fun w => ⌜txQueues w = q⌝⦄ peerGet pid
    ⦃⇓? _ w => ⌜txQueues w = q ∧ ∃ n, 1 < n ∧
      (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount) = some n⌝⦄ := by
  mvcgen [peerGet, requireNotPending, getPeer, getDev, setPeer, modifyDev,
    refcountInc, branchCmp, branchCmpExcluded, branch, invariant, unsupported, AmbientM.branchCmp, AmbientM.branchCmpExcluded, AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]
  all_goals try unfold borrowView at *
  all_goals unfold txQueues at *
  all_goals dsimp +zetaDelta only [PeerBorrow.resident, wgStoreView] at *
  all_goals simp_all [txQueues, PeerBorrow.resident, Std.TreeMap.getElem?_insert]
  all_goals subst_vars
  all_goals try simp_all [Std.TreeMap.getElem?_insert]
  all_goals try subst q
  all_goals try omega
  all_goals try { constructor <;> first | omega | (funext j; by_cases hj : pid = j <;> simp_all) }

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
      have hs : ⦃fun z => ⌜wgStoreView z = (wgStoreView w)⌝⦄ peerPut (some pid)
          ⦃⇓? _ z => ⌜txQueues z = txQueues w⌝⦄ := by
        clear hq
        have hg := PeerBorrow.getPeer_known (wgStoreView w) d pid p hd hp
        simp only [peerPut]
        mvcgen [requireNotPending, hg, setPeer, modifyDev,
          refcountDecAndTest, branchCmp, branchCmpExcluded, branch, invariant, unsupported, AmbientM.branchCmp, AmbientM.branchCmpExcluded, AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]
        all_goals unfold txQueues at *
        all_goals dsimp +zetaDelta only at *
        all_goals simp_all [PeerBorrow.resident, wgStoreView, Std.TreeMap.getElem?_insert]
        all_goals first
          | omega
          | (funext j; by_cases hj : pid = j <;> simp_all)
      exact ((hoare_iff_run_ambient _ _ _).mp hs w ambient u v ambient' rfl hr).trans hq

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
  apply SameView.of_wp
  intro s
  have hc := (cpu_borrow pid).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => borrowView pid w = s) (fun _ w => borrowView pid w = s) :=
    hoare_liftAmbient a _
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => borrowView pid w = s)
        (fun _ w => borrowView pid w = s) := by
    apply hoare_liftSkb
    intro w d store hi hd
    unfold borrowView txQueues at hi ⊢
    simpa [PeerBorrow.resident, wgStoreView, hd] using hi
  unfold Hoare at ambient skb
  mvcgen [-Std.Do.Spec.monadLift_StateT, publicationMiddle, hc, ambient, skb, getPeer, setTxSkb,
    getDev, modifyDev, invariant, peekQueuedUnit, recordQueued]
  all_goals try unfold borrowView at *
  all_goals unfold txQueues at *
  all_goals dsimp +zetaDelta only [PeerBorrow.resident, wgStoreView] at *
  all_goals simp_all [borrowView, txQueues, PeerBorrow.resident, wgStoreView, Option.map_map,
    Option.bind_map, Function.comp_def]

theorem publication_factor (item : List SkbId) (state : PacketState) :
    enqueuePerPeerTx item state = (do
      let some first := item.head? | invariant "an empty ring item"
      let pid ← IndexOwner.peerDeref (.keypair (← getTxSkb first).keypair)
      peerGet pid
      publicationMiddle pid first state
      peerPut (some pid)) := by
  simp only [enqueuePerPeerTx, publicationMiddle, bind_assoc, bind_ite, pure_bind, bind_pure_unit]
  rfl

theorem publication_queues (item : List SkbId) (state : PacketState) :
    SameView txQueues (enqueuePerPeerTx item state) := by
  apply SameView.of_wp
  intro q
  rw [publication_factor]
  have mid := fun pid first => (publicationMiddle_frame pid first state).wp
    (fun t => t.1 = q ∧ ∃ n, 1 < n ∧ t.2 = some n)
  have owner := fun o => indexOwner_peerDeref_preserves o (fun w => txQueues w = q)
  unfold Preserves Hoare at owner
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => txQueues w = q) (fun _ w => txQueues w = q) := by
    apply hoare_liftSkb
    intro w d store hi hd
    unfold txQueues at hi ⊢
    simpa [PeerBorrow.resident, wgStoreView, hd] using hi
  unfold Hoare at skb
  mvcgen [owner, strict_acquire_queues, nonfinal_put_queues, mid, getTxSkb, skb,
    getDev, invariant, AmbientM.invariant]
  all_goals try unfold borrowView at *
  all_goals unfold txQueues at *
  all_goals dsimp +zetaDelta only [PeerBorrow.resident, wgStoreView] at *
  all_goals simp_all [borrowView, txQueues, PeerBorrow.resident, wgStoreView]

end Leanux.Proofs.WG.Queues.TxDisposition
