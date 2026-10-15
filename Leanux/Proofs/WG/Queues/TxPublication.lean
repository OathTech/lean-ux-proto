import Leanux.Proofs.WG.Queues.TxDispositionCuts

/-! The actual TX publication borrow spans CPU selection and queue-work records.
The endpoint retains every peer's full TX queue, even when the publication peer
differs from the caller's enqueue peer. This is normal-return partial correctness;
record failures after publication retain the existing observer prefix. -/
set_option maxHeartbeats 1500000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def txQueues (w : World) : PeerId → Option (PrevQueue (List SkbId)) :=
  fun pid => (PeerBorrow.resident w.k pid).map (·.txQueue)

def borrowView (pid : PeerId) (w : World) :=
  (txQueues w, (PeerBorrow.resident w.k pid).map (·.refcount))

theorem borrow_kernel (pid : PeerId) (ha : SameKernel a) : SameView (borrowView pid) a := by
  intro w x v hr
  unfold borrowView txQueues
  rw [ha w x v hr]

theorem borrow_modify (pid : PeerId) (f : Device → Device)
    (h : ∀ d, (f d).peers = d.peers) : SameView (borrowView pid) (modifyDev f) := by
  intro w x v hr
  cases hr
  unfold borrowView txQueues
  simp [PeerBorrow.resident, Option.map_map,
    Option.bind_map, Function.comp_def, h]

theorem cpu_borrow (pid : PeerId) : SameView (borrowView pid) (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [cpumaskChooseOnline, getPeer, getDev, getK, setPeer, modifyDev, modifyK, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜borrowView pid w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try unfold borrowView at *
  all_goals unfold txQueues at *
  all_goals dsimp +zetaDelta only [PeerBorrow.resident] at *
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
      (PeerBorrow.resident w.k pid).map (·.refcount) = some n⌝⦄ := by
  mvcgen [peerGet, requireNotPending, getPeer, getDev, getK, setPeer, modifyDev,
    modifyK, refcountInc, branchCmp, branchCmpExcluded, branch, invariant, unsupported]
  all_goals try unfold borrowView at *
  all_goals unfold txQueues at *
  all_goals dsimp +zetaDelta only [PeerBorrow.resident] at *
  all_goals simp_all [txQueues, PeerBorrow.resident, Std.TreeMap.getElem?_insert]
  all_goals subst_vars
  all_goals try simp_all [Std.TreeMap.getElem?_insert]
  all_goals try subst q
  all_goals try omega
  all_goals try { constructor <;> first | omega | (funext j; by_cases hj : pid = j <;> simp_all) }

theorem nonfinal_put_queues (pid : PeerId) (q : PeerId → Option (PrevQueue (List SkbId))) :
    ⦃fun w => ⌜txQueues w = q ∧ ∃ n, 1 < n ∧
      (PeerBorrow.resident w.k pid).map (·.refcount) = some n⌝⦄ peerPut (some pid)
    ⦃⇓? _ w => ⌜txQueues w = q⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w u v hb hr
  obtain ⟨hq, n, hn, href⟩ := hb
  cases hd : w.k.wg with
  | none => simp [PeerBorrow.resident, hd] at href
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [PeerBorrow.resident, hd, hp] at href
    | some p =>
      have hc : 1 < p.refcount := by
        have he : p.refcount = n := by simpa [PeerBorrow.resident, hd, hp] using href
        omega
      have hs : ⦃fun z => ⌜z.k = w.k⌝⦄ peerPut (some pid)
          ⦃⇓? _ z => ⌜txQueues z = txQueues w⌝⦄ := by
        clear hq
        have hg := PeerBorrow.getPeer_known w.k d pid p hd hp
        simp only [peerPut]
        mvcgen [requireNotPending, hg, setPeer, modifyDev, modifyK,
          refcountDecAndTest, branchCmp, branchCmpExcluded, branch, invariant, unsupported]
        all_goals unfold txQueues at *
        all_goals dsimp +zetaDelta only at *
        all_goals simp_all [PeerBorrow.resident, Std.TreeMap.getElem?_insert]
        all_goals first
          | omega
          | (funext j; by_cases hj : pid = j <;> simp_all)
      exact ((hoare_iff_triple _ _ _).mpr hs w u v rfl hr).trans hq

def publicationMiddle (pid : PeerId) (first : SkbId) (state : PacketState) : M Unit := do
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
  have hp := (borrow_kernel pid (peekQueuedUnit_sameKernel .txWorker pid)).wp (fun t => t = s)
  have hr := (borrow_kernel pid (Lifetimes.recordQueued_sameKernel .txWorker pid)).wp (fun t => t = s)
  mvcgen [publicationMiddle, hc, hp, hr, getPeer, getTxSkb, setTxSkb,
    getDev, getK, modifyDev, modifyK, invariant]
  all_goals try unfold borrowView at *
  all_goals unfold txQueues at *
  all_goals dsimp +zetaDelta only [PeerBorrow.resident] at *
  all_goals simp_all [borrowView, txQueues, PeerBorrow.resident, Option.map_map,
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
  mvcgen [IndexOwner.peerDeref, IndexOwner.peerWord, unsupported, strict_acquire_queues, nonfinal_put_queues, mid, getKeypair, getTxSkb,
    getDev, getK, invariant]
  all_goals try unfold borrowView at *
  all_goals unfold txQueues at *
  all_goals dsimp +zetaDelta only [PeerBorrow.resident] at *
  all_goals simp_all [borrowView, txQueues, PeerBorrow.resident]

end Leanux.Proofs.WG.Queues.TxDisposition
