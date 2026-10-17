import Leanux.Proofs.WG.Queues.TxPublication

/-! Normal list disposal removes the actual packet records, without an
allocation invariant or a distinct-ID premise. A duplicate may instead Stop at
its second getter; exact reached release prefixes remain in TxDisposition.free_run.
No peer-queue preservation follows from cleanup's unrelated final peer put. -/
set_option maxHeartbeats 1500000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def txPackets (w : WGWorld) (id : SkbId) : Option DataPacket :=
  w.dev.bind fun d => d.txSkbs[id]?

def freeList (item : List SkbId) : WG.M Unit := do
  for id in item do freeTxSkb id

theorem freeList_nil : freeList [] = pure () := rfl

theorem freeList_cons (id : SkbId) (rest : List SkbId) :
    freeList (id :: rest) = (do freeTxSkb id; freeList rest) := by
  simp [freeList]

theorem free_packet_wp (id : SkbId) (before : SkbId → Option DataPacket) :
    ⦃fun w => ⌜txPackets w = before⌝⦄ freeTxSkb id
    ⦃⇓? _ w => ⌜txPackets w = fun j => if id = j then none else before j⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hb hr
  cases u
  cases hd : w.dev with
  | none => simp [freeTxSkb, liftSkb_run, hd] at hr
  | some d =>
    cases hp : d.txSkbs[id]? with
    | none =>
      simp [freeTxSkb, liftSkb_run, SkbStore.freeTx, SkbStore.getTx,
        hd, hp, invariant, AmbientM.invariant] at hr
      cases hr
    | some p =>
      rw [Packets.freeTxSkb_run w ambient d id p hd hp] at hr
      cases hr
      subst before
      funext j
      simp [txPackets, Packets.update, hd,
        Std.TreeMap.getElem?_erase]


theorem freeList_wp (item : List SkbId) (before : SkbId → Option DataPacket) :
    ⦃fun w => ⌜txPackets w = before⌝⦄ freeList item
    ⦃⇓? _ w => ⌜txPackets w = fun j => if j ∈ item then none else before j⌝⦄ := by
  induction item generalizing before with
  | nil =>
    rw [freeList_nil]
    apply hoare_consequence (hoare_pure () (fun w => txPackets w = before))
    · exact fun _ h => h
    · intro x w h
      simpa using h.2
  | cons id rest ih =>
    rw [freeList_cons]
    apply hoare_bind _ _ (free_packet_wp id before)
    intro _
    apply hoare_consequence (ih (fun j => if id = j then none else before j))
    · exact fun _ h => h
    · intro x w h
      rw [h]
      funext j
      by_cases he : id = j <;> by_cases hm : j ∈ rest <;> simp_all [eq_comm]

theorem freeList_absent (item : List SkbId) :
    ⦃fun _ => ⌜True⌝⦄ freeList item
    ⦃⇓? _ w => ⌜∀ id ∈ item, txPackets w id = none⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' _ hr id hi
  have he := (hoare_iff_run_ambient _ _ _).mp (freeList_wp item (txPackets w)) w ambient u v ambient' rfl hr
  simpa [hi] using congrFun he id

theorem keyPut_packets (key : Option KeypairId) (now : Bool) :
    SameView txPackets (keypairPut key now) := by
  intro initial
  let P := fun w : WGWorld => txPackets w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have index {α : Type} (a : IndexM α) :
      Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftIndex a
    intro w d table h hd
    change txPackets _ = initial
    funext id
    have point := congrFun h id
    simpa [txPackets, hd] using point
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have write (f : Device → Device) (hf : ∀ d, (f d).txSkbs = d.txSkbs) :
      Preserves P (modifyDev f) := by
    unfold modifyDev
    apply hoare_modify
    intro w h
    change txPackets _ = initial
    funext id
    have point := congrFun h id
    simpa [txPackets, Option.bind_map, Function.comp_def, hf] using point
  change Preserves P (keypairPut key now)
  unfold keypairPut getKeypair getDev setKeypair
  simp only [branch, branchCmp, refcountDecAndTest, invariant, unsupported]
  repeat' first
    | (allocation_release_head IndexOwner.peerDeref
       exact indexOwner_peerDeref_preserves _ P)
    | (allocation_release_head modifyDev; apply write; intro; rfl)
    | (allocation_release_lift_from IndexM; exact index _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step
  all_goals first
    | exact read
    | (apply hoare_modify; intro w h; exact h)

theorem peerPut_packets (peer : Option PeerId) : SameView txPackets (peerPut peer) := by
  intro initial
  let P := fun w : WGWorld => txPackets w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have index {α : Type} (a : IndexM α) :
      Preserves P (monadLift a : WG.M α) := by
    apply hoare_liftIndex a
    intro w d table h hd
    change txPackets _ = initial
    funext id
    have point := congrFun h id
    simpa [txPackets, hd] using point
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have write (f : Device → Device) (hf : ∀ d, (f d).txSkbs = d.txSkbs) :
      Preserves P (modifyDev f) := by
    unfold modifyDev
    apply hoare_modify
    intro w h
    change txPackets _ = initial
    funext id
    have point := congrFun h id
    simpa [txPackets, Option.bind_map, Function.comp_def, hf] using point
  change Preserves P (peerPut peer)
  unfold peerPut getPeer getDev setPeer
  simp only [branch, branchCmp, refcountDecAndTest, invariant, unsupported, requireNotPending, retirePeerUnits, modifyAmbient]
  repeat' first
    | (allocation_release_head modifyDev; apply write; intro; rfl)
    | (allocation_release_lift_from IndexM; exact index _)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step
  all_goals first
    | exact read
    | (apply hoare_modify; intro w h; exact h)

theorem dispose_packets (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    ⦃fun _ => ⌜True⌝⦄ disposeSource pid item key
    ⦃⇓? result w => ⌜result = true ∧ ∀ id ∈ item, txPackets w id = none⌝⦄ := by
  have he : disposeSource pid item key = (do
      freeList item
      keypairPut (some key) false
      peerPut (some pid)
      pure true) := by simp [disposeSource, freeList]
  rw [he]
  have hk := (keyPut_packets (some key) false).wp (fun s => ∀ id ∈ item, s id = none)
  have hp := (peerPut_packets (some pid)).wp (fun s => ∀ id ∈ item, s id = none)
  apply hoare_bind _ _ (freeList_absent item)
  intro _
  apply hoare_bind _ _ hk
  intro _
  apply hoare_bind _ _ hp
  intro _
  exact hoare_pure true _

def cleanupSource (pid : PeerId) (item : List SkbId) (first : SkbId) : WG.M Unit := do
  keypairPut (some (← getTxSkb first).keypair) false
  peerPut (some pid)
  freeList item

theorem cleanup_absent (pid : PeerId) (item : List SkbId) (first : SkbId) :
    ⦃fun _ => ⌜True⌝⦄ cleanupSource pid item first
    ⦃⇓? _ w => ⌜∀ id ∈ item, txPackets w id = none⌝⦄ := by
  have hk := fun key => (keyPut_packets (some key) false).wp (fun _ => True)
  have hp := (peerPut_packets (some pid)).wp (fun _ => True)
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun _ => True) (fun _ _ => True) :=
    hoare_liftSkb a _ (fun _ _ _ _ _ => trivial)
  unfold cleanupSource
  apply hoare_bind _ _ (skb (SkbStore.getTx first))
  intro packet
  apply hoare_bind _ _ (hk packet.keypair)
  intro _
  exact hoare_bind _ _ hp (fun _ => freeList_absent item)


def createTailSource (pid : PeerId) (item : List SkbId) (first : SkbId) (ret : Int) : WG.M Unit := do
  if ← branch .createDataOk (ret == 0) then return
  if ← branch .createDataOkEpipe (ret == -WG.EPIPE) then return
  cleanupSource pid item first

theorem createSource_factor (pid : PeerId) (item : List SkbId) : createData pid item = (do
    let some first := item.head? | invariant "an empty ring item"
    let ret ← do
      if ← branch .createDataDead (← getPeer pid).isDead then pure (-EINVAL)
      else
        let ret ← enqueuePerDeviceAndPeer pid item
        if ← branch .createDataEpipe (ret == -WG.EPIPE) then enqueuePerPeerTx item .dead
        pure ret
    createTailSource pid item first ret) := by
  simp only [createData, createTailSource, cleanupSource, freeList]
  rfl

theorem enqueue_full (pid : PeerId) (item : List SkbId) (q : PrevQueue (List SkbId))
    (hfull : MAX_QUEUED_PACKETS ≤ q.count) :
    ⦃fun w => ⌜txQueues w pid = some q⌝⦄ enqueuePerDeviceAndPeer pid item
    ⦃⇓? ret _ => ⌜ret = -WG.ENOSPC⌝⦄ := by
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => txQueues w pid = some q)
        (fun _ w => txQueues w pid = some q) := by
    apply hoare_liftSkb
    intro w d store hi hd
    unfold txQueues at hi ⊢
    simpa [PeerBorrow.resident, wgStoreView, hd] using hi
  let P := fun w : WGWorld => txQueues w pid = some q
  have getter : Hoare (getPeer pid) P (fun p w => p.txQueue = q ∧ P w) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hi hr
    cases hd : w.dev with
    | none =>
      simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
        cases hr
      | some peer =>
        simp [getPeer, getDev, hd, hp] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        exact ⟨by simpa [P, txQueues, PeerBorrow.resident, wgStoreView, hd, hp] using hi, hi⟩
  unfold enqueuePerDeviceAndPeer
  cases item.head? with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' _ hr
    cases hr
  | some first =>
    apply hoare_bind _ _ (skb (SkbStore.setTx first (fun p => {p with state := .uncrypted})))
    intro _
    apply hoare_bind _ _ getter
    intro p
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' ⟨hqueue, hi⟩ hr
    have full : decide (p.txQueue.count ≥ MAX_QUEUED_PACKETS) = true := by simpa [hqueue] using hfull
    simp [branch, AmbientM.branch, full] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl

/-- An actual full peer queue forces normal createData to finish direct cleanup.
This proves packet absence only: its peer put can remove an unrelated old queue. -/
theorem create_noSpace (pid : PeerId) (item : List SkbId) (q : PrevQueue (List SkbId))
    (hfull : MAX_QUEUED_PACKETS ≤ q.count) :
    ⦃fun w => ⌜∃ p, PeerBorrow.resident (wgStoreView w) pid = some p ∧
      p.isDead = false ∧ p.txQueue = q⌝⦄ createData pid item
    ⦃⇓? _ w => ⌜∀ id ∈ item, txPackets w id = none⌝⦄ := by
  have getter : Hoare (getPeer pid)
      (fun w => ∃ p, PeerBorrow.resident (wgStoreView w) pid = some p ∧
        p.isDead = false ∧ p.txQueue = q)
      (fun p w => p.isDead = false ∧ txQueues w pid = some q) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' hi hr
    cases hd : w.dev with
    | none =>
      simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
        cases hr
      | some peer =>
        simp [getPeer, getDev, hd, hp] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        obtain ⟨old, hold, alive, queue⟩ := hi
        have he : old = peer := by
          simpa [PeerBorrow.resident, wgStoreView, hd, hp] using hold.symm
        subst old
        exact ⟨alive, by simp [txQueues, PeerBorrow.resident, wgStoreView, hd, hp, queue]⟩
  have branchRule {α : Type} (decision : Decision) (value : Bool)
      (P : WGWorld → Prop) (Q : α → WGWorld → Prop) (f : Bool → WG.M α)
      (hf : Hoare (f value) P Q) :
      Hoare ((branch decision value : WG.M Bool) >>= f) P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hi hr
    change ((f value).run w).run _ = .ok ((x, v), ambient') at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
  rw [createSource_factor]
  cases item.head? with
  | none =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' _ hr
    cases hr
  | some first =>
    apply hoare_bind _ _ getter
    intro peer
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' ⟨alive, queue⟩ hr
    simp only [alive] at hr
    apply (hoare_iff_run_ambient _ (fun w => txQueues w pid = some q) _).mp ?_
      w ambient x v ambient' queue hr
    apply branchRule .createDataDead false
    simp only [Bool.false_eq_true, ↓reduceIte]
    apply hoare_bind _ _ (enqueue_full pid item q hfull)
    intro result
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hresult hr
    subst result
    simp [createTailSource, branch, AmbientM.branch, WG.EPIPE, WG.ENOSPC] at hr
    exact (hoare_iff_run_ambient _ _ _).mp (cleanup_absent pid item first)
      _ _ _ _ _ trivial hr

end Leanux.Proofs.WG.Queues.TxDisposition
