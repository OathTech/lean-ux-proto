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
  | nil => simp only [freeList_nil]; mvcgen
  | cons id rest ih =>
    rw [freeList_cons]
    mvcgen [free_packet_wp, ih]
    all_goals try dsimp +zetaDelta only at *
    all_goals intro _ he
    all_goals rw [he]
    all_goals funext j
    all_goals by_cases he : id = j <;> by_cases hm : j ∈ rest <;> simp_all [eq_comm]

theorem freeList_absent (item : List SkbId) :
    ⦃fun _ => ⌜True⌝⦄ freeList item
    ⦃⇓? _ w => ⌜∀ id ∈ item, txPackets w id = none⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' _ hr id hi
  have he := (hoare_iff_run_ambient _ _ _).mp (freeList_wp item (txPackets w)) w ambient u v ambient' rfl hr
  simpa [hi] using congrFun he id

theorem keyPut_packets (key : Option KeypairId) (now : Bool) :
    SameView txPackets (keypairPut key now) := by
  apply SameView.of_wp
  intro s
  have owner := fun o => indexOwner_peerDeref_preserves o (fun w => txPackets w = s)
  unfold Preserves Hoare at owner
  have index_spec {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => txPackets w = s)
        (fun _ w => txPackets w = s) := by
    apply hoare_liftIndex
    intro w d table hi hd
    unfold txPackets at hi ⊢
    simpa [hd] using hi
  unfold Hoare at index_spec
  mvcgen [keypairPut, owner, index_spec, getKeypair, getDev, setKeypair, modifyDev,
    refcountDecAndTest, branch, branchCmp, invariant, unsupported,
    AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant, AmbientM.unsupported]
  all_goals unfold txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem peerPut_packets (peer : Option PeerId) : SameView txPackets (peerPut peer) := by
  apply SameView.of_wp
  intro s
  have index_spec {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => txPackets w = s)
        (fun _ w => txPackets w = s) := by
    apply hoare_liftIndex
    intro w d table hi hd
    unfold txPackets at hi ⊢
    simpa [hd] using hi
  unfold Hoare at index_spec
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => txPackets w = s)
        (fun _ w => txPackets w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, peerPut, requireNotPending, index_spec, ambient,
    getPeer, getDev, setPeer, modifyDev, retirePeerUnits, modifyAmbient,
    refcountDecAndTest, branch, branchCmp, invariant, unsupported]
  all_goals unfold txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

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
  mvcgen [freeList_absent, hk, hp]

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
  unfold Hoare at skb
  mvcgen [cleanupSource, freeList_absent, hk, hp, getTxSkb, skb]


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
  unfold Hoare at skb
  mvcgen [enqueuePerDeviceAndPeer, setTxSkb, skb, getPeer, getDev,
    modifyDev, setPeer, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals unfold txQueues at *
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [wgStoreView, PeerBorrow.resident]
  all_goals subst_vars
  all_goals simp_all
  all_goals omega

/-- An actual full peer queue forces normal createData to finish direct cleanup.
This proves packet absence only: its peer put can remove an unrelated old queue. -/
theorem create_noSpace (pid : PeerId) (item : List SkbId) (q : PrevQueue (List SkbId))
    (hfull : MAX_QUEUED_PACKETS ≤ q.count) :
    ⦃fun w => ⌜∃ p, PeerBorrow.resident (wgStoreView w) pid = some p ∧
      p.isDead = false ∧ p.txQueue = q⌝⦄ createData pid item
    ⦃⇓? _ w => ⌜∀ id ∈ item, txPackets w id = none⌝⦄ := by
  rw [createSource_factor]
  have he := enqueue_full pid item q hfull
  mvcgen [createTailSource, he, cleanup_absent, getPeer, getDev, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals unfold txQueues at *
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [wgStoreView, PeerBorrow.resident, WG.EPIPE, WG.ENOSPC]

end Leanux.Proofs.WG.Queues.TxDisposition
