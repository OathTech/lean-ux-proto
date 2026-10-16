import Leanux.Proofs.WG.Lifetimes.TxContracts

set_option maxHeartbeats 500000
set_option pp.structureInstances false

/-! Complete TX enqueue callers with failure-retaining resolved-store accesses. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def cpumaskChooseOnlinePrefix (pid : PeerId) : MixedM Nat := do
  let p ← getPeerMixed pid
  let invalid ← do
    if ← liftWGPrefix (branch .chooseCpuInvalid (p.serialWorkCpu.getD 1 ≥ 1)) then pure true
    else liftWGPrefix (branch .chooseCpuOffline false)
  if !invalid then return p.serialWorkCpu.getD 0
  let cpuIndex := p.internalId % 1
  for _ in [0:cpuIndex] do _ ← liftWGPrefix (branch .chooseCpuIndexIterate true)
  _ ← liftWGPrefix (branch .chooseCpuIndexIterate false)
  setPeerMixed pid { (← getPeerMixed pid) with serialWorkCpu := some 0 }
  return 0


def enqueuePerPeerTxPrefix (item : List SkbId) (state : PacketState) : MixedM Unit := do
  let some first := item.head? | liftWGPrefix (invariant "an empty ring item")
  let pid ← peerDerefPrefix (.keypair (← getTxSkbPrefix first).keypair)
  peerGetMixed pid
  if !((← getPeerMixed pid).txQueue.all.any (·.head? == some first)) then
    liftWGPrefix (invariant "an item for the tx worker that is not on its peer's tx_queue")
  setTxSkbPrefix first fun p => { p with state }
  _ ← cpumaskChooseOnlinePrefix pid
  if !(← liftWGPrefix getDev).txWorkQueue.contains pid || (← liftWGPrefix (peekQueuedUnit .txWorker pid)) then
    liftWGPrefix (recordQueued .txWorker pid)
    liftWGPrefix (modifyDev fun d => { d with txWorkQueue := d.txWorkQueue ++ [pid] })
  peerPutMixed (some pid)


def enqueuePerDeviceAndPeerPrefix (pid : PeerId) (item : List SkbId) : MixedM Int := do
  let some first := item.head? | liftWGPrefix (invariant "an empty ring item")
  setTxSkbPrefix first fun p => { p with state := .uncrypted }
  let p ← getPeerMixed pid
  if ← liftWGPrefix (branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS)) then return -ENOSPC
  setPeerMixed pid { p with txQueue := p.txQueue.enqueue item }   -- W7: a multi-item queue
  let d ← liftWGPrefix getDev
  let cpu ← liftWGPrefix (cpumaskNextOnlineFrom d.encryptLastCpu)
  liftWGPrefix (modifyDev fun d => { d with encryptLastCpu := cpu })
  if ← liftWGPrefix (branch .enqueueRingFull d.encryptQueue.full) then return -WG.EPIPE
  liftWGPrefix (queueDeviceWork .encryptWorker)
  liftWGPrefix (modifyDev fun d => { d with encryptQueue := d.encryptQueue.produce item })
  return 0


def createDataPrefix (pid : PeerId) (item : List SkbId) : MixedM Unit := do
  let some first := item.head? | liftWGPrefix (invariant "an empty ring item")
  let ret ← do
    if ← liftWGPrefix (branch .createDataDead (← getPeerMixed pid).isDead) then pure (-EINVAL)
    else
      let ret ← enqueuePerDeviceAndPeerPrefix pid item
      if ← liftWGPrefix (branch .createDataEpipe (ret == -WG.EPIPE)) then enqueuePerPeerTxPrefix item .dead
      pure ret
  if ← liftWGPrefix (branch .createDataOk (ret == 0)) then return
  if ← liftWGPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
  keypairPutPrefix (some (← getTxSkbPrefix first).keypair) false
  peerPutMixed (some pid)
  for id in item do freeTxSkbPrefix id



theorem cpumaskChooseOnlinePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (cpumaskChooseOnlinePrefix pid) (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnlinePrefix cpumaskChooseOnline
  simp only [Nat.mod_one, Std.Legacy.Range.forIn_eq_forIn_range', show (Std.Legacy.Range.mk 0 0 1 (by decide)).size = 0 from rfl, List.range'_zero,
    List.forIn_nil, pure_bind]
  repeat' first
    | exact getPeerMixed_erases _
    | exact setPeerMixed_erases _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | split
    | (solve | simp_all)
    | (intro x; try dsimp only)

theorem enqueuePerPeerTxPrefix_erases (item : List SkbId) (state : PacketState) :
    ErasesStatePrefix (enqueuePerPeerTxPrefix item state) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTxPrefix enqueuePerPeerTx
  cases he : item.head? with
  | none => exact erasesStatePrefix_lift _
  | some first =>
    apply erasesStatePrefix_bind (getTxSkbPrefix_erases _)
    intro pkt
    apply erasesStatePrefix_bind (peerDerefPrefix_erases _)
    intro pid
    apply erasesStatePrefix_bind (peerGetMixed_erases _)
    intro _
    apply erasesStatePrefix_bind (getPeerMixed_erases _)
    intro p
    split
    · exact erasesStatePrefix_lift _
    · apply erasesStatePrefix_bind (setTxSkbPrefix_erases _ _)
      intro _
      apply erasesStatePrefix_bind (cpumaskChooseOnlinePrefix_erases _)
      intro _
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro d
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro queued
      split
      · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro _
        exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ => peerPutMixed_erases _)
      · exact peerPutMixed_erases _

theorem enqueuePerDeviceAndPeerPrefix_erases (pid : PeerId) (item : List SkbId) :
    ErasesStatePrefix (enqueuePerDeviceAndPeerPrefix pid item) (enqueuePerDeviceAndPeer pid item) := by
  unfold enqueuePerDeviceAndPeerPrefix enqueuePerDeviceAndPeer
  cases he : item.head? <;> simp only
  · exact erasesStatePrefix_lift _
  · repeat' first
      | exact getPeerMixed_erases _
      | exact setPeerMixed_erases _ _
      | exact setTxSkbPrefix_erases _ _
      | exact erasesStatePrefix_lift _
      | exact erasesStatePrefix_pure _
      | apply erasesStatePrefix_bind
      | split
      | (solve | simp_all)
      | (intro x; try dsimp only)

theorem createDataPrefix_erases (pid : PeerId) (item : List SkbId) :
    ErasesStatePrefix (createDataPrefix pid item) (createData pid item) := by
  unfold createDataPrefix createData
  cases he : item.head? with
  | none => exact erasesStatePrefix_lift _
  | some first =>
    apply erasesStatePrefix_bind (getPeerMixed_erases _)
    intro p
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro dead
    have tail (ret : Int) : ErasesStatePrefix
        (do
          if ← liftWGPrefix (branch .createDataOk (ret == 0)) then return
          if ← liftWGPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
          keypairPutPrefix (some (← getTxSkbPrefix first).keypair) false
          peerPutMixed (some pid)
          for id in item do freeTxSkbPrefix id)
        (do
          if ← branch .createDataOk (ret == 0) then return
          if ← branch .createDataOkEpipe (ret == -WG.EPIPE) then return
          keypairPut (some (← getTxSkb first).keypair) false
          peerPut (some pid)
          for id in item do freeTxSkb id) := by
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro ok
      split
      · exact erasesStatePrefix_pure _
      · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro pipe
        split
        · exact erasesStatePrefix_pure _
        · apply erasesStatePrefix_bind (getTxSkbPrefix_erases _)
          intro pkt
          apply erasesStatePrefix_bind (keypairPutPrefix_erases _ _)
          intro _
          apply erasesStatePrefix_bind (peerPutMixed_erases _)
          intro _
          apply erasesStatePrefix_bind (erasesStatePrefix_forIn _ _ _ _ (fun id _ =>
            erasesStatePrefix_bind (freeTxSkbPrefix_erases id) (fun _ => erasesStatePrefix_pure _)))
          intro _
          exact erasesStatePrefix_pure _
    split
    · simpa only [pure_bind] using tail (-EINVAL)
    · apply erasesStatePrefix_bind (enqueuePerDeviceAndPeerPrefix_erases _ _)
      intro ret
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro pipe
      split
      · simpa only [pure_bind] using erasesStatePrefix_bind (enqueuePerPeerTxPrefix_erases item .dead) (fun _ => tail ret)
      · simpa only [pure_bind] using tail ret

theorem cpumaskChooseOnlinePrefix_preserves_ambient (c : AmbientContracts I) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (cpumaskChooseOnlinePrefix pid) := by
  unfold cpumaskChooseOnlinePrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
  intro p
  have tail (invalid : Bool) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (do
        if !invalid then return p.serialWorkCpu.getD 0
        for _ in [0:p.internalId % 1] do _ ← liftWGPrefix (branch .chooseCpuIndexIterate true)
        _ ← liftWGPrefix (branch .chooseCpuIndexIterate false)
        modifyPeerKeysPrefix pid fun q => {q with serialWorkCpu := some 0}
        return 0) := by
    split
    · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    · simp only [Nat.mod_one, Std.Legacy.Range.forIn_eq_forIn_range', show (Std.Legacy.Range.mk 0 0 1 (by decide)).size = 0 from rfl, List.range'_zero,
        List.forIn_nil, pure_bind]
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro _
      exact StatePrefixEnsures.bind (AmbientContracts.drop
        (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
        (fun _ => StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro b
  split
  · simpa only [pure_bind, modifyPeerKeysPrefix, bind_assoc] using tail true
  · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro b
    simpa only [modifyPeerKeysPrefix, bind_assoc] using tail b

theorem enqueuePerPeerTxPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (item : List SkbId) (state : PacketState) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (enqueuePerPeerTxPrefix item state) := by
  unfold enqueuePerPeerTxPrefix
  cases he : item.head? with
  | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
  | some first =>
    apply StatePrefixEnsures.bind (AmbientContracts.drop (t.get (fun _ => True) _))
    intro pkt
    apply StatePrefixEnsures.bind (AmbientContracts.drop (peerDerefPrefix_spec c (fun _ => True) _))
    intro pid
    apply StatePrefixEnsures.bind (c.peerGet _)
    intro _
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    intro p
    split
    · exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    · apply StatePrefixEnsures.bind (AmbientContracts.drop (t.set (fun _ => True) _ _))
      intro _
      apply StatePrefixEnsures.bind (cpumaskChooseOnlinePrefix_preserves_ambient c _)
      intro _
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
      intro d
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.peekQueuedUnit .txWorker pid) (fun w => wgStoreView w = initial))))
      intro queued
      split
      · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.recordQueued .txWorker pid) (fun w => wgStoreView w = initial))))
        intro _
        exact StatePrefixEnsures.bind (AmbientContracts.drop (t.device (fun _ => True) (.work _))) (fun _ => c.peerPut _)
      · exact c.peerPut _

theorem enqueuePerDeviceAndPeerPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) (item : List SkbId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (enqueuePerDeviceAndPeerPrefix pid item) := by
  unfold enqueuePerDeviceAndPeerPrefix
  cases he : item.head? <;> simp only
  · exact AmbientContracts.drop (c.invariant (fun _ => True) _)
  · apply StatePrefixEnsures.bind (AmbientContracts.drop (t.set (fun _ => True) _ _))
    intro _
    have hget : StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe (getPeerMixed pid)
        (fun p h w _ => I h w ∧ (identityView w).1.slots pid = some p.internalId) :=
      (c.getPeer (fun _ => True) pid).consequence
        (fun _ _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ _ hi => ⟨hi.1, hi.2.2⟩)
    apply StatePrefixEnsures.bind hget
    intro p
    let P := fun s : IdentityView => s.1.slots pid = some p.internalId
    apply StatePrefixEnsures.bind (c.branch P _ _)
    intro full
    split
    · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi.1) (fun _ _ _ hi => hi.1)
    · apply StatePrefixEnsures.bind ((c.setPeer (fun _ => True) pid {p with txQueue := p.txQueue.enqueue item}).consequence
        (fun _ _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ _ hi => hi.1))
      intro _
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore))
      intro d
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (cpumaskNextOnlineFrom_sameStore _)))
      intro cpu
      apply StatePrefixEnsures.bind (AmbientContracts.drop (t.device (fun _ => True) (.cpu cpu)))
      intro _
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro full
      split
      · exact StatePrefixEnsures.pure (-WG.EPIPE) (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
      · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker) (fun w => wgStoreView w = initial))))
        intro _
        apply StatePrefixEnsures.bind (AmbientContracts.drop (t.device (fun _ => True) (.ring item)))
        intro _
        exact StatePrefixEnsures.pure 0 (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)

theorem createDataPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) (item : List SkbId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (createDataPrefix pid item) := by
  unfold createDataPrefix
  cases he : item.head? with
  | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
  | some first =>
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    intro p
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro dead
    have tail (ret : Int) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
        (do
          if ← liftWGPrefix (branch .createDataOk (ret == 0)) then return
          if ← liftWGPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
          keypairPutPrefix (some (← getTxSkbPrefix first).keypair) false
          peerPutMixed (some pid)
          for id in item do freeTxSkbPrefix id) := by
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro ok
      split
      · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
      · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        intro pipe
        split
        · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
        · apply StatePrefixEnsures.bind (AmbientContracts.drop (t.get (fun _ => True) _))
          intro pkt
          apply StatePrefixEnsures.bind (t.put _ _)
          intro _
          apply StatePrefixEnsures.bind (c.peerPut _)
          intro _
          apply StatePrefixEnsures.bind (StatePrefixEnsures.forInInvariant item () _
            (fun _ h w _ => I h w) LifetimeEvent.Safe (fun _ h w _ hi => c.safe h w hi) (fun id _ =>
              StatePrefixEnsures.bind (t.free id) (fun _ =>
                StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))))
          intro _
          exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    split
    · simpa only [pure_bind] using tail (-EINVAL)
    · apply StatePrefixEnsures.bind (enqueuePerDeviceAndPeerPrefix_preserves_ambient c t _ _)
      intro ret
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro pipe
      split
      · simpa only [pure_bind] using StatePrefixEnsures.bind (enqueuePerPeerTxPrefix_preserves_ambient c t item .dead) (fun _ => tail ret)
      · simpa only [pure_bind] using tail ret

theorem cpumaskChooseOnlinePrefix_preserves_product (c : ProductAmbientContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (cpumaskChooseOnlinePrefix pid)) := by
  have branch_spec (P : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (branch d b))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  have invariant_spec (P : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (invariant (α := Unit) why))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)
  simp only [cpumaskChooseOnlinePrefix, liftWGObserver_bind, liftWGObserver_pure]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
  intro p
  have tail (invalid : Bool) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (do
        if !invalid then return p.serialWorkCpu.getD 0
        for _ in [0:p.internalId % 1] do _ ← liftWGPrefix (branch .chooseCpuIndexIterate true)
        _ ← liftWGPrefix (branch .chooseCpuIndexIterate false)
        modifyPeerKeysPrefix pid fun q => {q with serialWorkCpu := some 0}
        return 0)) := by
    simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
    split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
    · exact PrefixPreserves.pure c.safe _
    · simp only [Nat.mod_one, Std.Legacy.Range.forIn_eq_forIn_range',
        show (Std.Legacy.Range.mk 0 0 1 (by decide)).size = 0 from rfl,
        List.range'_zero, List.forIn_nil, pure_bind, liftWGObserver_bind, liftWGObserver_pure]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
      intro _
      exact PrefixPreserves.bind (ProductAmbientContracts.drop
        (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
        (fun _ => PrefixPreserves.pure c.safe _)
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
  intro b
  split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
  · simpa only [pure_bind, modifyPeerKeysPrefix, bind_assoc, liftWGObserver_bind, liftWGObserver_pure] using tail true
  · apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
    intro b
    simpa only [modifyPeerKeysPrefix, bind_assoc, liftWGObserver_bind, liftWGObserver_pure] using tail b

theorem enqueuePerPeerTxPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (item : List SkbId) (state : PacketState) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (enqueuePerPeerTxPrefix item state)) := by
  have branch_spec (P : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (branch d b))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  have invariant_spec (P : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (invariant (α := Unit) why))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)
  simp only [enqueuePerPeerTxPrefix, liftWGObserver_bind, liftWGObserver_pure]
  cases he : item.head? with
  | none => exact ProductAmbientContracts.drop (invariant_spec (fun _ => True) _)
  | some first =>
    simp only [liftWGObserver_bind, liftWGObserver_pure]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (t.get (fun _ => True) _))
    intro pkt
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (ProductAmbientContracts.peerDeref c (fun _ => True) _))
    intro pid
    apply PrefixPreserves.bind (c.peerGet _)
    intro _
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    intro p
    simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
    split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
    · exact ProductAmbientContracts.drop (invariant_spec (fun _ => True) _)
    · apply PrefixPreserves.bind (ProductAmbientContracts.drop (t.set (fun _ => True) _ _))
      intro _
      apply PrefixPreserves.bind (cpumaskChooseOnlinePrefix_preserves_product c _)
      intro _
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
      intro d
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.peekQueuedUnit .txWorker pid) (fun w => wgStoreView w = initial))))
      intro queued
      simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
      split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
      · apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.recordQueued .txWorker pid) (fun w => wgStoreView w = initial))))
        intro _
        exact PrefixPreserves.bind (ProductAmbientContracts.drop (t.device (fun _ => True) (.work _))) (fun _ => c.peerPut _)
      · exact c.peerPut _

theorem enqueuePerDeviceAndPeerPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (pid : PeerId) (item : List SkbId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (enqueuePerDeviceAndPeerPrefix pid item)) := by
  have branch_spec (P : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (branch d b))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  have invariant_spec (P : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (invariant (α := Int) why))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)
  simp only [enqueuePerDeviceAndPeerPrefix, liftWGObserver_bind, liftWGObserver_pure]
  cases he : item.head? <;> simp only [liftWGObserver_bind, liftWGObserver_pure]
  · exact ProductAmbientContracts.drop (invariant_spec (fun _ => True) _)
  · apply PrefixPreserves.bind (ProductAmbientContracts.drop (t.set (fun _ => True) _ _))
    intro _
    apply PrefixEnsures.preserves
    have hget : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (getPeerMixed pid))
        (fun p h w => I h w ∧ (identityView w.wg).1.slots pid = some p.internalId) :=
      (c.getPeer (fun _ => True) pid).consequence
        (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
    apply PrefixEnsures.bind hget
    intro p
    let P := fun s : IdentityView => s.1.slots pid = some p.internalId
    apply PrefixEnsures.bind (branch_spec P _ _)
    intro full
    simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
    split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
    · exact PrefixEnsures.pure (fun h w hi => c.safe h w hi.1) (fun _ _ hi => hi.1)
    · apply PrefixEnsures.bind ((c.setPeer (fun _ => True) pid {p with txQueue := p.txQueue.enqueue item}).consequence
        (fun _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ hi => hi.1))
      intro _
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
      intro d
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (cpumaskNextOnlineFrom_sameStore _)))
      intro cpu
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (t.device (fun _ => True) (.cpu cpu)))
      intro _
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
      intro full
      simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
      split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure]
      · exact PrefixPreserves.pure c.safe (-WG.EPIPE)
      · apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.queueDeviceWork .encryptWorker) (fun w => wgStoreView w = initial))))
        intro _
        apply PrefixPreserves.bind (ProductAmbientContracts.drop (t.device (fun _ => True) (.ring item)))
        intro _
        exact PrefixPreserves.pure c.safe 0

theorem createDataPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (pid : PeerId) (item : List SkbId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (createDataPrefix pid item)) := by
  have lift_loop (xs : List SkbId) (init : PUnit)
      (f : SkbId → PUnit → MixedM (ForInStep PUnit)) :
      liftWGObserver (forIn xs init f) = forIn xs init (fun x b => liftWGObserver (f x b)) := by
    induction xs generalizing init with
    | nil => simp only [List.forIn_nil, liftWGObserver_pure]
    | cons x xs ih =>
      simp only [List.forIn_cons, liftWGObserver_bind]
      congr 1
      funext step
      cases step with
      | done b => exact liftWGObserver_pure b
      | yield b => exact ih b
  have branch_spec (P : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (branch d b))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  have invariant_spec (P : IdentityView → Prop) (why : String) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (invariant (α := Unit) why))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.invariant why) (fun w => wgStoreView w = initial)
  simp only [createDataPrefix, liftWGObserver_bind, liftWGObserver_pure]
  cases he : item.head? with
  | none => exact ProductAmbientContracts.drop (invariant_spec (fun _ => True) _)
  | some first =>
    simp only [liftWGObserver_bind, liftWGObserver_pure]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    intro p
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
    intro dead
    have tail (ret : Int) : PrefixPreserves I LifetimeEvent.Safe
        (liftWGObserver (do
          if ← liftWGPrefix (branch .createDataOk (ret == 0)) then return
          if ← liftWGPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
          keypairPutPrefix (some (← getTxSkbPrefix first).keypair) false
          peerPutMixed (some pid)
          for id in item do freeTxSkbPrefix id)) := by
      simp only [liftWGObserver_bind, liftWGObserver_pure, lift_loop]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
      intro ok
      simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
      split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure, lift_loop]
      · exact PrefixPreserves.pure c.safe _
      · apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
        intro pipe
        simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
        split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure, lift_loop]
        · exact PrefixPreserves.pure c.safe _
        · apply PrefixPreserves.bind (ProductAmbientContracts.drop (t.get (fun _ => True) _))
          intro pkt
          apply PrefixPreserves.bind (t.put _ _)
          intro _
          apply PrefixPreserves.bind (c.peerPut _)
          intro _
          apply PrefixPreserves.bind (PrefixPreserves.forIn _ _ _ c.safe (fun id _ =>
            PrefixPreserves.bind (t.free id) (fun _ => PrefixPreserves.pure c.safe _)))
          intro _
          exact PrefixPreserves.pure c.safe _
    simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
    split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure, lift_loop]
    · simpa only [pure_bind, liftWGObserver_bind, liftWGObserver_pure, lift_loop, apply_ite] using tail (-EINVAL)
    · apply PrefixPreserves.bind (enqueuePerDeviceAndPeerPrefix_preserves_product c t _ _)
      intro ret
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
      intro pipe
      simp only [liftWGObserver_bind, liftWGObserver_pure, apply_ite]
      split <;> try simp only [liftWGObserver_bind, liftWGObserver_pure, lift_loop]
      · simpa only [pure_bind, liftWGObserver_bind, liftWGObserver_pure, lift_loop, apply_ite] using PrefixPreserves.bind (enqueuePerPeerTxPrefix_preserves_product c t item .dead) (fun _ => tail ret)
      · simpa only [pure_bind, liftWGObserver_bind, liftWGObserver_pure, lift_loop, apply_ite] using tail ret


end Leanux.Proofs.WG.Lifetimes
