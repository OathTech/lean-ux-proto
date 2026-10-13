import Leanux.Proofs.WG.Lifetimes.TxContracts

set_option maxHeartbeats 500000
set_option pp.structureInstances false

/-! Complete TX enqueue callers with failure-retaining resolved-store accesses. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def cpumaskChooseOnlinePrefix (pid : PeerId) : MixedM Nat := do
  let p ← getPeerMixed pid
  let invalid ← do
    if ← liftPrefix (branch .chooseCpuInvalid (p.serialWorkCpu.getD 1 ≥ 1)) then pure true
    else liftPrefix (branch .chooseCpuOffline false)
  if !invalid then return p.serialWorkCpu.getD 0
  let cpuIndex := p.internalId % 1
  for _ in [0:cpuIndex] do _ ← liftPrefix (branch .chooseCpuIndexIterate true)
  _ ← liftPrefix (branch .chooseCpuIndexIterate false)
  setPeerMixed pid { (← getPeerMixed pid) with serialWorkCpu := some 0 }
  return 0


def enqueuePerPeerTxPrefix (item : List SkbId) (state : PacketState) : MixedM Unit := do
  let some first := item.head? | liftPrefix (invariant "an empty ring item")
  let pid := (← getKeypairPrefix (← getTxSkbPrefix first).keypair).peer
  peerGetMixed pid
  if !((← getPeerMixed pid).txQueue.all.any (·.head? == some first)) then
    liftPrefix (invariant "an item for the tx worker that is not on its peer's tx_queue")
  setTxSkbPrefix first fun p => { p with state }
  _ ← cpumaskChooseOnlinePrefix pid
  if !(← liftPrefix getDev).txWorkQueue.contains pid then
    liftPrefix (recordQueued .txWorker pid)
    liftPrefix (modifyDev fun d => { d with txWorkQueue := d.txWorkQueue ++ [pid] })
  peerPutMixed (some pid)


def enqueuePerDeviceAndPeerPrefix (pid : PeerId) (item : List SkbId) : MixedM Int := do
  let some first := item.head? | liftPrefix (invariant "an empty ring item")
  setTxSkbPrefix first fun p => { p with state := .uncrypted }
  let p ← getPeerMixed pid
  if ← liftPrefix (branch .enqueuePeerQueueFull (p.txQueue.count ≥ MAX_QUEUED_PACKETS)) then return -ENOSPC
  setPeerMixed pid { p with txQueue := p.txQueue.enqueue item }   -- W7: a multi-item queue
  let d ← liftPrefix getDev
  let cpu ← liftPrefix (cpumaskNextOnlineFrom d.encryptLastCpu)
  liftPrefix (modifyDev fun d => { d with encryptLastCpu := cpu })
  if ← liftPrefix (branch .enqueueRingFull d.encryptQueue.full) then return -WG.EPIPE
  liftPrefix (queueDeviceWork .encryptWorker)
  liftPrefix (modifyDev fun d => { d with encryptQueue := d.encryptQueue.produce item })
  return 0


def createDataPrefix (pid : PeerId) (item : List SkbId) : MixedM Unit := do
  let some first := item.head? | liftPrefix (invariant "an empty ring item")
  let ret ← do
    if ← liftPrefix (branch .createDataDead (← getPeerMixed pid).isDead) then pure (-EINVAL)
    else
      let ret ← enqueuePerDeviceAndPeerPrefix pid item
      if ← liftPrefix (branch .createDataEpipe (ret == -WG.EPIPE)) then enqueuePerPeerTxPrefix item .dead
      pure ret
  if ← liftPrefix (branch .createDataOk (ret == 0)) then return
  if ← liftPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
  keypairPutPrefix (some (← getTxSkbPrefix first).keypair) false
  peerPutMixed (some pid)
  for id in item do freeTxSkbPrefix id



theorem cpumaskChooseOnlinePrefix_erases (pid : PeerId) :
    ErasesPrefix (cpumaskChooseOnlinePrefix pid) (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnlinePrefix cpumaskChooseOnline
  repeat' first
    | exact getPeerMixed_erases _
    | exact setPeerMixed_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_range
    | apply erasesPrefix_bind
    | split
    | (solve | simp_all)
    | (intro x; try dsimp only)

theorem enqueuePerPeerTxPrefix_erases (item : List SkbId) (state : PacketState) :
    ErasesPrefix (enqueuePerPeerTxPrefix item state) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTxPrefix enqueuePerPeerTx
  cases he : item.head? with
  | none => exact erasesPrefix_lift _
  | some first =>
    apply erasesPrefix_bind (getTxSkbPrefix_erases _)
    intro pkt
    apply erasesPrefix_bind (getKeypairPrefix_erases _)
    intro k
    apply erasesPrefix_bind (peerGetMixed_erases _)
    intro _
    apply erasesPrefix_bind (getPeerMixed_erases _)
    intro p
    split
    · exact erasesPrefix_lift _
    · apply erasesPrefix_bind (setTxSkbPrefix_erases _ _)
      intro _
      apply erasesPrefix_bind (cpumaskChooseOnlinePrefix_erases _)
      intro _
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro d
      split
      · apply erasesPrefix_bind (erasesPrefix_lift _)
        intro _
        exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => peerPutMixed_erases _)
      · exact peerPutMixed_erases _

theorem enqueuePerDeviceAndPeerPrefix_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (enqueuePerDeviceAndPeerPrefix pid item) (enqueuePerDeviceAndPeer pid item) := by
  unfold enqueuePerDeviceAndPeerPrefix enqueuePerDeviceAndPeer
  cases he : item.head? <;> simp only
  · exact erasesPrefix_lift _
  · repeat' first
      | exact getPeerMixed_erases _
      | exact setPeerMixed_erases _ _
      | exact setTxSkbPrefix_erases _ _
      | exact erasesPrefix_lift _
      | exact erasesPrefix_pure _
      | apply erasesPrefix_bind
      | split
      | (solve | simp_all)
      | (intro x; try dsimp only)

theorem createDataPrefix_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (createDataPrefix pid item) (createData pid item) := by
  unfold createDataPrefix createData
  cases he : item.head? with
  | none => exact erasesPrefix_lift _
  | some first =>
    apply erasesPrefix_bind (getPeerMixed_erases _)
    intro p
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro dead
    have tail (ret : Int) : ErasesPrefix
        (do
          if ← liftPrefix (branch .createDataOk (ret == 0)) then return
          if ← liftPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
          keypairPutPrefix (some (← getTxSkbPrefix first).keypair) false
          peerPutMixed (some pid)
          for id in item do freeTxSkbPrefix id)
        (do
          if ← branch .createDataOk (ret == 0) then return
          if ← branch .createDataOkEpipe (ret == -WG.EPIPE) then return
          keypairPut (some (← getTxSkb first).keypair) false
          peerPut (some pid)
          for id in item do freeTxSkb id) := by
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro ok
      split
      · exact erasesPrefix_pure _
      · apply erasesPrefix_bind (erasesPrefix_lift _)
        intro pipe
        split
        · exact erasesPrefix_pure _
        · apply erasesPrefix_bind (getTxSkbPrefix_erases _)
          intro pkt
          apply erasesPrefix_bind (keypairPutPrefix_erases _ _)
          intro _
          apply erasesPrefix_bind (peerPutMixed_erases _)
          intro _
          apply erasesPrefix_bind (erasesPrefix_forIn _ _ _ _ (fun id _ =>
            erasesPrefix_bind (freeTxSkbPrefix_erases id) (fun _ => erasesPrefix_pure _)))
          intro _
          exact erasesPrefix_pure _
    split
    · simpa only [pure_bind] using tail (-EINVAL)
    · apply erasesPrefix_bind (enqueuePerDeviceAndPeerPrefix_erases _ _)
      intro ret
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro pipe
      split
      · simpa only [pure_bind] using erasesPrefix_bind (enqueuePerPeerTxPrefix_erases item .dead) (fun _ => tail ret)
      · simpa only [pure_bind] using tail ret

theorem cpumaskChooseOnlinePrefix_preserves_ambient (c : AmbientContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (cpumaskChooseOnlinePrefix pid) := by
  unfold cpumaskChooseOnlinePrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
  intro p
  have tail (invalid : Bool) : PrefixPreserves I LifetimeEvent.Safe
      (do
        if !invalid then return p.serialWorkCpu.getD 0
        for _ in [0:p.internalId % 1] do _ ← liftPrefix (branch .chooseCpuIndexIterate true)
        _ ← liftPrefix (branch .chooseCpuIndexIterate false)
        modifyPeerKeysPrefix pid fun q => {q with serialWorkCpu := some 0}
        return 0) := by
    split
    · exact PrefixPreserves.pure c.safe _
    · apply PrefixPreserves.bind
        (PrefixPreserves.range _ _ _ c.safe (fun _ _ =>
          PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
            (fun _ => PrefixPreserves.pure c.safe _)))
      intro _
      apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro _
      exact PrefixPreserves.bind (AmbientContracts.drop
        (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
        (fun _ => PrefixPreserves.pure c.safe _)
  apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro b
  split
  · simpa only [pure_bind, modifyPeerKeysPrefix, bind_assoc] using tail true
  · apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro b
    simpa only [modifyPeerKeysPrefix, bind_assoc] using tail b

theorem enqueuePerPeerTxPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (item : List SkbId) (state : PacketState) :
    PrefixPreserves I LifetimeEvent.Safe (enqueuePerPeerTxPrefix item state) := by
  unfold enqueuePerPeerTxPrefix
  cases he : item.head? with
  | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
  | some first =>
    apply PrefixPreserves.bind (AmbientContracts.drop (t.get (fun _ => True) _))
    intro pkt
    apply PrefixPreserves.bind (AmbientContracts.drop (c.getKeypair_frame (fun _ => True) _))
    intro k
    apply PrefixPreserves.bind (c.peerGet _)
    intro _
    apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    intro p
    split
    · exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    · apply PrefixPreserves.bind (AmbientContracts.drop (t.set (fun _ => True) _ _))
      intro _
      apply PrefixPreserves.bind (cpumaskChooseOnlinePrefix_preserves_ambient c _)
      intro _
      apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel))
      intro d
      split
      · apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (recordQueued_sameKernel _ _)))
        intro _
        exact PrefixPreserves.bind (AmbientContracts.drop (t.device (fun _ => True) (.work _))) (fun _ => c.peerPut _)
      · exact c.peerPut _

theorem enqueuePerDeviceAndPeerPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) (item : List SkbId) :
    PrefixPreserves I LifetimeEvent.Safe (enqueuePerDeviceAndPeerPrefix pid item) := by
  unfold enqueuePerDeviceAndPeerPrefix
  cases he : item.head? <;> simp only
  · exact AmbientContracts.drop (c.invariant (fun _ => True) _)
  · apply PrefixPreserves.bind (AmbientContracts.drop (t.set (fun _ => True) _ _))
    intro _
    apply PrefixEnsures.preserves
    have hget : PrefixEnsures I LifetimeEvent.Safe (getPeerMixed pid)
        (fun p h w => I h w ∧ (identityView w).1.slots pid = some p.internalId) :=
      (c.getPeer (fun _ => True) pid).consequence
        (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
    apply PrefixEnsures.bind hget
    intro p
    let P := fun s : IdentityView => s.1.slots pid = some p.internalId
    apply PrefixEnsures.bind (c.branch P _ _)
    intro full
    split
    · exact PrefixEnsures.pure (fun h w hi => c.safe h w hi.1) (fun _ _ hi => hi.1)
    · apply PrefixEnsures.bind ((c.setPeer (fun _ => True) pid {p with txQueue := p.txQueue.enqueue item}).consequence
        (fun _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ hi => hi.1))
      intro _
      apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel))
      intro d
      apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (cpumaskNextOnlineFrom_sameKernel _)))
      intro cpu
      apply PrefixPreserves.bind (AmbientContracts.drop (t.device (fun _ => True) (.cpu cpu)))
      intro _
      apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro full
      split
      · exact PrefixPreserves.pure c.safe (-WG.EPIPE)
      · apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (queueDeviceWork_sameKernel _)))
        intro _
        apply PrefixPreserves.bind (AmbientContracts.drop (t.device (fun _ => True) (.ring item)))
        intro _
        exact PrefixPreserves.pure c.safe 0

theorem createDataPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) (item : List SkbId) : PrefixPreserves I LifetimeEvent.Safe (createDataPrefix pid item) := by
  unfold createDataPrefix
  cases he : item.head? with
  | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
  | some first =>
    apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    intro p
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro dead
    have tail (ret : Int) : PrefixPreserves I LifetimeEvent.Safe
        (do
          if ← liftPrefix (branch .createDataOk (ret == 0)) then return
          if ← liftPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
          keypairPutPrefix (some (← getTxSkbPrefix first).keypair) false
          peerPutMixed (some pid)
          for id in item do freeTxSkbPrefix id) := by
      apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro ok
      split
      · exact PrefixPreserves.pure c.safe _
      · apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        intro pipe
        split
        · exact PrefixPreserves.pure c.safe _
        · apply PrefixPreserves.bind (AmbientContracts.drop (t.get (fun _ => True) _))
          intro pkt
          apply PrefixPreserves.bind (t.put _ _)
          intro _
          apply PrefixPreserves.bind (c.peerPut _)
          intro _
          apply PrefixPreserves.bind (PrefixPreserves.forIn _ _ _ c.safe (fun id _ =>
            PrefixPreserves.bind (t.free id) (fun _ => PrefixPreserves.pure c.safe _)))
          intro _
          exact PrefixPreserves.pure c.safe _
    split
    · simpa only [pure_bind] using tail (-EINVAL)
    · apply PrefixPreserves.bind (enqueuePerDeviceAndPeerPrefix_preserves_ambient c t _ _)
      intro ret
      apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro pipe
      split
      · simpa only [pure_bind] using PrefixPreserves.bind (enqueuePerPeerTxPrefix_preserves_ambient c t item .dead) (fun _ => tail ret)
      · simpa only [pure_bind] using tail ret

end Leanux.Proofs.WG.Lifetimes
