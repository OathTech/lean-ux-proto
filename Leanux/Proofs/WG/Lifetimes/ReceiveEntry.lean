import Leanux.Proofs.WG.Lifetimes.LookupAccess

set_option maxHeartbeats 400000
set_option pp.structureInstances false

/-! Complete data receive entry and device/peer enqueue. Queue scheduling,
CPU selection and scalar queue updates are inspected access-free operations.
The original ENOSPC invariant error and EPIPE dead-packet enqueue are retained.
No index consistency, ownership or packet-delivery property is assumed. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem recordQueued_sameKernel (worker : Worker) (pid : Nat) : SameKernel (recordQueued worker pid) := by
  apply sameKernel_of_wp
  intro k
  have hh := sameKernel_wp _ (hidden_sameKernel (.queued worker)) (fun k' => k' = k)
  mvcgen [recordQueued, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem queueDeviceWork_sameKernel (worker : Worker) : SameKernel (queueDeviceWork worker) := by
  apply sameKernel_of_wp
  intro k
  have hq := sameKernel_wp _ (recordQueued_sameKernel worker 0) (fun k' => k' = k)
  have hp := sameKernel_wp _ (peekQueuedUnit_sameKernel worker 0) (fun k' => k' = k)
  mvcgen [queueDeviceWork, hq, hp, unsupported]

theorem cpumaskNextOnlineFrom_sameKernel (last : Int) : SameKernel (cpumaskNextOnlineFrom last) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [cpumaskNextOnlineFrom, branch]

theorem keypairGetCurrent_sameKernel : SameKernel keypairGetCurrent := by
  apply sameKernel_of_wp
  intro k
  mvcgen [keypairGetCurrent, branch]

def enqueuePerDeviceAndPeerRxPrefix (id : SkbId) : MixedM Int := do
  setRxSkbPrefix id fun p => {p with state := .uncrypted}
  let pkt ← getRxSkbPrefix id
  let p ← getPeerMixed pkt.peer
  if ← liftPrefix (branch .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS)) then return -ENOSPC
  setPeerMixed pkt.peer {p with rxQueue := p.rxQueue.enqueue id}
  let d ← liftPrefix getDev
  let cpu ← liftPrefix (cpumaskNextOnlineFrom d.decryptLastCpu)
  liftPrefix (modifyDev fun d => {d with decryptLastCpu := cpu})
  if ← liftPrefix (branch .enqueueRingFull d.decryptQueue.full) then return -EPIPE
  liftPrefix (queueDeviceWork .decryptWorker)
  liftPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id})
  return 0

theorem enqueuePerDeviceAndPeerRxPrefix_erases (id : SkbId) :
    ErasesPrefix (enqueuePerDeviceAndPeerRxPrefix id) (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRxPrefix enqueuePerDeviceAndPeerRx
  repeat' first
    | exact setRxSkbPrefix_erases _ _
    | exact getRxSkbPrefix_erases _
    | exact getPeerMixed_erases _
    | exact setPeerMixed_erases _ _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | split
    | (solve | simp_all)
    | (intro x; try dsimp only)
    | rfl

theorem enqueuePerDeviceAndPeerRxPrefix_preserves_ambient (c : AmbientContracts I)
    (hc : ∀ cpu, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptLastCpu := cpu})))
    (hq : ∀ id, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id})))
    (id : SkbId) : PrefixPreserves I LifetimeEvent.Safe (enqueuePerDeviceAndPeerRxPrefix id) := by
  unfold enqueuePerDeviceAndPeerRxPrefix
  apply PrefixPreserves.bind (AmbientContracts.drop (c.setRx (fun _ => True) id _))
  intro _
  apply PrefixPreserves.bind (AmbientContracts.drop (c.getRx (fun _ => True) id))
  intro pkt
  apply PrefixEnsures.preserves
  have hget : PrefixEnsures I LifetimeEvent.Safe (getPeerMixed pkt.peer)
      (fun p h w => I h w ∧ (identityView w).1.slots pkt.peer = some p.internalId) :=
    (c.getPeer (fun _ => True) pkt.peer).consequence
      (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply PrefixEnsures.bind hget
  intro p
  let P := fun s : IdentityView => s.1.slots pkt.peer = some p.internalId
  apply PrefixEnsures.bind (c.branch P _ _)
  intro full
  split
  · exact PrefixEnsures.pure (fun h w hi => c.safe h w hi.1) (fun _ _ hi => hi.1)
  · apply PrefixEnsures.bind ((c.setPeer (fun _ => True) pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).consequence
      (fun _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ hi => hi.1))
    intro _
    apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel))
    intro d
    apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (cpumaskNextOnlineFrom_sameKernel _)))
    intro cpu
    apply PrefixPreserves.bind (hc cpu)
    intro _
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro full
    split
    · exact PrefixPreserves.pure c.safe (-EPIPE)
    · apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ (queueDeviceWork_sameKernel _)))
      intro _
      apply PrefixPreserves.bind (hq id)
      intro _
      exact PrefixPreserves.pure c.safe 0

theorem decryptLastCpu_identity (cpu : Int) :
    SameView identityView (modifyDev fun d => {d with decryptLastCpu := cpu}) := by
  intro w x v hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents
  simp [Option.bind_map, Function.comp_def]

theorem decryptProduce_identity (id : SkbId) :
    SameView identityView (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id}) := by
  intro w x v hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents
  simp [Option.bind_map, Function.comp_def]

theorem decryptLastCpu_allocation (cpu : Int) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptLastCpu := cpu})) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  exact hi.congr (decryptLastCpu_identity cpu w x v hr)
    (metadata_modifyDev (fun d => {d with decryptLastCpu := cpu}) (fun _ => rfl) w x v hr)

theorem decryptProduce_allocation (id : SkbId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id})) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  exact hi.congr (decryptProduce_identity id w x v hr)
    (metadata_modifyDev (fun d => {d with decryptQueue := d.decryptQueue.produce id}) (fun _ => rfl) w x v hr)

theorem enqueuePerDeviceAndPeerRxPrefix_allocation (id : SkbId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (enqueuePerDeviceAndPeerRxPrefix id) :=
  enqueuePerDeviceAndPeerRxPrefix_preserves_ambient allocationAmbient
    decryptLastCpu_allocation decryptProduce_allocation id

def consumeDataPrefix (msg : List UInt8) (src : SkbSource) (ds : Nat) : MixedM Unit := do
  let entry ← indexLookupPrefix [.keypair] (u32le msg 4)
  let peer := entry.map (·.peer)
  let kp ← match entry with
    | none => do liftPrefix keypairGetCurrent; pure none
    | some e => keypairGetPrefix e.keypair
  if ← liftPrefix (branch .dataNoKeypair kp.isNone) then
    peerPutMixed peer
    return
  let some id := kp | liftPrefix (invariant "unreachable")
  let some pid := peer | liftPrefix (invariant "a keypair entry without a peer")
  if ← liftPrefix (branch .dataPeerDead (← getPeerMixed pid).isDead) then
    keypairPutPrefix (some id) false
    peerPutMixed peer
    return
  let skb ← newRxSkbPrefix {peer := pid, keypair := id, bytes := msg, source := src, ds}
  let ret ← enqueuePerDeviceAndPeerRxPrefix skb
  if ← liftPrefix (branch .dataEpipe (ret == -EPIPE)) then enqueuePerPeerRxPrefix (pure ()) skb .dead
  if ← liftPrefix (WG.orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
  liftPrefix (invariant "unreachable")

theorem consumeDataPrefix_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesPrefix (consumeDataPrefix msg src ds) (consumeData msg src ds) := by
  unfold consumeDataPrefix consumeData
  apply erasesPrefix_bind (indexLookupPrefix_erases _ _)
  intro entry
  cases entry with
  | none =>
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    simp only [pure_bind, Option.map_none]
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro noKey
    split
    · exact erasesPrefix_bind (peerPutMixed_erases _) (fun _ => erasesPrefix_pure _)
    · exact erasesPrefix_lift _
  | some e =>
    apply erasesPrefix_bind (keypairGetPrefix_erases e.keypair)
    intro kp
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro noKey
    split
    · exact erasesPrefix_bind (peerPutMixed_erases _) (fun _ => erasesPrefix_pure _)
    · cases kp with
      | none => exact erasesPrefix_lift _
      | some id =>
        apply erasesPrefix_bind (getPeerMixed_erases _)
        intro p
        apply erasesPrefix_bind (erasesPrefix_lift _)
        intro dead
        split
        · exact erasesPrefix_bind (keypairPutPrefix_erases _ _) (fun _ =>
            erasesPrefix_bind (peerPutMixed_erases _) (fun _ => erasesPrefix_pure _))
        · apply erasesPrefix_bind (PacketAllocation.erases (.rx _))
          intro skb
          apply erasesPrefix_bind (enqueuePerDeviceAndPeerRxPrefix_erases skb)
          intro ret
          apply erasesPrefix_bind (erasesPrefix_lift _)
          intro pipe
          have tail : ErasesPrefix (Event := LifetimeEvent)
              (do if ← liftPrefix (WG.orM (branch .dataEnqueueOk (ret == 0))
                    (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
                  liftPrefix (invariant "unreachable"))
              (do if ← WG.orM (branch .dataEnqueueOk (ret == 0))
                    (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
                  invariant "unreachable") := by
            apply erasesPrefix_bind (erasesPrefix_lift _)
            intro okay
            split
            · exact erasesPrefix_pure _
            · exact erasesPrefix_lift _
          split
          · exact erasesPrefix_bind (enqueuePerPeerRxPrefix_pure_erases skb .dead) (fun _ => tail)
          · exact tail

theorem consumeDataPrefix_preserves_ambient (c : AmbientContracts I)
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now))
    (alloc : ∀ p, PrefixPreserves I LifetimeEvent.Safe (newRxSkbPrefix p))
    (hc : ∀ cpu, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptLastCpu := cpu})))
    (hq : ∀ id, PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id})))
    (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (consumeDataPrefix msg src ds) := by
  unfold consumeDataPrefix
  apply PrefixPreserves.bind (indexLookupPrefix_preserves_ambient c _ _)
  intro entry
  cases entry with
  | none =>
    apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _ keypairGetCurrent_sameKernel))
    intro _
    simp only [pure_bind, Option.map_none]
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro noKey
    split
    · exact PrefixPreserves.bind (c.peerPut _) (fun _ => PrefixPreserves.pure c.safe ())
    · exact AmbientContracts.drop (c.invariant (fun _ => True) _)
  | some e =>
    apply PrefixPreserves.bind (AmbientContracts.drop (keypairGetPrefix_spec_ambient c (fun _ => True) e.keypair))
    intro kp
    apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro noKey
    split
    · exact PrefixPreserves.bind (c.peerPut _) (fun _ => PrefixPreserves.pure c.safe ())
    · cases kp with
      | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
      | some id =>
        apply PrefixPreserves.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
        intro p
        apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
        intro dead
        split
        · exact PrefixPreserves.bind (put _ _) (fun _ =>
            PrefixPreserves.bind (c.peerPut _) (fun _ => PrefixPreserves.pure c.safe ()))
        · apply PrefixPreserves.bind (alloc _)
          intro skb
          apply PrefixPreserves.bind (enqueuePerDeviceAndPeerRxPrefix_preserves_ambient c hc hq skb)
          intro ret
          apply PrefixPreserves.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
          intro pipe
          have tail : PrefixPreserves I LifetimeEvent.Safe
              (do if ← liftPrefix (WG.orM (branch .dataEnqueueOk (ret == 0))
                    (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
                  liftPrefix (invariant "unreachable")) := by
            apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) _
              (orM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _))))
            intro okay
            split
            · exact PrefixPreserves.pure c.safe ()
            · exact AmbientContracts.drop (c.invariant (fun _ => True) _)
          split
          · exact PrefixPreserves.bind
              (enqueuePerPeerRxPrefix_preserves_ambient c (PrefixPreserves.pure c.safe ()) skb .dead)
              (fun _ => tail)
          · exact tail

theorem consumeDataPrefix_allocation (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (consumeDataPrefix msg src ds) :=
  consumeDataPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation
    (fun p => PacketAllocation.preserves (.rx p)) decryptLastCpu_allocation decryptProduce_allocation msg src ds

end Leanux.Proofs.WG.Lifetimes
