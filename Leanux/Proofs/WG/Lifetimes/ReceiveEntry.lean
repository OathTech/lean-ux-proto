import Leanux.Proofs.WG.Lifetimes.LookupAccess

set_option maxHeartbeats 400000
set_option pp.structureInstances false

/-! Complete data receive entry and device/peer enqueue. Queue scheduling,
CPU selection and scalar queue updates are inspected access-free operations.
The original ENOSPC reference releases/free and EPIPE dead-packet enqueue are retained.
No index consistency, ownership or packet-delivery property is assumed. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

theorem cpumaskNextOnlineFrom_sameStore (last : Int) : SameWGStore (cpumaskNextOnlineFrom last) := by
  apply SameView.of_wp
  intro initial
  mvcgen [cpumaskNextOnlineFrom, branch, AmbientM.branch]

theorem keypairGetNull_sameStore : SameWGStore keypairGetNull := by
  apply SameView.of_wp
  intro initial
  mvcgen [keypairGetNull, branch, AmbientM.branch]

def enqueuePerDeviceAndPeerRxPrefix (id : SkbId) : MixedM Int := do
  setRxSkbPrefix id fun p => {p with state := .uncrypted}
  let pkt ← getRxSkbPrefix id
  let p ← getPeerMixed pkt.peer
  if ← liftWGPrefix (branch .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS)) then return -ENOSPC
  setPeerMixed pkt.peer {p with rxQueue := p.rxQueue.enqueue id}
  let d ← liftWGPrefix getDev
  let cpu ← liftWGPrefix (cpumaskNextOnlineFrom d.decryptLastCpu)
  liftWGPrefix (modifyDev fun d => {d with decryptLastCpu := cpu})
  if ← liftWGPrefix (branch .enqueueRingFull d.decryptQueue.full) then return -EPIPE
  liftWGPrefix (queueDeviceWork .decryptWorker : WG.M Unit)
  liftWGPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id})
  return 0

theorem enqueuePerDeviceAndPeerRxPrefix_erases (id : SkbId) :
    ErasesStatePrefix (enqueuePerDeviceAndPeerRxPrefix id) (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRxPrefix enqueuePerDeviceAndPeerRx
  apply erasesStatePrefix_bind (setRxSkbPrefix_erases _ _)
  intro _
  apply erasesStatePrefix_bind (getRxSkbPrefix_erases _)
  intro pkt
  apply erasesStatePrefix_bind (getPeerMixed_erases _)
  intro p
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro full
  split
  · exact erasesStatePrefix_pure _
  · apply erasesStatePrefix_bind (setPeerMixed_erases _ _)
    intro _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro d
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro cpu
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro _
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro full
    split
    · exact erasesStatePrefix_pure _
    · apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro _
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro _
      exact erasesStatePrefix_pure _

theorem enqueuePerDeviceAndPeerRxPrefix_preserves_ambient (c : AmbientContracts I)
    (hc : ∀ cpu, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with decryptLastCpu := cpu})))
    (hq : ∀ id, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id})))
    (id : SkbId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (enqueuePerDeviceAndPeerRxPrefix id) := by
  unfold enqueuePerDeviceAndPeerRxPrefix
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.setRx (fun _ => True) id _))
  intro _
  apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getRx (fun _ => True) id))
  intro pkt
  have hget : StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe (getPeerMixed pkt.peer)
      (fun p h w _ => I h w ∧ (identityView w).1.slots pkt.peer = some p.internalId) :=
    (c.getPeer (fun _ => True) pkt.peer).consequence
      (fun _ _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply StatePrefixEnsures.bind hget
  intro p
  let P := fun s : IdentityView => s.1.slots pkt.peer = some p.internalId
  apply StatePrefixEnsures.bind (c.branch P _ _)
  intro full
  split
  · exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi.1) (fun _ _ _ hi => hi.1)
  · apply StatePrefixEnsures.bind ((c.setPeer (fun _ => True) pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).consequence
      (fun _ _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ _ hi => hi.1))
    intro _
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (by
      apply SameView.of_wp
      intro initial
      mvcgen [getDev, invariant, AmbientM.invariant])))
    intro d
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (cpumaskNextOnlineFrom_sameStore _)))
    intro cpu
    apply StatePrefixEnsures.bind (hc cpu)
    intro _
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro full
    split
    · exact StatePrefixEnsures.pure (-EPIPE) (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    · apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (fun initial =>
        hoare_liftAmbient (queueDeviceWork .decryptWorker) (fun w => wgStoreView w = initial))))
      intro _
      apply StatePrefixEnsures.bind (hq id)
      intro _
      exact StatePrefixEnsures.pure 0 (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)

theorem decryptLastCpu_identity (cpu : Int) :
    SameView identityView (modifyDev fun d => {d with decryptLastCpu := cpu}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents
  simp [Option.bind_map, Function.comp_def]

theorem decryptProduce_identity (id : SkbId) :
    SameView identityView (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents
  simp [Option.bind_map, Function.comp_def]

theorem decryptLastCpu_allocation (cpu : Int) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with decryptLastCpu := cpu})) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  exact hi.congr ((ProjectedAction.iff_run_ambient _ _ _).mp
    (decryptLastCpu_identity cpu) w ambient x v ambient' hr)
    ((ProjectedAction.iff_run_ambient _ _ _).mp
      (metadata_modifyDev (fun d => {d with decryptLastCpu := cpu}) (fun _ => rfl)) w ambient x v ambient' hr)

theorem decryptProduce_allocation (id : SkbId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id})) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  exact hi.congr ((ProjectedAction.iff_run_ambient _ _ _).mp
    (decryptProduce_identity id) w ambient x v ambient' hr)
    ((ProjectedAction.iff_run_ambient _ _ _).mp
      (metadata_modifyDev (fun d => {d with decryptQueue := d.decryptQueue.produce id}) (fun _ => rfl)) w ambient x v ambient' hr)

theorem enqueuePerDeviceAndPeerRxPrefix_allocation (id : SkbId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (enqueuePerDeviceAndPeerRxPrefix id) :=
  enqueuePerDeviceAndPeerRxPrefix_preserves_ambient allocationAmbient
    decryptLastCpu_allocation decryptProduce_allocation id

def consumeDataPrefix (msg : List UInt8) (src : SkbSource) (ds : Nat) : MixedM Unit := do
  let entry ← indexLookupPrefix [.keypair] (u32le msg 4)
  let (keypair, peer) ← match entry with
    | none => pure (none, none)
    | some (IndexOwner.keypair kp, pid) => pure (some kp, some pid)
    | some (IndexOwner.handshake _, _) => liftWGPrefix (invariant "a handshake entry under the keypair mask")
  let kp ← match keypair with
    | none => do liftWGPrefix keypairGetNull; pure none
    | some kp => keypairGetPrefix (some kp)
  if ← liftWGPrefix (branch .dataNoKeypair kp.isNone) then
    peerPutMixed peer
    return
  let some id := kp | liftWGPrefix (invariant "unreachable")
  let some pid := peer | liftWGPrefix (invariant "a keypair entry without a peer")
  if ← liftWGPrefix (branch .dataPeerDead (← getPeerMixed pid).isDead) then
    keypairPutPrefix (some id) false
    peerPutMixed peer
    return
  let skb ← newRxSkbPrefix {peer := pid, keypair := id, bytes := msg, source := src, ds}
  let ret ← enqueuePerDeviceAndPeerRxPrefix skb
  if ← liftWGPrefix (branch .dataEpipe (ret == -EPIPE)) then enqueuePerPeerRxNativePrefix skb .dead
  if ← liftWGPrefix (WG.orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
  keypairPutPrefix (some id) false
  peerPutMixed peer
  freeRxSkbPrefix skb

theorem consumeDataPrefix_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesStatePrefix (consumeDataPrefix msg src ds) (consumeData msg src ds) := by
  unfold consumeDataPrefix consumeData
  simp only [pure_bind]
  apply erasesStatePrefix_bind (indexLookupPrefix_erases _ _)
  intro entry
  cases entry with
  | none =>
    dsimp only
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro _
    try simp only [pure_bind, Option.map_none]
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro noKey
    split
    · exact erasesStatePrefix_bind (peerPutMixed_erases _) (fun _ => erasesStatePrefix_pure _)
    · exact erasesStatePrefix_lift _
  | some e =>
    rcases e with ⟨owner, pid⟩
    cases owner with
    | handshake owner =>
      intro w ambient h
      rfl
    | keypair key =>
      try simp only [pure_bind]
      apply erasesStatePrefix_bind (keypairGetPrefix_erases (some key))
      intro kp
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro noKey
      split
      · exact erasesStatePrefix_bind (peerPutMixed_erases _) (fun _ => erasesStatePrefix_pure _)
      · cases kp with
        | none => exact erasesStatePrefix_lift _
        | some id =>
          apply erasesStatePrefix_bind (getPeerMixed_erases _)
          intro p
          apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
          intro dead
          split
          · exact erasesStatePrefix_bind (keypairPutPrefix_erases _ _) (fun _ =>
              erasesStatePrefix_bind (peerPutMixed_erases _) (fun _ => erasesStatePrefix_pure _))
          · apply erasesStatePrefix_bind (PacketAllocation.erases (.rx _))
            intro skb
            apply erasesStatePrefix_bind (enqueuePerDeviceAndPeerRxPrefix_erases skb)
            intro ret
            apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
            intro pipe
            have tail : ErasesStatePrefix (E := LifetimeEvent)
                (do if ← liftWGPrefix (WG.orM (branch .dataEnqueueOk (ret == 0))
                      (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
                    keypairPutPrefix (some id) false
                    peerPutMixed (some pid)
                    freeRxSkbPrefix skb)
                (do if ← WG.orM (branch .dataEnqueueOk (ret == 0))
                      (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
                    keypairPut (some id) false
                    peerPut (some pid)
                    freeRxSkb skb) := by
              apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
              intro okay
              split
              · exact erasesStatePrefix_pure _
              · exact erasesStatePrefix_bind (keypairPutPrefix_erases _ _) (fun _ =>
                  erasesStatePrefix_bind (peerPutMixed_erases _) (fun _ => freeRxSkbPrefix_erases _))
            split
            · exact erasesStatePrefix_bind (enqueuePerPeerRxNativePrefix_erases skb .dead) (fun _ => tail)
            · exact tail

theorem consumeDataPrefix_preserves_ambient (c : AmbientContracts I)
    (put : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now))
    (alloc : ∀ p, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (newRxSkbPrefix p))
    (free : ∀ id, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (freeRxSkbPrefix id))
    (hc : ∀ cpu, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with decryptLastCpu := cpu})))
    (hq : ∀ id, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id})))
    (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (consumeDataPrefix msg src ds) := by
  unfold consumeDataPrefix
  simp only [pure_bind]
  apply StatePrefixEnsures.bind (indexLookupPrefix_preserves_ambient c _ _)
  intro entry
  cases entry with
  | none =>
    dsimp only
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ keypairGetNull_sameStore))
    intro _
    try simp only [pure_bind, Option.map_none]
    apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
    intro noKey
    split
    · exact StatePrefixEnsures.bind (c.peerPut _) (fun _ => StatePrefixEnsures.pure () (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    · exact AmbientContracts.drop (c.invariant (fun _ => True) _)
  | some e =>
    rcases e with ⟨owner, pid⟩
    cases owner with
    | handshake owner =>
      intro w ambient h hi
      change ∃ tail, h = h ++ tail ∧ LifetimeEvent.Safe h ∧ True
      exact ⟨[], by simp, c.safe h w hi, trivial⟩
    | keypair key =>
      try simp only [pure_bind]
      apply StatePrefixEnsures.bind (AmbientContracts.drop (keypairGetPrefix_spec_ambient c (fun _ => True) (some key)))
      intro kp
      apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
      intro noKey
      split
      · exact StatePrefixEnsures.bind (c.peerPut _) (fun _ => StatePrefixEnsures.pure () (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
      · cases kp with
        | none => exact AmbientContracts.drop (c.invariant (fun _ => True) _)
        | some id =>
          apply StatePrefixEnsures.bind (AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
          intro p
          apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
          intro dead
          split
          · exact StatePrefixEnsures.bind (put _ _) (fun _ =>
              StatePrefixEnsures.bind (c.peerPut _) (fun _ => StatePrefixEnsures.pure () (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)))
          · apply StatePrefixEnsures.bind (alloc _)
            intro skb
            apply StatePrefixEnsures.bind (enqueuePerDeviceAndPeerRxPrefix_preserves_ambient c hc hq skb)
            intro ret
            apply StatePrefixEnsures.bind (AmbientContracts.drop (c.branch (fun _ => True) _ _))
            intro pipe
            have tail : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
                (do if ← liftWGPrefix (WG.orM (branch .dataEnqueueOk (ret == 0))
                      (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
                    keypairPutPrefix (some id) false
                    peerPutMixed (some pid)
                    freeRxSkbPrefix skb) := by
              apply StatePrefixEnsures.bind (AmbientContracts.drop (c.store (fun _ => True) _ (by
                apply SameView.of_wp
                intro initial
                mvcgen [WG.orM, branch, AmbientM.branch])))
              intro okay
              split
              · exact StatePrefixEnsures.pure () (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
              · exact StatePrefixEnsures.bind (put _ _) (fun _ =>
                  StatePrefixEnsures.bind (c.peerPut _) (fun _ => free _))
            split
            · exact StatePrefixEnsures.bind
                (enqueuePerPeerRxNativePrefix_preserves_ambient c skb .dead)
                (fun _ => tail)
            · exact tail

theorem consumeDataPrefix_allocation (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (consumeDataPrefix msg src ds) :=
  consumeDataPrefix_preserves_ambient allocationAmbient keypairPutPrefix_allocation
    (fun p => PacketAllocation.preserves (.rx p)) freeRxSkbPrefix_allocation decryptLastCpu_allocation decryptProduce_allocation msg src ds

/-- The original caller contract at the actual product boundary. -/
theorem enqueuePerDeviceAndPeerRxPrefix_preserves_product (c : ProductAmbientContracts I)
    (hc : ∀ cpu, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with decryptLastCpu := cpu}))))
    (hq : ∀ id, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id}))))
    (id : SkbId) : PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (enqueuePerDeviceAndPeerRxPrefix id)) := by
  have branch_spec (P : IdentityView → Prop) (d : Decision) (b : Bool) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (branch d b))) (fun _ => P) := by
    apply c.nativeStore
    intro initial
    exact hoare_liftAmbient (AmbientM.branch d b) (fun w => wgStoreView w = initial)
  simp only [enqueuePerDeviceAndPeerRxPrefix, liftWGObserver_bind, liftWGObserver_pure]
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.setRx (fun _ => True) id _))
  intro _
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getRx (fun _ => True) id))
  intro pkt
  apply PrefixEnsures.preserves
  have hget : PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (getPeerMixed pkt.peer))
      (fun p h w => I h w ∧ (identityView w.wg).1.slots pkt.peer = some p.internalId) :=
    (c.getPeer (fun _ => True) pkt.peer).consequence
      (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => ⟨hi.1, hi.2.2⟩)
  apply PrefixEnsures.bind hget
  intro p
  let P := fun s : IdentityView => s.1.slots pkt.peer = some p.internalId
  apply PrefixEnsures.bind (branch_spec P _ _)
  intro full
  split
  · exact PrefixEnsures.pure (fun h w hi => c.safe h w hi.1) (fun _ _ hi => hi.1)
  · simp only [liftWGObserver_bind, liftWGObserver_pure]
    apply PrefixEnsures.bind ((c.setPeer (fun _ => True) pkt.peer {p with rxQueue := p.rxQueue.enqueue id}).consequence
      (fun _ _ hi => ⟨hi.1, True.intro, hi.2⟩) (fun _ _ _ hi => hi.1))
    intro _
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (by
      apply SameView.of_wp
      intro initial
      mvcgen [getDev, invariant, AmbientM.invariant])))
    intro d
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (cpumaskNextOnlineFrom_sameStore _)))
    intro cpu
    apply PrefixPreserves.bind (hc cpu)
    intro _
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
    intro full
    split
    · exact PrefixPreserves.pure c.safe (-EPIPE)
    · simp only [liftWGObserver_bind, liftWGObserver_pure]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (fun initial =>
        hoare_liftAmbient (AmbientM.queueDeviceWork .decryptWorker) (fun w => wgStoreView w = initial))))
      intro _
      apply PrefixPreserves.bind (hq id)
      intro _
      exact PrefixPreserves.pure c.safe 0

/-- Arbitrary product invariants retain their original caller-supplied obligations. -/
theorem consumeDataPrefix_preserves_product (c : ProductAmbientContracts I)
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (alloc : ∀ p, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (newRxSkbPrefix p)))
    (free : ∀ id, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (freeRxSkbPrefix id)))
    (hc : ∀ cpu, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with decryptLastCpu := cpu}))))
    (hq : ∀ id, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with decryptQueue := d.decryptQueue.produce id}))))
    (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (consumeDataPrefix msg src ds)) := by
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
  have keyGet (P : IdentityView → Prop) (kp : Option KeypairId) :
      ProductAmbientSpec I P (liftWGObserver (keypairGetPrefix kp)) (fun _ => P) := by
    simp only [keypairGetPrefix, liftWGObserver_bind, liftWGObserver_pure]
    apply PrefixEnsures.bind (branch_spec P _ _)
    intro isNull
    split
    · exact c.pure P _
    · cases kp with
      | some id =>
        simp only [liftWGObserver_bind, liftWGObserver_pure]
        apply PrefixEnsures.bind (c.getKeypair P id)
        intro k
        let Q := fun s : IdentityView => P s ∧ s.2.1 id = some k.internalId
        apply PrefixEnsures.bind (c.nativeStore Q _ (by
          have factor : (refcountIncNotZero k.refcount : WG.M Bool) =
              StateT.lift (refcountIncNotZero k.refcount : AmbientM Bool) := by
            change (refcountIncNotZero k.refcount : WG.M Bool) =
              (monadLift (refcountIncNotZero k.refcount : AmbientM Bool) : WG.M Bool)
            simp only [refcountIncNotZero, branch, branchCmp, unsupported, monadLift_self,
              monadLift_bind, monadLift_pure, apply_ite]
          rw [factor]
          intro initial
          exact hoare_liftAmbient (refcountIncNotZero k.refcount : AmbientM Bool)
            (fun w => wgStoreView w = initial)))
        intro nz
        apply PrefixEnsures.bind (branch_spec Q _ _)
        intro zero
        split
        · exact ProductAmbientContracts.forget (c.pure Q none) (fun _ _ hi => hi.1)
        · simp only [liftWGObserver_bind, liftWGObserver_pure]
          apply PrefixEnsures.bind (c.setKeypair P id {k with refcount := k.refcount + 1})
          intro _
          exact c.pure P _
      | none =>
        apply c.nativeStore
        intro initial
        exact hoare_liftAmbient (AmbientM.invariant _) (fun w => wgStoreView w = initial)
  simp only [consumeDataPrefix, pure_bind, liftWGObserver_bind, liftWGObserver_pure]
  apply PrefixPreserves.bind (indexLookupPrefix_preserves_product c _ _)
  intro entry
  cases entry with
  | none =>
    simp only [liftWGObserver_bind, liftWGObserver_pure]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ keypairGetNull_sameStore))
    intro _
    try simp only [pure_bind, Option.map_none, liftWGObserver_bind, liftWGObserver_pure]
    apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
    intro noKey
    split
    · simp only [liftWGObserver_bind, liftWGObserver_pure]
      exact PrefixPreserves.bind (c.peerPut _) (fun _ => PrefixPreserves.pure c.safe ())
    · exact ProductAmbientContracts.drop (invariant_spec (fun _ => True) _)
  | some e =>
    rcases e with ⟨owner, pid⟩
    cases owner with
    | handshake owner =>
      intro w h hi
      exact ⟨[], by change h = h ++ []; simp, c.safe h w hi, trivial⟩
    | keypair key =>
      simp only [pure_bind, liftWGObserver_bind, liftWGObserver_pure]
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (keyGet (fun _ => True) (some key)))
      intro kp
      apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
      intro noKey
      split
      · simp only [liftWGObserver_bind, liftWGObserver_pure]
        exact PrefixPreserves.bind (c.peerPut _) (fun _ => PrefixPreserves.pure c.safe ())
      · cases kp with
        | none => exact ProductAmbientContracts.drop (invariant_spec (fun _ => True) _)
        | some id =>
          simp only [liftWGObserver_bind, liftWGObserver_pure]
          apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
          intro p
          apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
          intro dead
          split
          · simp only [liftWGObserver_bind, liftWGObserver_pure]
            exact PrefixPreserves.bind (put _ _) (fun _ =>
                PrefixPreserves.bind (c.peerPut _) (fun _ => PrefixPreserves.pure c.safe ()))
          · simp only [liftWGObserver_bind, liftWGObserver_pure]
            apply PrefixPreserves.bind (alloc _)
            intro skb
            apply PrefixPreserves.bind (enqueuePerDeviceAndPeerRxPrefix_preserves_product c hc hq skb)
            intro ret
            apply PrefixPreserves.bind (ProductAmbientContracts.drop (branch_spec (fun _ => True) _ _))
            intro pipe
            have tail : PrefixPreserves I LifetimeEvent.Safe
                (do if ← liftWGObserver (liftWGPrefix (WG.orM (branch .dataEnqueueOk (ret == 0))
                      (branch .dataEnqueueOkEpipe (ret == -EPIPE)))) then return
                    liftWGObserver (keypairPutPrefix (some id) false)
                    liftWGObserver (peerPutMixed (some pid))
                    liftWGObserver (freeRxSkbPrefix skb)) := by
              apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ (by
                apply SameView.of_wp
                intro initial
                mvcgen [WG.orM, branch, AmbientM.branch])))
              intro okay
              split
              · exact PrefixPreserves.pure c.safe ()
              · exact PrefixPreserves.bind (put _ _) (fun _ =>
                  PrefixPreserves.bind (c.peerPut _) (fun _ => free _))
            split
            · simp only [liftWGObserver_bind, liftWGObserver_pure]
              apply PrefixPreserves.bind (g := liftWGObserver (enqueuePerPeerRxNativePrefix skb .dead))
              · rw [enqueuePerPeerRxNativePrefix_lift]
                exact enqueuePerPeerRxPrefix_preserves_ambient c (PrefixPreserves.pure c.safe ()) skb .dead
              · intro _
                simpa only [apply_ite, liftWGObserver_bind, liftWGObserver_pure] using tail
            · simpa only [apply_ite, liftWGObserver_bind, liftWGObserver_pure] using tail

end Leanux.Proofs.WG.Lifetimes
