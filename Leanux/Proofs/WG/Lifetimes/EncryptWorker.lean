import Leanux.Proofs.WG.Lifetimes.TxEnqueue
import Leanux.Proofs.WG.Lifetimes.MaintenanceTimers
import Leanux.Proofs.Framing.WGData
import Leanux.Proofs.Logged.PrefixWorkers

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Complete original encryption and worker iteration. Explicit checksum,
softirq and rescheduling callbacks may change identities while preserving the
ambient invariant. Safety concerns resolved current-store accesses, not the
ownership or continued identity of saved numeric references. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def encryptPacketPrefix (checksumHelp : Packet → PrefixM LifetimeEvent Packet)
    (keypair : KeypairId) (pkt : DataPacket) : PrefixM LifetimeEvent (Option (List UInt8)) := do
  liftPrefix (skipCut [.flowHashSecret])
  let len := pkt.plaintext.bytes.length
  let paddingLen ← liftWGObserver (liftWGPrefix (calculateSkbPadding len pkt.plaintext.mtu))
  if ← liftPrefix (branch .encCowHeadFailed !(← liftPrefix (hiddenAlloc .skbCowHead))) then return none
  let mut inner := pkt.plaintext
  if ← liftPrefix (branch .encChecksumPartial inner.csum.isSome) then
    if ← liftPrefix (branch .encChecksumHelpFailed !(← liftPrefix (hiddenAlloc .skbChecksumHelp))) then return none
    inner ← checksumHelp inner
  let cowOk ← liftPrefix (hiddenAlloc .skbCowDataTx)
  if ← liftPrefix (branch .encCowDataFailed !cowOk) then return none
  if ← liftPrefix (branch .encTooManyFrags false) then return none
  let k ← liftWGObserver (getKeypairPrefix keypair)
  if ← liftPrefix (branch .encSgvecFailed false) then return none
  return some (dataMessage k.remoteIndex pkt.nonce k.sending.key
    (inner.bytes ++ List.replicate paddingLen 0))

def encryptStepPrefix (checksumHelp : Packet → PrefixM LifetimeEvent Packet) (softirq : PrefixM LifetimeEvent Unit) : PrefixM LifetimeEvent Bool := do
  let (item, ring) := (← liftWGObserver (liftWGPrefix getDev)).encryptQueue.consume
  liftWGObserver (liftWGPrefix (modifyDev fun d => {d with encryptQueue := ring}))
  softirq
  _ ← liftPrefix (branch .encWorkerConsumed item.isSome)
  match item with
  | none => return false
  | some first =>
    let some headId := first.head? | liftPrefix (invariant "an empty ring item")
    let head ← liftWGObserver (getTxSkbPrefix headId)
    let mut state := PacketState.crypted
    for id in first do
      _ ← liftPrefix (branch .encWorkerSkbIterate true)
      let encrypted ← encryptPacketPrefix checksumHelp head.keypair (← liftWGObserver (getTxSkbPrefix id))
      if ← liftPrefix (branch .encWorkerEncrypted encrypted.isSome) then
        liftWGObserver (setTxSkbPrefix id fun p => {p with bytes := encrypted.getD []})
      else
        state := .dead
        break
    if state == .crypted then _ ← liftPrefix (branch .encWorkerSkbIterate false)
    liftWGObserver (enqueuePerPeerTxPrefix first state)
    return true

def encryptIterPrefix (checksumHelp : Packet → PrefixM LifetimeEvent Packet) (softirq : PrefixM LifetimeEvent Unit)
    (needResched : PrefixM LifetimeEvent Bool) : PrefixM LifetimeEvent IterResult :=
  workerIterPrefix .encryptWorker none (encryptStepPrefix checksumHelp softirq)
    (do liftPrefix (branch .encWorkerNeedResched (← needResched)))

theorem encryptPacketPrefix_erases
    (hc : ∀ pkt, ErasesPrefix (checksum pkt) (originalChecksum pkt)) (kp : KeypairId) (pkt : DataPacket) :
    ErasesPrefix (encryptPacketPrefix checksum kp pkt) (encryptPacket originalChecksum kp pkt) := by
  unfold encryptPacketPrefix encryptPacket
  repeat' first
    | exact hc _
    | exact liftWGObserver_erases (getKeypairPrefix_erases _)
    | exact liftWGObserver_erases (erasesStatePrefix_lift _)
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | apply erasesPrefix_ite
    | split
    | (intro x; try dsimp only)

theorem encryptStepPrefix_erases
    (hc : ∀ pkt, ErasesPrefix (checksum pkt) (originalChecksum pkt))
    (hs : ErasesPrefix softirq originalSoftirq) :
    ErasesPrefix (encryptStepPrefix checksum softirq) (encryptStep originalChecksum originalSoftirq) := by
  unfold encryptStepPrefix encryptStep encryptRingPoll
  simp only [bind_assoc, pure_bind]
  apply erasesPrefix_bind (liftWGObserver_erases (erasesStatePrefix_lift getDev))
  intro dev
  generalize hconsume : dev.encryptQueue.consume = consumed
  rcases consumed with ⟨item, ring⟩
  apply erasesPrefix_bind (liftWGObserver_erases (erasesStatePrefix_lift _))
  intro _
  apply erasesPrefix_bind hs
  intro _
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro _
  cases item with
  | none => exact erasesPrefix_pure _
  | some first =>
    dsimp only
    cases he : first.head? with
    | none => exact erasesPrefix_lift _
    | some headId =>
      repeat' first
        | with_reducible exact encryptPacketPrefix_erases hc _ _
        | (maintenance_head enqueuePerPeerTxPrefix; exact liftWGObserver_erases (enqueuePerPeerTxPrefix_erases _ _))
        | (maintenance_head getTxSkbPrefix; exact liftWGObserver_erases (getTxSkbPrefix_erases _))
        | (maintenance_head setTxSkbPrefix; exact liftWGObserver_erases (setTxSkbPrefix_erases _ _))
        | with_reducible exact erasesPrefix_lift _
        | with_reducible exact erasesPrefix_pure _
        | with_reducible apply erasesPrefix_forIn
        | with_reducible apply erasesPrefix_bind
        | with_reducible apply erasesPrefix_ite
        | (with_reducible split)
        | (with_reducible intro x; try dsimp only)

theorem encryptIterPrefix_erases
    (hc : ∀ pkt, ErasesPrefix (checksum pkt) (originalChecksum pkt))
    (hs : ErasesPrefix softirq originalSoftirq) (hr : ErasesPrefix needResched originalResched) :
    ErasesPrefix (encryptIterPrefix checksum softirq needResched)
      (encryptIter originalChecksum originalSoftirq originalResched) := by
  apply workerIterPrefix_erases
  · exact encryptStepPrefix_erases hc hs
  · exact erasesPrefix_bind hr (fun _ => erasesPrefix_lift _)

theorem encryptPacketPrefix_spec_ambient (c : ProductAmbientContracts I) (P : IdentityView → Prop)
    (hc : ∀ pkt, ProductAmbientSpec I P (checksum pkt) (fun _ => P)) (kp : KeypairId) (pkt : DataPacket) :
    ProductAmbientSpec I P (encryptPacketPrefix checksum kp pkt) (fun _ => P) := by
  unfold encryptPacketPrefix
  repeat' first
    | exact hc _
    | exact c.getKeypair_frame P _
    | exact c.branch P _ _
    | exact c.ambient P (AmbientM.skipCut _)
    | exact c.nativeStore P _ ((calculateSkbPadding_sameWGWorld _ _).of_factor wgStoreView wgStoreView (fun _ => rfl))
    | exact c.ambient P (AmbientM.hiddenAlloc _)
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem encryptPacketPrefix_preserves_ambient (c : ProductAmbientContracts I)
    (hc : ∀ pkt, PrefixPreserves I LifetimeEvent.Safe (checksum pkt)) (kp : KeypairId) (pkt : DataPacket) :
    PrefixPreserves I LifetimeEvent.Safe (encryptPacketPrefix checksum kp pkt) := by
  apply ProductAmbientContracts.drop (encryptPacketPrefix_spec_ambient c (fun _ => True) ?_ kp pkt)
  intro p
  exact PrefixEnsures.consequence
    (show PrefixEnsures I LifetimeEvent.Safe (checksum p) (fun _ => I) from hc p)
    (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩)

/-- Replacement by the ring returned from consume is a separate contract from
the staging contract's produce update. No ring geometry is required here. -/
theorem encryptStepPrefix_preserves_ambient (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (hq : ∀ ring : PtrRing (List SkbId), PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with encryptQueue := ring}))))
    (hc : ∀ pkt, PrefixPreserves I LifetimeEvent.Safe (checksum pkt))
    (hs : PrefixPreserves I LifetimeEvent.Safe softirq) :
    PrefixPreserves I LifetimeEvent.Safe (encryptStepPrefix checksum softirq) := by
  unfold encryptStepPrefix
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.nativeStore (fun _ => True) getDev getDev_sameWGStore))
  intro dev
  generalize hconsume : dev.encryptQueue.consume = consumed
  rcases consumed with ⟨item, ring⟩
  apply PrefixPreserves.bind (hq ring)
  intro _
  apply PrefixPreserves.bind hs
  intro _
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro _
  cases item with
  | none => exact PrefixPreserves.pure c.safe _
  | some first =>
    dsimp only
    cases he : first.head? with
    | none => exact ProductAmbientContracts.drop (c.invariant (fun _ => True) _)
    | some headId =>
      repeat' first
        | with_reducible exact encryptPacketPrefix_preserves_ambient c hc _ _
        | with_reducible exact enqueuePerPeerTxPrefix_preserves_product c t _ _
        | with_reducible exact ProductAmbientContracts.drop (t.get (fun _ => True) _)
        | with_reducible exact ProductAmbientContracts.drop (t.set (fun _ => True) _ _)
        | with_reducible exact ProductAmbientContracts.drop (c.branch (fun _ => True) _ _)
        | with_reducible exact PrefixPreserves.pure c.safe _
        | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
        | with_reducible apply PrefixPreserves.bind
        | with_reducible apply PrefixPreserves.ite
        | (with_reducible split)
        | (with_reducible intro x; try dsimp only)

theorem encryptIterPrefix_preserves_ambient (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (hq : ∀ ring : PtrRing (List SkbId), PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with encryptQueue := ring}))))
    (hc : ∀ pkt, PrefixPreserves I LifetimeEvent.Safe (checksum pkt))
    (hs : PrefixPreserves I LifetimeEvent.Safe softirq)
    (hr : PrefixPreserves I LifetimeEvent.Safe needResched) :
    PrefixPreserves I LifetimeEvent.Safe (encryptIterPrefix checksum softirq needResched) := by
  apply workerIterPrefix_preserves _ _ c.safe
    (encryptStepPrefix_preserves_ambient c t hq hc hs)
  exact PrefixPreserves.bind hr (fun _ => ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))

theorem encryptQueue_allocation (ring : PtrRing (List SkbId)) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with encryptQueue := ring}))) := by
  apply PrefixEnsures.preserves
  apply StatePrefixEnsures.liftWGObserver (P := fun h w _ => AllocationInv h w)
    (Q := fun _ h w _ => AllocationInv h w)
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  apply hi.congr
  · cases hr
    unfold identityView Peers.snapshot keypairResidents packetResidents
    simp [Option.bind_map, Function.comp_def]
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (metadata_modifyDev (fun d => {d with encryptQueue := ring}) (fun _ => rfl))
      w ambient x v ambient' hr

theorem encryptPacketPrefix_allocation (kp : KeypairId) (pkt : DataPacket) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe
      (encryptPacketPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p)) kp pkt) :=
  ProductAmbientContracts.drop (encryptPacketPrefix_spec_ambient (ProductAmbientContracts.ofNative allocationAmbient) (fun _ => True)
    (fun p => (ProductAmbientContracts.ofNative allocationAmbient).store _ _ ((checksumHelp_sameWorld p).of_factor productStoreView productStoreView (fun _ => rfl))) kp pkt)

theorem encryptStepPrefix_allocation
    (hs : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe softirq) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe
      (encryptStepPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p)) softirq) :=
  encryptStepPrefix_preserves_ambient (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) encryptQueue_allocation
    (fun p => ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store _ _ ((checksumHelp_sameWorld p).of_factor productStoreView productStoreView (fun _ => rfl)))) hs

theorem encryptIterPrefix_allocation
    (hs : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe softirq)
    (hr : PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe needResched) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe
      (encryptIterPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p)) softirq needResched) :=
  encryptIterPrefix_preserves_ambient (ProductAmbientContracts.ofNative allocationAmbient) (ProductTxContracts.ofNative allocationTx) encryptQueue_allocation
    (fun p => ProductAmbientContracts.drop ((ProductAmbientContracts.ofNative allocationAmbient).store _ _ ((checksumHelp_sameWorld p).of_factor productStoreView productStoreView (fun _ => rfl)))) hs hr

end Leanux.Proofs.WG.Lifetimes
