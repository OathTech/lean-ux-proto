import Leanux.Proofs.WG.Lifetimes.TxEnqueue
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

def encryptPacketPrefix (checksumHelp : Packet → MixedM Packet)
    (keypair : KeypairId) (pkt : DataPacket) : MixedM (Option (List UInt8)) := do
  liftPrefix (skipCut [.flowHashSecret])
  let len := pkt.plaintext.bytes.length
  let paddingLen ← liftPrefix (calculateSkbPadding len pkt.plaintext.mtu)
  if ← liftPrefix (branch .encCowHeadFailed !(← liftPrefix (hiddenAlloc .skbCowHead))) then return none
  let mut inner := pkt.plaintext
  if ← liftPrefix (branch .encChecksumPartial inner.csum.isSome) then
    if ← liftPrefix (branch .encChecksumHelpFailed !(← liftPrefix (hiddenAlloc .skbChecksumHelp))) then return none
    inner ← checksumHelp inner
  let cowOk ← liftPrefix (hiddenAlloc .skbCowDataTx)
  if ← liftPrefix (branch .encCowDataFailed !cowOk) then return none
  if ← liftPrefix (branch .encTooManyFrags false) then return none
  let k ← getKeypairPrefix keypair
  if ← liftPrefix (branch .encSgvecFailed false) then return none
  return some (dataMessage k.remoteIndex pkt.nonce k.sending.key
    (inner.bytes ++ List.replicate paddingLen 0))

def encryptStepPrefix (checksumHelp : Packet → MixedM Packet) (softirq : MixedM Unit) : MixedM Bool := do
  softirq
  match (← liftPrefix getDev).encryptQueue.consume with
  | (none, _) =>
    _ ← liftPrefix (branch .encWorkerConsumed false)
    return false
  | (some first, ring) =>
    _ ← liftPrefix (branch .encWorkerConsumed true)
    liftPrefix (modifyDev fun d => {d with encryptQueue := ring})
    let some headId := first.head? | liftPrefix (invariant "an empty ring item")
    let head ← getTxSkbPrefix headId
    let mut state := PacketState.crypted
    for id in first do
      _ ← liftPrefix (branch .encWorkerSkbIterate true)
      let encrypted ← encryptPacketPrefix checksumHelp head.keypair (← getTxSkbPrefix id)
      if ← liftPrefix (branch .encWorkerEncrypted encrypted.isSome) then
        setTxSkbPrefix id fun p => {p with bytes := encrypted.getD []}
      else
        state := .dead
        break
    if state == .crypted then _ ← liftPrefix (branch .encWorkerSkbIterate false)
    enqueuePerPeerTxPrefix first state
    return true

def encryptIterPrefix (checksumHelp : Packet → MixedM Packet) (softirq : MixedM Unit)
    (needResched : MixedM Bool) : MixedM IterResult :=
  workerIterPrefix .encryptWorker none (encryptStepPrefix checksumHelp softirq)
    (do liftPrefix (branch .encWorkerNeedResched (← needResched)))

theorem encryptPacketPrefix_erases
    (hc : ∀ pkt, ErasesPrefix (checksum pkt) (originalChecksum pkt)) (kp : KeypairId) (pkt : DataPacket) :
    ErasesPrefix (encryptPacketPrefix checksum kp pkt) (encryptPacket originalChecksum kp pkt) := by
  unfold encryptPacketPrefix encryptPacket
  repeat' first
    | exact hc _
    | exact getKeypairPrefix_erases _
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
  unfold encryptStepPrefix encryptStep
  apply erasesPrefix_bind hs
  intro _
  apply erasesPrefix_bind (erasesPrefix_lift getDev)
  intro dev
  generalize hconsume : dev.encryptQueue.consume = consumed
  rcases consumed with ⟨item, ring⟩
  cases item with
  | none =>
    exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _)
  | some first =>
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    cases he : first.head? with
    | none => exact erasesPrefix_lift _
    | some headId =>
      repeat' first
        | exact encryptPacketPrefix_erases hc _ _
        | exact enqueuePerPeerTxPrefix_erases _ _
        | exact getTxSkbPrefix_erases _
        | exact setTxSkbPrefix_erases _ _
        | exact erasesPrefix_lift _
        | exact erasesPrefix_pure _
        | apply erasesPrefix_forIn
        | apply erasesPrefix_bind
        | apply erasesPrefix_ite
        | split
        | (intro x; try dsimp only)

theorem encryptIterPrefix_erases
    (hc : ∀ pkt, ErasesPrefix (checksum pkt) (originalChecksum pkt))
    (hs : ErasesPrefix softirq originalSoftirq) (hr : ErasesPrefix needResched originalResched) :
    ErasesPrefix (encryptIterPrefix checksum softirq needResched)
      (encryptIter originalChecksum originalSoftirq originalResched) := by
  apply workerIterPrefix_erases
  · exact encryptStepPrefix_erases hc hs
  · exact erasesPrefix_bind hr (fun _ => erasesPrefix_lift _)

theorem encryptPacketPrefix_spec_ambient (c : AmbientContracts I) (P : IdentityView → Prop)
    (hc : ∀ pkt, AmbientSpec I P (checksum pkt) (fun _ => P)) (kp : KeypairId) (pkt : DataPacket) :
    AmbientSpec I P (encryptPacketPrefix checksum kp pkt) (fun _ => P) := by
  unfold encryptPacketPrefix
  repeat' first
    | exact hc _
    | exact c.getKeypair_frame P _
    | exact c.branch P _ _
    | exact c.kernel P _ (skipCut_sameKernel _)
    | exact c.kernel P _ (calculateSkbPadding_sameKernel _ _)
    | exact c.kernel P _ (hiddenAlloc_sameKernel _)
    | exact c.pure P _
    | apply PrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem encryptPacketPrefix_preserves_ambient (c : AmbientContracts I)
    (hc : ∀ pkt, PrefixPreserves I LifetimeEvent.Safe (checksum pkt)) (kp : KeypairId) (pkt : DataPacket) :
    PrefixPreserves I LifetimeEvent.Safe (encryptPacketPrefix checksum kp pkt) := by
  apply AmbientContracts.drop (encryptPacketPrefix_spec_ambient c (fun _ => True) ?_ kp pkt)
  intro p
  exact PrefixEnsures.consequence
    (show PrefixEnsures I LifetimeEvent.Safe (checksum p) (fun _ => I) from hc p)
    (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩)

/-- Replacement by the ring returned from consume is a separate contract from
the staging contract's produce update. No ring geometry is required here. -/
theorem encryptStepPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (hq : ∀ ring : PtrRing (List SkbId), PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with encryptQueue := ring})))
    (hc : ∀ pkt, PrefixPreserves I LifetimeEvent.Safe (checksum pkt))
    (hs : PrefixPreserves I LifetimeEvent.Safe softirq) :
    PrefixPreserves I LifetimeEvent.Safe (encryptStepPrefix checksum softirq) := by
  unfold encryptStepPrefix
  apply PrefixPreserves.bind hs
  intro _
  apply PrefixPreserves.bind (AmbientContracts.drop (c.kernel (fun _ => True) getDev getDev_sameKernel))
  intro dev
  split
  all_goals repeat' first
    | exact hq _
    | exact encryptPacketPrefix_preserves_ambient c hc _ _
    | exact enqueuePerPeerTxPrefix_preserves_ambient c t _ _
    | exact AmbientContracts.drop (t.get (fun _ => True) _)
    | exact AmbientContracts.drop (t.set (fun _ => True) _ _)
    | exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | exact PrefixPreserves.pure c.safe _
    | apply PrefixPreserves.forIn _ _ _ c.safe
    | apply PrefixPreserves.bind
    | split
    | (intro x; try dsimp only)

theorem encryptIterPrefix_preserves_ambient (c : AmbientContracts I) (t : TxContracts I)
    (hq : ∀ ring : PtrRing (List SkbId), PrefixPreserves I LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with encryptQueue := ring})))
    (hc : ∀ pkt, PrefixPreserves I LifetimeEvent.Safe (checksum pkt))
    (hs : PrefixPreserves I LifetimeEvent.Safe softirq)
    (hr : PrefixPreserves I LifetimeEvent.Safe needResched) :
    PrefixPreserves I LifetimeEvent.Safe (encryptIterPrefix checksum softirq needResched) := by
  apply workerIterPrefix_preserves _ _ c.safe
    (encryptStepPrefix_preserves_ambient c t hq hc hs)
  exact PrefixPreserves.bind hr (fun _ => AmbientContracts.drop (c.branch (fun _ => True) _ _))

theorem encryptQueue_allocation (ring : PtrRing (List SkbId)) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with encryptQueue := ring})) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  apply hi.congr
  · cases hr
    unfold identityView Peers.snapshot keypairResidents packetResidents
    simp [Option.bind_map, Function.comp_def]
  · exact metadata_modifyDev (fun d => {d with encryptQueue := ring}) (fun _ => rfl) w x v hr

theorem encryptPacketPrefix_allocation (kp : KeypairId) (pkt : DataPacket) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (encryptPacketPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p)) kp pkt) :=
  AmbientContracts.drop (encryptPacketPrefix_spec_ambient allocationAmbient (fun _ => True)
    (fun p => allocationAmbient.kernel _ _ (checksumHelp_sameKernel p)) kp pkt)

theorem encryptStepPrefix_allocation
    (hs : PrefixPreserves AllocationInv LifetimeEvent.Safe softirq) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (encryptStepPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p)) softirq) :=
  encryptStepPrefix_preserves_ambient allocationAmbient allocationTx encryptQueue_allocation
    (fun p => AmbientContracts.drop (allocationAmbient.kernel _ _ (checksumHelp_sameKernel p))) hs

theorem encryptIterPrefix_allocation
    (hs : PrefixPreserves AllocationInv LifetimeEvent.Safe softirq)
    (hr : PrefixPreserves AllocationInv LifetimeEvent.Safe needResched) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (encryptIterPrefix (fun p => liftPrefix (Leanux.Env.checksumHelp p)) softirq needResched) :=
  encryptIterPrefix_preserves_ambient allocationAmbient allocationTx encryptQueue_allocation
    (fun p => AmbientContracts.drop (allocationAmbient.kernel _ _ (checksumHelp_sameKernel p))) hs hr

end Leanux.Proofs.WG.Lifetimes
