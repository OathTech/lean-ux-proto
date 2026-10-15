import Leanux.Proofs.WG.Keypairs.SessionOrigin
import Leanux.Proofs.WG.Packets.AffiliationCuts
import Leanux.Proofs.WG.Queues.RxWorkerCuts

/-! Actual RX allocation and stored-packet/decrypt receipts. Allocation is
observed before enqueue, so ENOSPC cleanup or a later Stop cannot erase its
history. Decryption captures the original stored getter and call once; its
input is that occurrence's complete record, not assumed allocation ciphertext. -/
namespace Leanux.Proofs.WG.RxOrigin
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes MaterialOrigin
open Leanux.Proofs.Framing Std.Do
set_option pp.structureInstances false

/-- The original getter and decrypt call, retaining the actual input record. -/
def readDecrypt (id : SkbId) : M (RxPacket × Option RxPacket) := do
  let pkt ← getRxSkb id
  let result ← decryptPacket pkt
  return (pkt, result)

def readDecryptPrefix (id : SkbId) : MixedM (RxPacket × Option RxPacket) := do
  let pkt ← getRxSkbPrefix id
  let result ← decryptPacketPrefix pkt
  return (pkt, result)

theorem readDecrypt_erases (id : SkbId) : ErasesPrefix (readDecryptPrefix id) (readDecrypt id) :=
  erasesPrefix_bind (getRxSkbPrefix_erases id) fun pkt =>
    erasesPrefix_bind (decryptPacketPrefix_erases pkt) fun _ => erasesPrefix_pure _

theorem readDecrypt_allocation (id : SkbId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (readDecryptPrefix id) :=
  PrefixPreserves.bind (AmbientContracts.drop (allocationAmbient.getRx (fun _ => True) id)) fun pkt =>
    PrefixPreserves.bind (decryptPacketPrefix_allocation pkt) fun _ => PrefixPreserves.pure allocationAmbient.safe _

structure Admission where
  packet : RxPacket
  slot : SkbId

def admitWith {m : Type → Type} [Monad m]
    (lookup : List IndexKind → Nat → m (Option (IndexOwner × PeerId)))
    (keyGet : Option KeypairId → m (Option KeypairId)) (read : PeerId → m Peer)
    (keyPut : Option KeypairId → Bool → m Unit) (peerPut : Option PeerId → m Unit)
    (newRx : RxPacket → m SkbId)
    (step : {α : Type} → M α → m α)
    (msg : List UInt8) (src : SkbSource) (ds : Nat) : m (Option Admission) := do
  let entry ← lookup [.keypair] (u32le msg 4)
  let (keypair, peer) ← match entry with
    | none => pure (none, none)
    | some (IndexOwner.keypair kp, pid) => pure (some kp, some pid)
    | some (IndexOwner.handshake _, _) => step (invariant "a handshake entry under the keypair mask")
  let kp ← match keypair with
    | none => do step keypairGetCurrent; pure none
    | some kp => keyGet (some kp)
  if ← step (branch .dataNoKeypair kp.isNone) then
    peerPut peer
    return none
  let some id := kp | step (invariant "unreachable")
  let some pid := peer | step (invariant "a keypair entry without a peer")
  if ← step (branch .dataPeerDead (← read pid).isDead) then
    keyPut (some id) false
    peerPut peer
    return none
  let packet : RxPacket := {peer := pid, keypair := id, bytes := msg, source := src, ds}
  let skb ← newRx packet
  return some ⟨packet, skb⟩

def admitSource (msg : List UInt8) (src : SkbSource) (ds : Nat) : M (Option Admission) :=
  admitWith indexLookup keypairGet getPeer keypairPut WG.peerPut newRxSkb (fun a => a) msg src ds

def admitPrefix (msg : List UInt8) (src : SkbSource) (ds : Nat) : MixedM (Option Admission) :=
  admitWith indexLookupPrefix keypairGetPrefix getPeerMixed keypairPutPrefix peerPutMixed newRxSkbPrefix liftPrefix msg src ds

inductive Receipt where
  | allocation (packet : RxPacket) (run : RunWitness SkbId)
  | admission (msg : List UInt8) (src : SkbSource) (ds : Nat) (run : RunWitness (Option Admission))
  | decrypt (id : SkbId) (run : RunWitness (RxPacket × Option RxPacket))

def Receipt.Valid : Receipt → Prop
  | .allocation pkt r => r.Valid (newRxSkb pkt)
  | .admission msg src ds r => r.Valid (admitSource msg src ds)
  | .decrypt id r => r.Valid (readDecrypt id)

abbrev Journal := PrefixM (Event Receipt)

def allocate (pkt : RxPacket) : Journal SkbId :=
  receiptObserved (access (newRxSkbPrefix pkt)) (Event.receipt ∘ Receipt.allocation pkt)

def decrypt (id : SkbId) : Journal (RxPacket × Option RxPacket) :=
  receiptObserved (access (readDecryptPrefix id)) (Event.receipt ∘ Receipt.decrypt id)

def admitRaw (msg : List UInt8) (src : SkbSource) (ds : Nat) : Journal (Option Admission) :=
  admitWith (fun mask i => access (indexLookupPrefix mask i)) (fun k => access (keypairGetPrefix k))
    (fun p => access (getPeerMixed p)) (fun k b => access (keypairPutPrefix k b))
    (fun p => access (peerPutMixed p)) allocate liftPrefix msg src ds

def observeAdmission (msg : List UInt8) (src : SkbSource) (ds : Nat) : Journal (Option Admission) :=
  receiptObserved (admitRaw msg src ds) (Event.receipt ∘ Receipt.admission msg src ds)

def finishWith {m : Type → Type} [Monad m]
    (keyPut : Option KeypairId → Bool → m Unit) (peerPut : Option PeerId → m Unit)
    (enqueue : SkbId → m Int) (publish : SkbId → m Unit) (free : SkbId → m Unit)
    (step : {α : Type} → M α → m α) (a : Admission) : m Unit := do
  let ret ← enqueue a.slot
  if ← step (branch .dataEpipe (ret == -EPIPE)) then publish a.slot
  if ← step (WG.orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
  keyPut (some a.packet.keypair) false
  peerPut (some a.packet.peer)
  free a.slot

def consumeWith {m : Type → Type} [Monad m]
    (front : m (Option Admission)) (keyPut : Option KeypairId → Bool → m Unit)
    (peerPut : Option PeerId → m Unit) (enqueue : SkbId → m Int)
    (publish : SkbId → m Unit) (free : SkbId → m Unit)
    (step : {α : Type} → M α → m α) : m Unit := do
  match ← front with
  | none => return
  | some a => finishWith keyPut peerPut enqueue publish free step a

def consumeSource (msg : List UInt8) (src : SkbSource) (ds : Nat) : M Unit :=
  consumeWith (admitSource msg src ds) keypairPut WG.peerPut enqueuePerDeviceAndPeerRx
    (fun id => enqueuePerPeerRx (pure ()) id .dead) freeRxSkb (fun a => a)

def consumePrefix (msg : List UInt8) (src : SkbSource) (ds : Nat) : MixedM Unit :=
  consumeWith (admitPrefix msg src ds) keypairPutPrefix peerPutMixed enqueuePerDeviceAndPeerRxPrefix
    (fun id => enqueuePerPeerRxPrefix (pure ()) id .dead) freeRxSkbPrefix liftPrefix

def consume (msg : List UInt8) (src : SkbSource) (ds : Nat) : Journal Unit :=
  consumeWith (observeAdmission msg src ds) (fun k b => access (keypairPutPrefix k b))
    (fun p => access (peerPutMixed p)) (fun id => access (enqueuePerDeviceAndPeerRxPrefix id))
    (fun id => access (enqueuePerPeerRxPrefix (pure ()) id .dead)) (fun id => access (freeRxSkbPrefix id)) liftPrefix

theorem consumeSource_eq (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    consumeSource msg src ds = consumeData msg src ds := by
  unfold consumeSource consumeWith finishWith admitSource admitWith consumeData
  simp only [bind_assoc, pure_bind]
  repeat' first
    | rfl
    | with_reducible apply Queues.RxWorkers.bind_congr
    | intro_forall
    | (split <;> try simp_all only [bind_assoc, pure_bind, Bool.not_eq_true, Bool.not_eq_false])
    | simp only [bind_assoc, pure_bind]

theorem consumePrefix_eq (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    consumePrefix msg src ds = consumeDataPrefix msg src ds := by
  unfold consumePrefix consumeWith finishWith admitPrefix admitWith consumeDataPrefix
  simp only [bind_assoc, pure_bind]
  repeat' first
    | rfl
    | with_reducible apply Queues.RxWorkers.bind_congr
    | intro_forall
    | (split <;> try simp_all only [bind_assoc, pure_bind, Bool.not_eq_true, Bool.not_eq_false])
    | simp only [bind_assoc, pure_bind]

theorem allocate_erases (pkt : RxPacket) : ErasesPrefix (allocate pkt) (newRxSkb pkt) :=
  receipt_erases (access_erases (PacketAllocation.erases (.rx pkt))) _

theorem admitRaw_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesPrefix (admitRaw msg src ds) (admitSource msg src ds) := by
  unfold admitRaw admitSource admitWith
  repeat' first
    | with_reducible exact access_erases (indexLookupPrefix_erases _ _)
    | with_reducible exact access_erases (keypairGetPrefix_erases _)
    | with_reducible exact access_erases (getPeerMixed_erases _)
    | with_reducible exact access_erases (keypairPutPrefix_erases _ _)
    | with_reducible exact access_erases (peerPutMixed_erases _)
    | with_reducible exact allocate_erases _
    | with_reducible exact access_erases (enqueuePerDeviceAndPeerRxPrefix_erases _)
    | with_reducible exact access_erases (enqueuePerPeerRxPrefix_erases (erasesPrefix_pure ()) _ _)
    | with_reducible exact access_erases (freeRxSkbPrefix_erases _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (intro_forall; try dsimp only)
    | split

theorem admit_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesPrefix (observeAdmission msg src ds) (admitSource msg src ds) :=
  receipt_erases (admitRaw_erases msg src ds) _

theorem consume_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesPrefix (consume msg src ds) (consumeData msg src ds) := by
  rw [← consumeSource_eq]
  unfold consume consumeSource consumeWith finishWith
  repeat' first
    | with_reducible exact admit_erases _ _ _
    | with_reducible exact access_erases (indexLookupPrefix_erases _ _)
    | with_reducible exact access_erases (keypairGetPrefix_erases _)
    | with_reducible exact access_erases (getPeerMixed_erases _)
    | with_reducible exact access_erases (keypairPutPrefix_erases _ _)
    | with_reducible exact access_erases (peerPutMixed_erases _)
    | with_reducible exact allocate_erases _
    | with_reducible exact access_erases (enqueuePerDeviceAndPeerRxPrefix_erases _)
    | with_reducible exact access_erases (enqueuePerPeerRxPrefix_erases (erasesPrefix_pure ()) _ _)
    | with_reducible exact access_erases (freeRxSkbPrefix_erases _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (intro_forall; try dsimp only)
    | split

theorem allocate_valid (pkt : RxPacket) :
    PrefixPreserves (fun h _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (allocate pkt) :=
  receipt_valid (access_erases (PacketAllocation.erases (.rx pkt))) (access_valid _ _) _ (fun _ hr => hr)

theorem admitRaw_valid (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves (fun h _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (admitRaw msg src ds) := by
  unfold admitRaw admitWith
  repeat' first
    | with_reducible exact access_valid _ _
    | with_reducible exact allocate_valid _
    | with_reducible exact valid_lift Receipt.Valid _
    | with_reducible exact valid_pure Receipt.Valid _
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

theorem admit_valid (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves (fun h _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (observeAdmission msg src ds) :=
  receipt_valid (admitRaw_erases msg src ds) (admitRaw_valid msg src ds)
    (Receipt.admission msg src ds) (fun _ hr => hr)

theorem consume_valid (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves (fun h _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (consume msg src ds) := by
  unfold consume consumeWith finishWith
  repeat' first
    | with_reducible exact admit_valid _ _ _
    | with_reducible exact access_valid _ _
    | with_reducible exact allocate_valid _
    | with_reducible exact valid_lift Receipt.Valid _
    | with_reducible exact valid_pure Receipt.Valid _
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

/-- The same stored getter/decrypt cut is used by the original worker, before
its branch, payload write and state-only publication. -/
def prepareWith {m : Type → Type} [Monad m]
    (runDecrypt : SkbId → m (RxPacket × Option RxPacket))
    (store : SkbId → (RxPacket → RxPacket) → m Unit)
    (publish : SkbId → PacketState → m PeerId)
    (step : {α : Type} → M α → m α) : m (Option PeerId) := do
  match (← step getDev).decryptQueue.consume with
  | (none, _) =>
    _ ← step (branch .decWorkerConsumed false)
    return none
  | (some id, ring) =>
    _ ← step (branch .decWorkerConsumed true)
    step (modifyDev fun d => {d with decryptQueue := ring})
    let (_, decrypted) ← runDecrypt id
    if ← step (branch .decWorkerDecrypted decrypted.isSome) then
      let some d := decrypted | step (invariant "unreachable")
      store id fun _ => d
      return some (← publish id .crypted)
    else return some (← publish id .dead)

def prepare : Journal (Option PeerId) :=
  prepareWith decrypt (fun id f => access (setRxSkbPrefix id f))
    (fun id state => access (Queues.RxWorkers.publishPrefix id state)) liftPrefix

theorem prepareSource_factor : Queues.RxWorkers.prepareSource =
    prepareWith readDecrypt setRxSkb Queues.RxWorkers.publishSource (fun a => a) := by
  unfold Queues.RxWorkers.prepareSource prepareWith readDecrypt
  simp only [bind_assoc, pure_bind]
  rfl

theorem preparePrefix_factor : Queues.RxWorkers.preparePrefix =
    prepareWith readDecryptPrefix setRxSkbPrefix Queues.RxWorkers.publishPrefix liftPrefix := by
  unfold Queues.RxWorkers.preparePrefix prepareWith readDecryptPrefix
  simp only [bind_assoc, pure_bind]
  rfl

theorem decrypt_erases (id : SkbId) : ErasesPrefix (decrypt id) (readDecrypt id) :=
  receipt_erases (access_erases (readDecrypt_erases id)) _

theorem prepare_erases : ErasesPrefix prepare Queues.RxWorkers.prepareSource := by
  rw [prepareSource_factor]
  unfold prepare prepareWith
  repeat' first
    | with_reducible exact decrypt_erases _
    | with_reducible exact access_erases (setRxSkbPrefix_erases _ _)
    | with_reducible exact access_erases (Queues.RxWorkers.publish_erases _ _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (intro_forall; try dsimp only)
    | split

theorem decrypt_valid (id : SkbId) :
    PrefixPreserves (fun h _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (decrypt id) :=
  receipt_valid (access_erases (readDecrypt_erases id)) (access_valid _ _) _ (fun _ hr => hr)

theorem prepare_valid :
    PrefixPreserves (fun h _ => Valid Receipt.Valid h) (Valid Receipt.Valid) prepare := by
  unfold prepare prepareWith
  repeat' first
    | with_reducible exact access_valid _ _
    | with_reducible exact decrypt_valid _
    | with_reducible exact valid_lift Receipt.Valid _
    | with_reducible exact valid_pure Receipt.Valid _
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

theorem allocate_projects (pkt : RxPacket) :
    ProjectsUnder AllocationInv life? (allocate pkt) (newRxSkbPrefix pkt) :=
  receiptObserved_projectsUnder (fun _ => rfl) (access_projects (PacketAllocation.preserves (.rx pkt)))

theorem decrypt_projects (id : SkbId) :
    ProjectsUnder AllocationInv life? (decrypt id) (readDecryptPrefix id) :=
  receiptObserved_projectsUnder (fun _ => rfl) (access_projects (readDecrypt_allocation id))

theorem admit_allocation (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe (admitPrefix msg src ds) := by
  unfold admitPrefix admitWith
  repeat' first
    | with_reducible exact indexLookupPrefix_preserves_ambient allocationAmbient _ _
    | with_reducible exact keypairGetPrefix_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact keypairPutPrefix_allocation _ _
    | with_reducible exact peerPutMixed_allocation _
    | with_reducible exact PacketAllocation.preserves (.rx _)
    | with_reducible exact enqueuePerDeviceAndPeerRxPrefix_allocation _
    | with_reducible exact enqueuePerPeerRxPrefix_allocation (PrefixPreserves.pure allocationAmbient.safe ()) _ _
    | with_reducible exact freeRxSkbPrefix_allocation _
    | with_reducible exact allocation_kernel _ keypairGetCurrent_sameKernel
    | with_reducible exact allocation_kernel _ (sameKernel_branch _ _)
    | with_reducible exact allocation_kernel _ (orM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

theorem admitRaw_projects (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ProjectsUnder AllocationInv life? (admitRaw msg src ds) (admitPrefix msg src ds) := by
  unfold admitRaw admitPrefix admitWith
  repeat' first
    | with_reducible exact allocate_projects _
    | with_reducible apply access_projects
    | with_reducible exact indexLookupPrefix_preserves_ambient allocationAmbient _ _
    | with_reducible exact keypairGetPrefix_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact keypairPutPrefix_allocation _ _
    | with_reducible exact peerPutMixed_allocation _
    | with_reducible exact PacketAllocation.preserves (.rx _)
    | with_reducible exact enqueuePerDeviceAndPeerRxPrefix_allocation _
    | with_reducible exact enqueuePerPeerRxPrefix_allocation (PrefixPreserves.pure allocationAmbient.safe ()) _ _
    | with_reducible exact freeRxSkbPrefix_allocation _
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact allocation_kernel _ keypairGetCurrent_sameKernel
    | with_reducible exact allocation_kernel _ (sameKernel_branch _ _)
    | with_reducible exact allocation_kernel _ (orM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

theorem admit_projects (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ProjectsUnder AllocationInv life? (observeAdmission msg src ds) (admitPrefix msg src ds) :=
  receiptObserved_projectsUnder (fun _ => rfl) (admitRaw_projects msg src ds)

theorem consume_projects (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ProjectsUnder AllocationInv life? (consume msg src ds) (consumeDataPrefix msg src ds) := by
  rw [← consumePrefix_eq]
  unfold consume consumePrefix consumeWith finishWith
  repeat' first
    | with_reducible exact admit_projects _ _ _
    | with_reducible exact admit_allocation _ _ _
    | with_reducible exact allocate_projects _
    | with_reducible apply access_projects
    | with_reducible exact indexLookupPrefix_preserves_ambient allocationAmbient _ _
    | with_reducible exact keypairGetPrefix_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact keypairPutPrefix_allocation _ _
    | with_reducible exact peerPutMixed_allocation _
    | with_reducible exact PacketAllocation.preserves (.rx _)
    | with_reducible exact enqueuePerDeviceAndPeerRxPrefix_allocation _
    | with_reducible exact enqueuePerPeerRxPrefix_allocation (PrefixPreserves.pure allocationAmbient.safe ()) _ _
    | with_reducible exact freeRxSkbPrefix_allocation _
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact allocation_kernel _ keypairGetCurrent_sameKernel
    | with_reducible exact allocation_kernel _ (sameKernel_branch _ _)
    | with_reducible exact allocation_kernel _ (orM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _))
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

theorem prepare_projects :
    ProjectsUnder AllocationInv life? prepare Queues.RxWorkers.preparePrefix := by
  rw [preparePrefix_factor]
  unfold prepare prepareWith
  repeat' first
    | with_reducible exact decrypt_projects _
    | with_reducible apply access_projects
    | with_reducible exact readDecrypt_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.setRx (fun _ => True) _ _)
    | with_reducible exact Queues.RxWorkers.publish_preserves _ _
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact allocation_kernel _ getDev_sameKernel
    | with_reducible exact allocation_kernel _ (sameKernel_branch _ _)
    | with_reducible exact decryptQueue_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure allocationAmbient.safe _
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.bind
    | (intro_forall; try dsimp only)
    | split

/-- Exact allocation state, including the full packet and epoch/slot identity.
The receipt remains meaningful after a later enqueue failure and free. -/
theorem allocation_record (pkt : RxPacket) (r : RunWitness SkbId)
    (hr : r.Valid (newRxSkb pkt)) :
    ∃ d, r.before.k.wg = some d ∧ r.value = d.nextSkb ∧
      r.after = Packets.update r.before (fun v =>
        {v with rxSkbs := v.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1}) ∧
      packetStamp r.before r.value = (d.ifindex, d.nextSkb + 1) := by
  cases hd : r.before.k.wg with
  | none => simp [RunWitness.Valid, newRxSkb, getDev, getK, hd, invariant] at hr
  | some d =>
    have he := Packets.newRxSkb_run r.before d pkt hd
    have hh := he.symm.trans hr
    obtain ⟨hi, hv⟩ := (show d.nextSkb = r.value ∧ _ from by simpa using hh)
    exact ⟨d, rfl, hi.symm, hv.symm, by simp [packetStamp, hd, ← hi]⟩

/-- Every field other than nonce and bytes is retained by the actual successful
AEAD tail. In particular this is stronger than just peer/key scalar equality. -/
theorem receiveTail_record (pkt out : RxPacket) (k : Keypair) (w v : World)
    (hr : (KeyTimes.receiveTail pkt k).run w = .ok (some out, v)) :
    out = {pkt with nonce := u64le pkt.bytes 8, bytes := out.bytes} := by
  have hs : ⦃fun _ => ⌜True⌝⦄ KeyTimes.receiveTail pkt k
      ⦃⇓? result _ => ⌜∀ out, result = some out →
        out = {pkt with nonce := u64le pkt.bytes 8, bytes := out.bytes}⌝⦄ := by
    have ha := sameKernel_wp _ (hiddenAlloc_sameKernel .skbCowDataRx) (fun _ => True)
    mvcgen [KeyTimes.receiveTail, WG.orM, ha, branch, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  exact (hoare_iff_triple _ _ _).mpr hs w (some out) v trivial hr out rfl

theorem decryptPacket_record (pkt out : RxPacket) (w v : World)
    (hr : (decryptPacket pkt).run w = .ok (some out, v)) :
    out = {pkt with nonce := u64le pkt.bytes 8, bytes := out.bytes} := by
  rw [KeyTimes.decryptPacket_factor] at hr
  simp only [StateT.run_bind, CounterWindow.branch_run,
    CounterWindow.except_ok_bind, Bool.false_eq_true, ↓reduceIte] at hr
  cases hg : (getKeypair pkt.keypair).run (CounterWindow.record w .decNoKeypair false) with
  | error e => simp [hg] at hr
  | ok result =>
    rcases result with ⟨k, entered⟩
    simp only [hg, CounterWindow.except_ok_bind] at hr
    cases hj : (KeyTimes.receiveReject k).run entered with
    | error e => simp [hj] at hr
    | ok result =>
      rcases result with ⟨reject, checked⟩
      cases reject with
      | false =>
        simp only [hj, CounterWindow.except_ok_bind, Bool.false_eq_true, ↓reduceIte] at hr
        exact receiveTail_record pkt out k checked v hr
      | true =>
        simp only [StateT.run_bind, hj, CounterWindow.except_ok_bind, ↓reduceIte] at hr
        cases hp : (getKeypair pkt.keypair).run checked with
        | error e => simp [hp] at hr
        | ok result =>
          rcases result with ⟨fresh, updated⟩
          simp [hp, CounterWindow.setKeypair_run] at hr

/-- Successful stored-packet decryption ties the receipt to that exact packet
record and actual resident receiving key. Missing keys Stop; no credit or
single-decryption invariant is assumed. -/
theorem decrypt_receipt (id : SkbId) (r : RunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (hv : r.Valid (readDecrypt id)) (ho : r.value.2 = some out) :
    ∃ d k, r.before.k.wg = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
      d.keypairs[r.value.1.keypair]? = some k ∧ k.receiving.isValid = true ∧
      (decryptPacket r.value.1).run r.before = .ok (some out, r.after) ∧
      out = {r.value.1 with nonce := u64le r.value.1.bytes 8, bytes := out.bytes} ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le r.value.1.bytes 8))
        (r.value.1.bytes.drop 16) [] = some out.bytes := by
  unfold RunWitness.Valid readDecrypt at hv
  simp only [bind_ok] at hv
  obtain ⟨pkt, a, hp, result, b, hd, he⟩ := hv
  have ha : a = r.before ∧ ∃ d, r.before.k.wg = some d ∧ d.rxSkbs[id]? = some pkt := by
    cases hw : r.before.k.wg with
    | none => simp [getRxSkb, getDev, getK, hw, invariant] at hp
    | some dev =>
      cases found : dev.rxSkbs[id]? with
      | none => simp [getRxSkb, getDev, getK, hw, found, invariant] at hp
      | some actual =>
        have eqs : actual = pkt ∧ r.before = a := by simpa [getRxSkb, getDev, getK, hw, found] using hp
        exact ⟨eqs.2.symm, dev, rfl, eqs.1 ▸ found⟩
  obtain ⟨rfl, d, hw, hp⟩ := ha
  change (Except.ok ((pkt, result), b) : Except Stop _) = .ok (r.value, r.after) at he
  simp only [Except.ok.injEq, Prod.mk.injEq] at he
  have hin : pkt = r.value.1 := congrArg Prod.fst he.1
  have hout : result = some out := (congrArg Prod.snd he.1).trans ho
  subst pkt; subst result; rw [he.2] at hd
  obtain ⟨e, key, he, hk, valid, _⟩ := KeyTimes.decryptPacket_admission _ _ _ _ hd
  have ed : e = d := Option.some.inj (he.symm.trans hw)
  subst e
  obtain ⟨e, actual, he, hak, _, _, aead⟩ := Affiliation.decryptPacket_fields _ _ _ _ hd
  have ed : e = d := Option.some.inj (he.symm.trans hw)
  subst e
  have ek : actual = key := Option.some.inj (hak.symm.trans hk)
  subst actual
  exact ⟨d, key, hw, hp, hk, valid, hd, decryptPacket_record _ _ _ _ hd, aead⟩

/-- The literal publication setter changes only the state of its actual stored
record. The worker source factor locates this after the successful decrypt cut. -/
theorem publication_write (id : SkbId) (state : PacketState) (w : World) (d : Device)
    (pkt : RxPacket) (hd : w.k.wg = some d) (hp : d.rxSkbs[id]? = some pkt) :
    (setRxSkb id (fun q => {q with state})).run w =
      .ok ((), Packets.update w (fun v => {v with rxSkbs := v.rxSkbs.insert id {pkt with state}})) :=
  Packets.setRxSkb_run w d id pkt _ hd hp

/-- A named original admission front exposes the index result and nullable
key acquisition before the live-peer check and allocation. -/
theorem admitSource_factor (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    admitSource msg src ds = (do
      let entry ← indexLookup [.keypair] (u32le msg 4)
      let (kp, peer) ← Affiliation.receiveKeyAcquire entry
      if ← branch .dataNoKeypair kp.isNone then
        peerPut peer
        return none
      let some id := kp | invariant "unreachable"
      let some pid := peer | invariant "a keypair entry without a peer"
      if ← branch .dataPeerDead (← getPeer pid).isDead then
        keypairPut (some id) false
        peerPut peer
        return none
      let pkt : RxPacket := {peer := pid, keypair := id, bytes := msg, source := src, ds}
      return some ⟨pkt, ← newRxSkb pkt⟩) := by
  unfold admitSource admitWith
  apply Queues.RxWorkers.bind_congr
  intro entry
  cases entry with
  | none => simp [Affiliation.receiveKeyAcquire]
  | some entry =>
    rcases entry with ⟨owner, pid⟩
    cases owner <;> simp [Affiliation.receiveKeyAcquire, bind_assoc, pure_bind]
    all_goals rfl

/-- One consecutive original execution from consumeData entry through the
allocation. The actual lookup and acquisition are retained even if enqueue or
later cleanup Stops, and the complete constructed packet is identified. -/
def Admitted (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (ctx : Admission) (w v : World) : Prop :=
  ∃ entry a b c peer d e,
    (indexLookup [.keypair] (u32le msg 4)).run w = .ok (entry, a) ∧
    (Affiliation.receiveKeyAcquire entry).run a =
      .ok ((some ctx.packet.keypair, some ctx.packet.peer), b) ∧
    (branch .dataNoKeypair false).run b = .ok (false, c) ∧
    (getPeer ctx.packet.peer).run c = .ok (peer, d) ∧
    (branch .dataPeerDead peer.isDead).run d = .ok (false, e) ∧
    ctx.packet = {peer := ctx.packet.peer, keypair := ctx.packet.keypair, bytes := msg, source := src, ds} ∧
    (newRxSkb ctx.packet).run e = .ok (ctx.slot, v)

theorem admission_execution (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (ctx : Admission) (w v : World)
    (hr : (admitSource msg src ds).run w = .ok (some ctx, v)) :
    Admitted msg src ds ctx w v := by
  rw [admitSource_factor] at hr
  simp only [bind_ok] at hr
  obtain ⟨entry, a, hl, acquired, b, hk, noKey, c, hn, hr⟩ := hr
  rcases acquired with ⟨kp, pid⟩
  cases noKey with
  | true =>
    simp only [↓reduceIte, bind_ok] at hr
    obtain ⟨_, _, _, bad⟩ := hr
    simp at bad
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr
    cases kp with
    | none => simp [invariant] at hr
    | some kid =>
      cases pid with
      | none => simp [invariant] at hr
      | some pid =>
        simp only [bind_ok] at hr
        obtain ⟨peer, d, hp, dead, e, hd, hr⟩ := hr
        cases dead with
        | true =>
          simp only [↓reduceIte, bind_ok] at hr
          obtain ⟨_, _, _, _, _, _, bad⟩ := hr
          simp at bad
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, bind_ok] at hr
          obtain ⟨slot, f, ha, he⟩ := hr
          change (Except.ok (some (Admission.mk _ slot), f) : Except Stop _) = .ok (some ctx, v) at he
          cases he
          exact ⟨entry, a, b, c, peer, d, e, hl, hk, hn, hp, hd, rfl, ha⟩

end Leanux.Proofs.WG.RxOrigin
