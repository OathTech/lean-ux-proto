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

/-- Focus the journal of a local observer, retaining its actual state result. -/
private def accessState {Outer Inner : Type} (a : StatePrefixT LifetimeEvent Outer Inner α) :
    StatePrefixT (Event R) Outer Inner α := focusStatePrefix Event.life life? a

private theorem accessState_erases {Outer Inner : Type}
    {a : StatePrefixT LifetimeEvent Outer Inner α}
    {original : StateT Outer (StateT Inner (Except Stop)) α}
    (ha : ErasesStatePrefix a original) :
    ErasesStatePrefix (accessState (R := R) a) original :=
  focusStatePrefix_erases _ _ ha

private theorem accessState_valid {Outer Inner : Type}
    (a : StatePrefixT LifetimeEvent Outer Inner α) (valid : R → Prop) :
    StatePrefixPreserves (fun h _ _ => Valid valid h) (Valid valid) (accessState a) :=
  fun s => MaterialOrigin.access_valid (a.run s) valid

private theorem accessState_projects {Outer Inner : Type}
    {I : List LifetimeEvent → Outer → Inner → Prop}
    {a : StatePrefixT LifetimeEvent Outer Inner α}
    (ha : StatePrefixPreserves I LifetimeEvent.Safe a) :
    StateProjectsUnder I life? (accessState (R := R) a) a :=
  stateProjectsUnder_focus Event.life life? (fun _ => rfl) ha

private theorem validState_lift {Outer Inner : Type}
    (valid : R → Prop) (a : StateT Outer (StateT Inner (Except Stop)) α) :
    StatePrefixPreserves (fun h _ _ => Valid valid h) (Valid valid) (liftStatePrefix a) :=
  fun s => MaterialOrigin.valid_lift valid (a.run s)

private theorem validState_pure {Outer Inner : Type} (valid : R → Prop) (x : α) :
    StatePrefixPreserves (fun h (_ : Outer) (_ : Inner) => Valid valid h) (Valid valid) (pure x) :=
  fun s => MaterialOrigin.valid_pure valid (x, s)

private theorem receiptState_valid {R α : Type} {a : WGPrefix (Event R) α}
    {original : WG.M α} {valid : R → Prop} (ha : ErasesStatePrefix a original)
    (hp : StatePrefixPreserves (fun h _ _ => Valid valid h) (Valid valid) a)
    (f : WGRunWitness α → R) (hf : ∀ r, r.Valid original → valid (f r)) :
    StatePrefixPreserves (fun h _ _ => Valid valid h) (Valid valid)
      (receiptWGObserved a (Event.receipt ∘ f)) := by
  intro w ambient h hi
  obtain ⟨suffix, hs, hv, _⟩ := hp w ambient h hi
  have hc := runWGPrefix_receiptWGObserved a (Event.receipt ∘ f) w ambient h
  simp only [runWGPrefix, runStatePrefix] at hc
  rw [hc]
  cases hr : runPrefix (a.run w) ambient h with
  | mk out t =>
    simp only [hr] at hs hv
    cases out with
    | error e => exact ⟨suffix, hs, hv, trivial⟩
    | ok out =>
      rcases out with ⟨⟨x, v⟩, ambient'⟩
      have hv' : Valid valid (t ++ [Event.receipt (f ⟨x, w, v, ambient, ambient'⟩)]) := by
        intro e he
        rcases List.mem_append.mp he with he | he
        · exact hv e he
        · simp only [List.mem_singleton] at he
          subst e
          exact hf _ ((ha w ambient h).symm.trans (congrArg Prod.fst hr))
      exact ⟨suffix ++ [Event.receipt (f ⟨x, w, v, ambient, ambient'⟩)],
        by simp [hs, List.append_assoc], hv', hv'⟩

private theorem receiptState_projects {I : List F → WGWorld → Ambient → Prop}
    {ρ : E → Option F} {a : WGPrefix E α} {b : WGPrefix F α}
    {receipt : WGRunWitness α → E}
    (hr : ∀ r, ρ (receipt r) = none) (ha : StateProjectsUnder I ρ a b) :
    StateProjectsUnder I ρ (receiptWGObserved a receipt) b := by
  intro w ambient h hi
  change runWGPrefix b w ambient (h.filterMap ρ) =
    ((runWGPrefix (receiptWGObserved a receipt) w ambient h).1,
      (runWGPrefix (receiptWGObserved a receipt) w ambient h).2.filterMap ρ)
  rw [show runWGPrefix b w ambient (h.filterMap ρ) =
    ((runWGPrefix a w ambient h).1, (runWGPrefix a w ambient h).2.filterMap ρ) from ha w ambient h hi,
    runWGPrefix_receiptWGObserved]
  cases runWGPrefix a w ambient h with
  | mk out hist => cases out <;> simp [List.filterMap_append, hr]



/-- The original getter and decrypt call, retaining the actual input record. -/
def readDecrypt (id : SkbId) : WG.M (RxPacket × Option RxPacket) := do
  let pkt ← getRxSkb id
  let result ← decryptPacket pkt
  return (pkt, result)

def readDecryptPrefix (id : SkbId) : MixedM (RxPacket × Option RxPacket) := do
  let pkt ← getRxSkbPrefix id
  let result ← decryptPacketPrefix pkt
  return (pkt, result)

theorem readDecrypt_erases (id : SkbId) : ErasesStatePrefix (readDecryptPrefix id) (readDecrypt id) :=
  erasesStatePrefix_bind (getRxSkbPrefix_erases id) fun pkt =>
    erasesStatePrefix_bind (decryptPacketPrefix_erases pkt) fun _ => erasesStatePrefix_pure _

theorem readDecrypt_allocation (id : SkbId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (readDecryptPrefix id) :=
  StatePrefixEnsures.bind (AmbientContracts.drop (allocationAmbient.getRx (fun _ => True) id)) fun pkt =>
    StatePrefixEnsures.bind (decryptPacketPrefix_allocation pkt) fun _ => StatePrefixEnsures.pure _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)

def admitWith {m sourceM : Type → Type} [Monad m] [Monad sourceM]
    [MonadLiftT WG.M sourceM] [MonadLiftT AmbientM sourceM]
    (lookup : List IndexKind → Nat → m (Option (IndexOwner × PeerId)))
    (keyGet : Option KeypairId → m (Option KeypairId)) (read : PeerId → m Peer)
    (keyPut : Option KeypairId → Bool → m Unit) (peerPut : Option PeerId → m Unit)
    (newRx : RxPacket → m SkbId)
    (step : {α : Type} → sourceM α → m α)
    (msg : List UInt8) (src : SkbSource) (ds : Nat) : m (Option Admission) := do
  let entry ← lookup [.keypair] (u32le msg 4)
  let (keypair, peer) ← match entry with
    | none => pure (none, none)
    | some (IndexOwner.keypair kp, pid) => pure (some kp, some pid)
    | some (IndexOwner.handshake _, _) => step (invariant "a handshake entry under the keypair mask")
  let kp ← match keypair with
    | none => do step (monadLift keypairGetNull); pure none
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

def admitSource (msg : List UInt8) (src : SkbSource) (ds : Nat) : WG.M (Option Admission) :=
  admitWith indexLookup keypairGet getPeer keypairPut WG.peerPut newRxSkb (fun a => a) msg src ds

def admitPrefix (msg : List UInt8) (src : SkbSource) (ds : Nat) : MixedM (Option Admission) :=
  admitWith indexLookupPrefix keypairGetPrefix getPeerMixed keypairPutPrefix peerPutMixed newRxSkbPrefix liftWGPrefix msg src ds

def Receipt.Valid : Receipt → Prop
  | .allocation pkt r => r.Valid (newRxSkb pkt)
  | .admission msg src ds r => r.Valid (admitSource msg src ds)
  | .decrypt id r => r.Valid (readDecrypt id)

abbrev Journal := WGPrefix (Event Receipt)

def allocate (pkt : RxPacket) : Journal SkbId :=
  receiptWGObserved (accessState (newRxSkbPrefix pkt)) (Event.receipt ∘ Receipt.allocation pkt)

def decrypt (id : SkbId) : Journal (RxPacket × Option RxPacket) :=
  receiptWGObserved (accessState (readDecryptPrefix id)) (Event.receipt ∘ Receipt.decrypt id)

def admitRaw (msg : List UInt8) (src : SkbSource) (ds : Nat) : Journal (Option Admission) :=
  admitWith (fun mask i => accessState (indexLookupPrefix mask i)) (fun k => accessState (keypairGetPrefix k))
    (fun p => accessState (getPeerMixed p)) (fun k b => accessState (keypairPutPrefix k b))
    (fun p => accessState (peerPutMixed p)) allocate liftWGPrefix msg src ds

def observeAdmission (msg : List UInt8) (src : SkbSource) (ds : Nat) : Journal (Option Admission) :=
  receiptWGObserved (admitRaw msg src ds) (Event.receipt ∘ Receipt.admission msg src ds)

def finishWith {m sourceM : Type → Type} [Monad m] [Monad sourceM]
    [MonadLiftT WG.M sourceM] [MonadLiftT AmbientM sourceM]
    (keyPut : Option KeypairId → Bool → m Unit) (peerPut : Option PeerId → m Unit)
    (enqueue : SkbId → m Int) (publish : SkbId → m Unit) (free : SkbId → m Unit)
    (step : {α : Type} → sourceM α → m α) (a : Admission) : m Unit := do
  let ret ← enqueue a.slot
  if ← step (branch .dataEpipe (ret == -EPIPE)) then publish a.slot
  if ← step (monadLift (WG.orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE)))) then return
  keyPut (some a.packet.keypair) false
  peerPut (some a.packet.peer)
  free a.slot

def consumeWith {m sourceM : Type → Type} [Monad m] [Monad sourceM]
    [MonadLiftT WG.M sourceM] [MonadLiftT AmbientM sourceM]
    (front : m (Option Admission)) (keyPut : Option KeypairId → Bool → m Unit)
    (peerPut : Option PeerId → m Unit) (enqueue : SkbId → m Int)
    (publish : SkbId → m Unit) (free : SkbId → m Unit)
    (step : {α : Type} → sourceM α → m α) : m Unit := do
  match ← front with
  | none => return
  | some a => finishWith keyPut peerPut enqueue publish free step a

def consumeSource (msg : List UInt8) (src : SkbSource) (ds : Nat) : WG.M Unit :=
  consumeWith (admitSource msg src ds) keypairPut WG.peerPut enqueuePerDeviceAndPeerRx
    (fun id => enqueuePerPeerRx (pure ()) id .dead) freeRxSkb (fun a => a)

def consumePrefix (msg : List UInt8) (src : SkbSource) (ds : Nat) : MixedM Unit :=
  consumeWith (admitPrefix msg src ds) keypairPutPrefix peerPutMixed enqueuePerDeviceAndPeerRxPrefix
    (fun id => enqueuePerPeerRxNativePrefix id .dead) freeRxSkbPrefix liftWGPrefix

def consume (msg : List UInt8) (src : SkbSource) (ds : Nat) : Journal Unit :=
  consumeWith (observeAdmission msg src ds) (fun k b => accessState (keypairPutPrefix k b))
    (fun p => accessState (peerPutMixed p)) (fun id => accessState (enqueuePerDeviceAndPeerRxPrefix id))
    (fun id => accessState (enqueuePerPeerRxNativePrefix id .dead)) (fun id => accessState (freeRxSkbPrefix id)) liftWGPrefix

theorem consumeSource_eq (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    consumeSource msg src ds = consumeData msg src ds := by
  unfold consumeSource consumeWith finishWith admitSource admitWith consumeData
  simp only [bind_assoc, pure_bind]
  repeat' first
    | rfl
    | with_reducible apply Queues.RxWorkers.bind_congr
    | session_origin_intro_forall
    | (split <;> try simp_all only [bind_assoc, pure_bind, Bool.not_eq_true])
    | simp only [bind_assoc, pure_bind]

theorem consumePrefix_eq (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    consumePrefix msg src ds = consumeDataPrefix msg src ds := by
  unfold consumePrefix consumeWith finishWith admitPrefix admitWith consumeDataPrefix
  simp only [bind_assoc, pure_bind]
  repeat' first
    | rfl
    | with_reducible apply Queues.RxWorkers.bind_congr
    | session_origin_intro_forall
    | (split <;> try simp_all only [bind_assoc, pure_bind, Bool.not_eq_true])
    | simp only [bind_assoc, pure_bind]

theorem allocate_erases (pkt : RxPacket) : ErasesStatePrefix (allocate pkt) (newRxSkb pkt) :=
  receiptWGObserved_erases (accessState_erases (PacketAllocation.erases (.rx pkt))) _

theorem admitRaw_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesStatePrefix (admitRaw msg src ds) (admitSource msg src ds) := by
  unfold admitRaw admitSource admitWith
  repeat' first
    | with_reducible exact accessState_erases (indexLookupPrefix_erases _ _)
    | with_reducible exact accessState_erases (keypairGetPrefix_erases _)
    | with_reducible exact accessState_erases (getPeerMixed_erases _)
    | with_reducible exact accessState_erases (keypairPutPrefix_erases _ _)
    | with_reducible exact accessState_erases (peerPutMixed_erases _)
    | with_reducible exact allocate_erases _
    | with_reducible exact accessState_erases (enqueuePerDeviceAndPeerRxPrefix_erases _)
    | with_reducible exact accessState_erases (enqueuePerPeerRxNativePrefix_erases _ _)
    | with_reducible exact accessState_erases (freeRxSkbPrefix_erases _)
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem admit_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesStatePrefix (observeAdmission msg src ds) (admitSource msg src ds) :=
  receiptWGObserved_erases (admitRaw_erases msg src ds) _

theorem consume_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesStatePrefix (consume msg src ds) (consumeData msg src ds) := by
  rw [← consumeSource_eq]
  unfold consume consumeSource consumeWith finishWith
  repeat' first
    | with_reducible exact admit_erases _ _ _
    | with_reducible exact accessState_erases (indexLookupPrefix_erases _ _)
    | with_reducible exact accessState_erases (keypairGetPrefix_erases _)
    | with_reducible exact accessState_erases (getPeerMixed_erases _)
    | with_reducible exact accessState_erases (keypairPutPrefix_erases _ _)
    | with_reducible exact accessState_erases (peerPutMixed_erases _)
    | with_reducible exact allocate_erases _
    | with_reducible exact accessState_erases (enqueuePerDeviceAndPeerRxPrefix_erases _)
    | with_reducible exact accessState_erases (enqueuePerPeerRxNativePrefix_erases _ _)
    | with_reducible exact accessState_erases (freeRxSkbPrefix_erases _)
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem allocate_valid (pkt : RxPacket) :
    StatePrefixPreserves (fun h _ _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (allocate pkt) :=
  receiptState_valid (accessState_erases (PacketAllocation.erases (.rx pkt))) (accessState_valid _ _) _ (fun _ hr => hr)

theorem admitRaw_valid (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StatePrefixPreserves (fun h _ _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (admitRaw msg src ds) := by
  unfold admitRaw admitWith
  simp only [liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact accessState_valid _ _
    | with_reducible exact allocate_valid _
    | with_reducible exact validState_lift Receipt.Valid _
    | with_reducible exact validState_pure Receipt.Valid _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem admit_valid (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StatePrefixPreserves (fun h _ _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (observeAdmission msg src ds) :=
  receiptState_valid (admitRaw_erases msg src ds) (admitRaw_valid msg src ds)
    (Receipt.admission msg src ds) (fun _ hr => hr)

theorem consume_valid (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StatePrefixPreserves (fun h _ _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (consume msg src ds) := by
  unfold consume consumeWith finishWith
  simp only [liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact admit_valid _ _ _
    | with_reducible exact accessState_valid _ _
    | with_reducible exact allocate_valid _
    | with_reducible exact validState_lift Receipt.Valid _
    | with_reducible exact validState_pure Receipt.Valid _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | split

/-- The same stored getter/decrypt cut is used by the original worker, before
its branch, payload write and state-only publication. -/
def prepareWith {m sourceM : Type → Type} [Monad m] [Monad sourceM]
    [MonadLiftT WG.M sourceM] [MonadLiftT AmbientM sourceM]
    (runDecrypt : SkbId → m (RxPacket × Option RxPacket))
    (store : SkbId → (RxPacket → RxPacket) → m Unit)
    (publish : SkbId → PacketState → m PeerId)
    (step : {α : Type} → sourceM α → m α) : m (Option PeerId) := do
  match (← step (monadLift getDev)).decryptQueue.consume with
  | (none, _) =>
    _ ← step (branch .decWorkerConsumed false)
    return none
  | (some id, ring) =>
    _ ← step (branch .decWorkerConsumed true)
    step (monadLift (modifyDev fun d => {d with decryptQueue := ring}))
    let (_, decrypted) ← runDecrypt id
    if ← step (branch .decWorkerDecrypted decrypted.isSome) then
      let some d := decrypted | step (invariant "unreachable")
      store id fun _ => d
      return some (← publish id .crypted)
    else return some (← publish id .dead)

def prepare : Journal (Option PeerId) :=
  prepareWith decrypt (fun id f => accessState (setRxSkbPrefix id f))
    (fun id state => accessState (Queues.RxWorkers.publishPrefix id state)) liftWGPrefix

theorem prepareSource_factor : Queues.RxWorkers.prepareSource =
    prepareWith readDecrypt setRxSkb Queues.RxWorkers.publishSource (fun a => a) := by
  unfold Queues.RxWorkers.prepareSource prepareWith readDecrypt
  simp only [bind_assoc, pure_bind]
  rfl

theorem preparePrefix_factor : Queues.RxWorkers.preparePrefix =
    prepareWith readDecryptPrefix setRxSkbPrefix Queues.RxWorkers.publishPrefix liftWGPrefix := by
  unfold Queues.RxWorkers.preparePrefix prepareWith readDecryptPrefix
  simp only [bind_assoc, pure_bind]
  rfl

theorem decrypt_erases (id : SkbId) : ErasesStatePrefix (decrypt id) (readDecrypt id) :=
  receiptWGObserved_erases (accessState_erases (readDecrypt_erases id)) _

theorem prepare_erases : ErasesStatePrefix prepare Queues.RxWorkers.prepareSource := by
  rw [prepareSource_factor]
  unfold prepare prepareWith
  simp only [liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact decrypt_erases _
    | with_reducible exact accessState_erases (setRxSkbPrefix_erases _ _)
    | with_reducible exact accessState_erases (Queues.RxWorkers.publish_erases _ _)
    | exact erasesStatePrefix_lift _
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem decrypt_valid (id : SkbId) :
    StatePrefixPreserves (fun h _ _ => Valid Receipt.Valid h) (Valid Receipt.Valid) (decrypt id) :=
  receiptState_valid (accessState_erases (readDecrypt_erases id)) (accessState_valid _ _) _ (fun _ hr => hr)

theorem prepare_valid :
    StatePrefixPreserves (fun h _ _ => Valid Receipt.Valid h) (Valid Receipt.Valid) prepare := by
  unfold prepare prepareWith
  simp only [liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact accessState_valid _ _
    | with_reducible exact decrypt_valid _
    | with_reducible exact validState_lift Receipt.Valid _
    | with_reducible exact validState_pure Receipt.Valid _
    | with_reducible apply StatePrefixEnsures.bind
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem allocate_projects (pkt : RxPacket) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) life? (allocate pkt) (newRxSkbPrefix pkt) :=
  receiptState_projects (fun _ => rfl) (accessState_projects (PacketAllocation.preserves (.rx pkt)))

theorem decrypt_projects (id : SkbId) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) life? (decrypt id) (readDecryptPrefix id) :=
  receiptState_projects (fun _ => rfl) (accessState_projects (readDecrypt_allocation id))

theorem admit_allocation (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe (admitPrefix msg src ds) := by
  have hbranch := fun tag b => AmbientContracts.drop (allocationAmbient.branch (fun _ => True) tag b)
  have hinvariant {α : Type} := fun reason => AmbientContracts.drop (allocationAmbient.invariant (α := α) (fun _ => True) reason)
  have hnull := AmbientContracts.drop (allocationAmbient.store (fun _ => True) keypairGetNull keypairGetNull_sameStore)
  have hget := AmbientContracts.drop (allocationAmbient.store (fun _ => True) getDev getDev_sameWGStore)
  simp only [liftWGPrefix] at hbranch hinvariant hnull hget

  unfold admitPrefix admitWith
  simp only [liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact indexLookupPrefix_preserves_ambient allocationAmbient _ _
    | with_reducible exact keypairGetPrefix_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact keypairPutPrefix_allocation _ _
    | with_reducible exact peerPutMixed_allocation _
    | with_reducible exact PacketAllocation.preserves (.rx _)
    | with_reducible exact enqueuePerDeviceAndPeerRxPrefix_allocation _
    | with_reducible exact enqueuePerPeerRxNativePrefix_preserves_ambient allocationAmbient _ _
    | with_reducible exact freeRxSkbPrefix_allocation _
    | with_reducible exact hnull
    | with_reducible exact hbranch _ _
    | with_reducible exact hinvariant _
    | with_reducible exact StatePrefixEnsures.pure (P := fun h w (_ : Ambient) => AllocationInv h w) _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => AllocationInv h w)
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem admitRaw_projects (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) life? (admitRaw msg src ds) (admitPrefix msg src ds) := by
  have hbranch := fun tag b => AmbientContracts.drop (allocationAmbient.branch (fun _ => True) tag b)
  have hinvariant {α : Type} := fun reason => AmbientContracts.drop (allocationAmbient.invariant (α := α) (fun _ => True) reason)
  have hnull := AmbientContracts.drop (allocationAmbient.store (fun _ => True) keypairGetNull keypairGetNull_sameStore)
  have hget := AmbientContracts.drop (allocationAmbient.store (fun _ => True) getDev getDev_sameWGStore)
  simp only [liftWGPrefix] at hbranch hinvariant hnull hget

  unfold admitRaw admitPrefix admitWith
  simp only [liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact allocate_projects _
    | with_reducible apply accessState_projects
    | with_reducible exact indexLookupPrefix_preserves_ambient allocationAmbient _ _
    | with_reducible exact keypairGetPrefix_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact keypairPutPrefix_allocation _ _
    | with_reducible exact peerPutMixed_allocation _
    | with_reducible exact PacketAllocation.preserves (.rx _)
    | with_reducible exact enqueuePerDeviceAndPeerRxPrefix_allocation _
    | with_reducible exact enqueuePerPeerRxNativePrefix_preserves_ambient allocationAmbient _ _
    | with_reducible exact freeRxSkbPrefix_allocation _
    | exact stateProjectsUnder_lift _ _
    | with_reducible exact stateProjectsUnder_pure _ _
    | with_reducible exact hnull
    | with_reducible exact hbranch _ _
    | with_reducible exact hinvariant _
    | with_reducible exact StatePrefixEnsures.pure (P := fun h w (_ : Ambient) => AllocationInv h w) _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
    | with_reducible apply stateProjectsUnder_bind (S := LifetimeEvent.Safe)
    | with_reducible apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => AllocationInv h w)
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem admit_projects (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) life? (observeAdmission msg src ds) (admitPrefix msg src ds) :=
  receiptState_projects (fun _ => rfl) (admitRaw_projects msg src ds)

theorem consume_projects (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    StateProjectsUnder (fun h w _ => AllocationInv h w) life? (consume msg src ds) (consumeDataPrefix msg src ds) := by
  have hbranch := fun tag b => AmbientContracts.drop (allocationAmbient.branch (fun _ => True) tag b)
  have hinvariant {α : Type} := fun reason => AmbientContracts.drop (allocationAmbient.invariant (α := α) (fun _ => True) reason)
  have hnull := AmbientContracts.drop (allocationAmbient.store (fun _ => True) keypairGetNull keypairGetNull_sameStore)
  have hget := AmbientContracts.drop (allocationAmbient.store (fun _ => True) getDev getDev_sameWGStore)
  simp only [liftWGPrefix] at hbranch hinvariant hnull hget

  rw [← consumePrefix_eq]
  have gate (ret : Int) :
      StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
        (liftWGPrefix (WG.orM (branch .dataEnqueueOk (ret == 0))
          (branch .dataEnqueueOkEpipe (ret == -EPIPE)))) := by
    apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
    intro h w ambient x v ambient' hi hr
    simp only [WG.orM, branch, StateT.run_monadLift, monadLift_self,
      StateT.run_bind, CounterWindow.branch_run, CounterWindow.except_ok_bind,
      StateT.run_pure, CounterWindow.except_pure] at hr
    split at hr <;> cases hr <;> exact hi
  unfold consume consumePrefix consumeWith finishWith
  simp only [liftWGPrefix, monadLift_self]
  repeat' first
    | exact gate _
    | with_reducible exact admit_projects _ _ _
    | with_reducible exact admit_allocation _ _ _
    | with_reducible exact allocate_projects _
    | with_reducible apply accessState_projects
    | with_reducible exact indexLookupPrefix_preserves_ambient allocationAmbient _ _
    | with_reducible exact keypairGetPrefix_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.getPeer (fun _ => True) _)
    | with_reducible exact keypairPutPrefix_allocation _ _
    | with_reducible exact peerPutMixed_allocation _
    | with_reducible exact PacketAllocation.preserves (.rx _)
    | with_reducible exact enqueuePerDeviceAndPeerRxPrefix_allocation _
    | with_reducible exact enqueuePerPeerRxNativePrefix_preserves_ambient allocationAmbient _ _
    | with_reducible exact freeRxSkbPrefix_allocation _
    | exact stateProjectsUnder_lift _ _
    | with_reducible exact stateProjectsUnder_pure _ _
    | with_reducible exact hnull
    | with_reducible exact hbranch _ _
    | with_reducible exact hinvariant _
    | with_reducible exact StatePrefixEnsures.pure (P := fun h w (_ : Ambient) => AllocationInv h w) _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
    | with_reducible apply stateProjectsUnder_bind (S := LifetimeEvent.Safe)
    | with_reducible apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => AllocationInv h w)
    | (session_origin_intro_forall; try dsimp only)
    | split

theorem prepare_projects :
    StateProjectsUnder (fun h w _ => AllocationInv h w) life? prepare Queues.RxWorkers.preparePrefix := by
  have hbranch := fun tag b => AmbientContracts.drop (allocationAmbient.branch (fun _ => True) tag b)
  have hinvariant {α : Type} := fun reason => AmbientContracts.drop (allocationAmbient.invariant (α := α) (fun _ => True) reason)
  have hnull := AmbientContracts.drop (allocationAmbient.store (fun _ => True) keypairGetNull keypairGetNull_sameStore)
  have hget := AmbientContracts.drop (allocationAmbient.store (fun _ => True) getDev getDev_sameWGStore)
  simp only [liftWGPrefix] at hbranch hinvariant hnull hget

  rw [preparePrefix_factor]
  unfold prepare prepareWith
  simp only [liftWGPrefix, monadLift_self]
  repeat' first
    | with_reducible exact decrypt_projects _
    | with_reducible apply accessState_projects
    | with_reducible exact readDecrypt_allocation _
    | with_reducible exact AmbientContracts.drop (allocationAmbient.setRx (fun _ => True) _ _)
    | with_reducible exact Queues.RxWorkers.publish_preserves _ _
    | exact stateProjectsUnder_lift _ _
    | with_reducible exact stateProjectsUnder_pure _ _
    | with_reducible exact hget
    | with_reducible exact hbranch _ _
    | exact decryptQueue_allocation _
    | with_reducible exact hinvariant _
    | with_reducible exact StatePrefixEnsures.pure (P := fun h w (_ : Ambient) => AllocationInv h w) _ (fun _ _ _ hi => hi.safe) (fun _ _ _ hi => hi)
    | with_reducible apply stateProjectsUnder_bind (S := LifetimeEvent.Safe)
    | with_reducible apply StatePrefixEnsures.bind (Q := fun _ h w (_ : Ambient) => AllocationInv h w)
    | (session_origin_intro_forall; try dsimp only)
    | split

/-- Exact allocation state, including the full packet and epoch/slot identity.
The receipt remains meaningful after a later enqueue failure and free. -/
theorem allocation_record (pkt : RxPacket) (r : WGRunWitness SkbId)
    (hr : r.Valid (newRxSkb pkt)) :
    ∃ d, r.before.dev = some d ∧ r.value = d.nextSkb ∧
      r.after = Packets.update r.before (fun v =>
        {v with rxSkbs := v.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1}) ∧
      r.ambientAfter = r.ambientBefore ∧
      packetStamp r.before r.value = (d.ifindex, d.nextSkb + 1) := by
  cases hd : r.before.dev with
  | none =>
    simp [WGRunWitness.Valid, newRxSkb, liftSkb_run, SkbStore.newRx, hd] at hr
  | some d =>
    have he := Packets.newRxSkb_run r.before r.ambientBefore d pkt hd
    have hh := he.symm.trans hr
    have eqs : d.nextSkb = r.value ∧
        Packets.update r.before (fun v => {v with rxSkbs := v.rxSkbs.insert d.nextSkb pkt, nextSkb := d.nextSkb + 1}) = r.after ∧ r.ambientBefore = r.ambientAfter := by
      simpa only [Except.ok.injEq, Prod.mk.injEq, and_assoc] using hh
    exact ⟨d, rfl, eqs.1.symm, eqs.2.1.symm, eqs.2.2.symm,
      by simp [packetStamp, hd, ← eqs.1]⟩

/-- Every field other than nonce and bytes is retained by the actual successful
AEAD tail. In particular this is stronger than just peer/key scalar equality. -/
theorem receiveTail_record (pkt out : RxPacket) (k : Keypair) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((KeyTimes.receiveTail pkt k).run w).run ambient = .ok ((some out, v), ambient')) :
    out = {pkt with nonce := u64le pkt.bytes 8, bytes := out.bytes} := by
  simp only [KeyTimes.receiveTail, StateT.run_bind] at hr
  cases ha : ((hiddenAlloc .skbCowDataRx : WG.M Bool).run w).run ambient with
  | error e =>
    simp only [ha] at hr
    change (Except.error e : Except Stop _) = _ at hr
    cases hr
  | ok result =>
    rcases result with ⟨⟨cowOk, entered⟩, enteredAmbient⟩
    simp only [ha, CounterWindow.except_ok_bind, WG.orM, branch, StateT.run_monadLift,
      monadLift_self, StateT.run_bind, CounterWindow.branch_run, StateT.run_pure,
      CounterWindow.except_pure] at hr
    cases cowOk <;>
      cases hp : aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8))
        (pkt.bytes.drop 16) [] <;>
      simp_all
    rw [← hr.1.1]


theorem decryptPacket_record (pkt out : RxPacket) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((decryptPacket pkt).run w).run ambient = .ok ((some out, v), ambient')) :
    out = {pkt with nonce := u64le pkt.bytes 8, bytes := out.bytes} := by
  rw [KeyTimes.decryptPacket_factor] at hr
  simp only [branch, StateT.run_monadLift, monadLift_self, StateT.run_bind,
    CounterWindow.branch_run, CounterWindow.except_ok_bind, StateT.run_pure,
    CounterWindow.except_pure, Bool.false_eq_true, ↓reduceIte] at hr
  cases hg : ((getKeypair pkt.keypair).run w).run (CounterWindow.record ambient .decNoKeypair false) with
  | error e =>
    simp only [hg] at hr
    change (Except.error e : Except Stop _) = _ at hr
    cases hr
  | ok result =>
    rcases result with ⟨⟨k, entered⟩, enteredAmbient⟩
    simp only [hg, CounterWindow.except_ok_bind] at hr
    cases hj : ((KeyTimes.receiveReject k).run entered).run enteredAmbient with
    | error e =>
      simp only [hj] at hr
      change (Except.error e : Except Stop _) = _ at hr
      cases hr
    | ok result =>
      rcases result with ⟨⟨reject, checked⟩, checkedAmbient⟩
      cases reject with
      | false =>
        simp only [hj, CounterWindow.except_ok_bind, Bool.false_eq_true, ↓reduceIte] at hr
        exact receiveTail_record pkt out k checked v checkedAmbient ambient' hr
      | true =>
        simp only [StateT.run_bind, hj, CounterWindow.except_ok_bind, ↓reduceIte] at hr
        cases hp : ((getKeypair pkt.keypair).run checked).run checkedAmbient with
        | error e =>
          simp only [hp] at hr
          change (Except.error e : Except Stop _) = _ at hr
          cases hr
        | ok result =>
          rcases result with ⟨⟨fresh, updated⟩, updatedAmbient⟩
          simp [hp, CounterWindow.setKeypair_run] at hr

/-- Successful stored-packet decryption ties the receipt to that exact packet
record and actual resident receiving key. Missing keys Stop; no credit or
single-decryption invariant is assumed. -/
theorem decrypt_receipt (id : SkbId) (r : WGRunWitness (RxPacket × Option RxPacket))
    (out : RxPacket) (hv : r.Valid (readDecrypt id)) (ho : r.value.2 = some out) :
    ∃ d k, r.before.dev = some d ∧ d.rxSkbs[id]? = some r.value.1 ∧
      d.keypairs[r.value.1.keypair]? = some k ∧ k.receiving.isValid = true ∧
      ((decryptPacket r.value.1).run r.before).run r.ambientBefore =
        .ok ((some out, r.after), r.ambientAfter) ∧
      out = {r.value.1 with nonce := u64le r.value.1.bytes 8, bytes := out.bytes} ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le r.value.1.bytes 8))
        (r.value.1.bytes.drop 16) [] = some out.bytes := by
  unfold WGRunWitness.Valid readDecrypt at hv
  simp only [bind_ok_ambient] at hv
  obtain ⟨pkt, a, aAmbient, hp, result, b, bAmbient, hd, he⟩ := hv
  obtain ⟨rfl, rfl, d, hw, hp⟩ := Packets.getRxSkb_current id r.before a pkt
    r.ambientBefore aAmbient hp
  change (Except.ok (((pkt, result), b), bAmbient) : Except Stop _) =
    .ok ((r.value, r.after), r.ambientAfter) at he
  simp only [Except.ok.injEq, Prod.mk.injEq] at he
  have hin : pkt = r.value.1 := congrArg Prod.fst he.1.1
  have hout : result = some out := (congrArg Prod.snd he.1.1).trans ho
  subst pkt; subst result
  rw [he.1.2, he.2] at hd
  obtain ⟨e, key, he, hk, valid, _⟩ := KeyTimes.decryptPacket_admission _ _ _ _ _ _ hd
  have ed : e = d := Option.some.inj (he.symm.trans hw)
  subst e
  obtain ⟨e, actual, he, hak, _, _, aead⟩ := Affiliation.decryptPacket_fields _ _ _ _ _ _ hd
  have ed : e = d := Option.some.inj (he.symm.trans hw)
  subst e
  have ek : actual = key := Option.some.inj (hak.symm.trans hk)
  subst actual
  exact ⟨d, key, hw, hp, hk, valid, hd, decryptPacket_record _ _ _ _ _ _ hd, aead⟩

/-- The literal publication setter changes only the state of its actual stored
record. The worker source factor locates this after the successful decrypt cut. -/
theorem publication_write (id : SkbId) (state : PacketState) (w : WGWorld) (ambient : Ambient) (d : Device)
    (pkt : RxPacket) (hd : w.dev = some d) (hp : d.rxSkbs[id]? = some pkt) :
    ((setRxSkb id (fun q => {q with state})).run w).run ambient =
      .ok (((), Packets.update w (fun v => {v with rxSkbs := v.rxSkbs.insert id {pkt with state}})), ambient) :=
  Packets.setRxSkb_run w ambient d id pkt _ hd hp

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
    (ctx : Admission) (w v : WGWorld) (ambient ambient' : Ambient) : Prop :=
  ∃ entry a aAmbient b bAmbient c cAmbient peer d dAmbient e eAmbient,
    ((indexLookup [.keypair] (u32le msg 4)).run w).run ambient = .ok ((entry, a), aAmbient) ∧
    ((Affiliation.receiveKeyAcquire entry).run a).run aAmbient =
      .ok (((some ctx.packet.keypair, some ctx.packet.peer), b), bAmbient) ∧
    ((branch .dataNoKeypair false : WG.M Bool).run b).run bAmbient = .ok ((false, c), cAmbient) ∧
    ((getPeer ctx.packet.peer).run c).run cAmbient = .ok ((peer, d), dAmbient) ∧
    ((branch .dataPeerDead peer.isDead : WG.M Bool).run d).run dAmbient = .ok ((false, e), eAmbient) ∧
    ctx.packet = {peer := ctx.packet.peer, keypair := ctx.packet.keypair, bytes := msg, source := src, ds} ∧
    ((newRxSkb ctx.packet).run e).run eAmbient = .ok ((ctx.slot, v), ambient')

theorem admission_execution (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (ctx : Admission) (w v : WGWorld) (ambient ambient' : Ambient)
    (hr : ((admitSource msg src ds).run w).run ambient = .ok ((some ctx, v), ambient')) :
    Admitted msg src ds ctx w v ambient ambient' := by
  rw [admitSource_factor] at hr
  simp only [bind_ok_ambient] at hr
  obtain ⟨entry, a, aAmbient, hl, acquired, b, bAmbient, hk, noKey, c, cAmbient, hn, hr⟩ := hr
  rcases acquired with ⟨kp, pid⟩
  cases noKey with
  | true =>
    simp only [↓reduceIte, bind_ok_ambient] at hr
    obtain ⟨_, _, _, _, bad⟩ := hr
    simp at bad
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr
    cases kp with
    | none =>
      simp [invariant, AmbientM.invariant] at hr
      cases hr
    | some kid =>
      cases pid with
      | none =>
        simp [invariant, AmbientM.invariant] at hr
        cases hr
      | some pid =>
        simp only [bind_ok_ambient] at hr
        obtain ⟨peer, d, dAmbient, hp, dead, e, eAmbient, hd, hr⟩ := hr
        cases dead with
        | true =>
          simp only [↓reduceIte, bind_ok_ambient] at hr
          obtain ⟨_, _, _, _, _, _, _, _, bad⟩ := hr
          simp at bad
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, bind_ok_ambient] at hr
          obtain ⟨slot, f, fAmbient, ha, he⟩ := hr
          change (Except.ok ((some (Admission.mk _ slot), f), fAmbient) : Except Stop _) =
            .ok ((some ctx, v), ambient') at he
          cases he
          exact ⟨entry, a, aAmbient, b, bAmbient, c, cAmbient, peer, d, dAmbient, e, eAmbient,
            hl, hk, hn, hp, hd, rfl, ha⟩

end Leanux.Proofs.WG.RxOrigin
