import Leanux.Proofs.WG.Queues.TxRingEntry

/-! Encryption observes arbitrary checksum/softirq/rescheduling callbacks.
The installed consume event precedes empty-item, getter, encryption and
publication failures; batches and their packet IDs need not be distinct. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def packet (checksumHelp : Packet → Obs Packet)
    (keypair : KeypairId) (pkt : DataPacket) : Obs (Option (List UInt8)) := do
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
  let k ← liftPrefix (getKeypair keypair)
  if ← liftPrefix (branch .encSgvecFailed false) then return none
  return some (dataMessage k.remoteIndex pkt.nonce k.sending.key
    (inner.bytes ++ List.replicate paddingLen 0))

def stepSource (checksum : Packet → M Packet) (softirq : M Unit) : M Bool := do
  softirq
  match ← pollSource with
  | none => return false
  | some first =>
    let some headId := first.head? | invariant "an empty ring item"
    let head ← getTxSkb headId
    let mut state := PacketState.crypted
    for id in first do
      _ ← branch .encWorkerSkbIterate true
      let encrypted ← encryptPacket checksum head.keypair (← getTxSkb id)
      if ← branch .encWorkerEncrypted encrypted.isSome then
        setTxSkb id fun p => {p with bytes := encrypted.getD []}
      else
        state := .dead
        break
    if state == .crypted then _ ← branch .encWorkerSkbIterate false
    enqueuePerPeerTx first state
    return true

private theorem bind_congr (a : M α) (f g : α → M β) (h : ∀ x, f x = g x) :
    (a >>= f) = (a >>= g) := congrArg (fun k => a >>= k) (funext h)

theorem stepSource_eq (checksum : Packet → M Packet) (softirq : M Unit) :
    stepSource checksum softirq = encryptStep checksum softirq := by
  unfold stepSource pollSource encryptStep
  simp only [bind_assoc]
  apply bind_congr
  intro _
  apply bind_congr
  intro d
  cases hc : d.encryptQueue.consume with
  | mk item ring =>
    cases item <;> simp only [bind_assoc, pure_bind]
    all_goals
      repeat' first
        | rfl
        | apply bind_congr
        | intro x
        | split

def step (checksum : Packet → Obs Packet) (softirq : Obs Unit) : Obs Bool := do
  softirq
  match ← poll with
  | none => return false
  | some first =>
    let some headId := first.head? | liftPrefix (invariant "an empty ring item")
    let head ← liftPrefix (getTxSkb headId)
    let mut state := PacketState.crypted
    for id in first do
      _ ← liftPrefix (branch .encWorkerSkbIterate true)
      let encrypted ← packet checksum head.keypair (← liftPrefix (getTxSkb id))
      if ← liftPrefix (branch .encWorkerEncrypted encrypted.isSome) then
        liftPrefix (setTxSkb id fun p => {p with bytes := encrypted.getD []})
      else
        state := .dead
        break
    if state == .crypted then _ ← liftPrefix (branch .encWorkerSkbIterate false)
    liftPrefix (enqueuePerPeerTx first state)
    return true

def iter (checksum : Packet → Obs Packet) (softirq : Obs Unit) (resched : Obs Bool) : Obs IterResult :=
  workerIterPrefix .encryptWorker none (step checksum softirq)
    (do liftPrefix (branch .encWorkerNeedResched (← resched)))

theorem packet_erases
    (hc : ∀ pkt, ErasesPrefix (checksum pkt) (originalChecksum pkt)) (kp : KeypairId) (pkt : DataPacket) :
    ErasesPrefix (packet checksum kp pkt) (encryptPacket originalChecksum kp pkt) := by
  unfold packet encryptPacket
  repeat' first
    | exact hc _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | apply erasesPrefix_ite
    | split
    | (intro x; try dsimp only)

theorem step_erases (hc : ∀ p, ErasesPrefix (checksum p) (originalChecksum p))
    (hs : ErasesPrefix softirq originalSoftirq) :
    ErasesPrefix (step checksum softirq) (encryptStep originalChecksum originalSoftirq) := by
  rw [← stepSource_eq]
  unfold step stepSource
  repeat' first
    | with_reducible exact hs
    | with_reducible exact poll_erases
    | with_reducible exact packet_erases hc _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem iter_erases (hc : ∀ p, ErasesPrefix (checksum p) (originalChecksum p))
    (hs : ErasesPrefix softirq originalSoftirq) (hr : ErasesPrefix resched originalResched) :
    ErasesPrefix (iter checksum softirq resched) (encryptIter originalChecksum originalSoftirq originalResched) := by
  unfold iter encryptIter
  exact workerIterPrefix_erases _ _ (step_erases hc hs)
    (erasesPrefix_bind hr (fun _ => erasesPrefix_lift _))

theorem packet_preserves
    (hc : ∀ p, PrefixPreserves (Inv deviceIndex initial) (Safe initial) (checksum p))
    (kp : KeypairId) (pkt : DataPacket) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (packet checksum kp pkt) := by
  unfold packet
  repeat' first
    | with_reducible exact hc _
    | with_reducible exact lift_frame (getKeypair_frame _)
    | with_reducible exact lift_frame (kernel (sameKernel_branch _ _))
    | with_reducible exact lift_frame (kernel (skipCut_sameKernel _))
    | with_reducible exact lift_frame (kernel (calculateSkbPadding_sameKernel _ _))
    | with_reducible exact lift_frame (kernel (hiddenAlloc_sameKernel _))
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem step_preserves
    (hc : ∀ p, PrefixPreserves (Inv deviceIndex initial) (Safe initial) (checksum p))
    (hs : PrefixPreserves (Inv deviceIndex initial) (Safe initial) softirq) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (step checksum softirq) := by
  unfold step
  repeat' first
    | with_reducible exact hs
    | with_reducible exact poll_preserves
    | with_reducible exact packet_preserves hc _ _
    | with_reducible exact lift_frame (getTx_frame _)
    | with_reducible exact lift_frame (setTx_frame _ _)
    | with_reducible exact lift_frame (enqueuePeer_frame _ _)
    | with_reducible exact lift_frame (kernel (sameKernel_branch _ _))
    | with_reducible exact lift_frame (invariant_frame _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem iter_preserves
    (hc : ∀ p, PrefixPreserves (Inv deviceIndex initial) (Safe initial) (checksum p))
    (hs : PrefixPreserves (Inv deviceIndex initial) (Safe initial) softirq)
    (hr : PrefixPreserves (Inv deviceIndex initial) (Safe initial) resched) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (iter checksum softirq resched) := by
  unfold iter
  exact workerIterPrefix_preserves _ _ (fun _ _ hi => hi.safe) (step_preserves hc hs)
    (PrefixPreserves.bind hr (fun _ => lift_frame (kernel (sameKernel_branch _ _))))

/-- The concrete checksum leaf preserves the entire ring cell. No corresponding
frame is claimed for a NAPI/stack softirq, which may enqueue TX work. -/
theorem checksum_preserves (p : Packet) : PrefixPreserves (Inv deviceIndex initial) (Safe initial)
    (liftPrefix (Leanux.Env.checksumHelp p)) := lift_frame (kernel (checksumHelp_sameKernel p))

inductive Call : Type → Type
  | enqueue (pid : PeerId) (item : List SkbId) : Call Int
  | create (pid : PeerId) (item : List SkbId) : Call Unit
  | packet (kp : KeypairId) (pkt : DataPacket) : Call (Option (List UInt8))
  | step : Call Bool
  | iter : Call IterResult

def Call.observe (c : Call α) (checksum : Packet → Obs Packet) (softirq : Obs Unit) (resched : Obs Bool) : Obs α :=
  match c with
  | .enqueue pid item => TxRing.enqueue pid item
  | .create pid item => TxRing.create pid item
  | .packet kp pkt => TxRing.packet checksum kp pkt
  | .step => TxRing.step checksum softirq
  | .iter => TxRing.iter checksum softirq resched

theorem Call.preserves (c : Call α)
    (hc : ∀ p, PrefixPreserves (Inv deviceIndex initial) (Safe initial) (checksum p))
    (hs : PrefixPreserves (Inv deviceIndex initial) (Safe initial) softirq)
    (hr : PrefixPreserves (Inv deviceIndex initial) (Safe initial) resched) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (c.observe checksum softirq resched) := by
  cases c with
  | enqueue pid item => exact enqueue_preserves pid item
  | create pid item => exact create_preserves pid item
  | packet kp pkt => exact packet_preserves hc kp pkt
  | step => exact step_preserves hc hs
  | iter => exact iter_preserves hc hs hr

/-- Initialized conservation concerns occurrences of whole ring items (lists),
not the constituent packet identities or their peer-queue aliases. -/
theorem Call.initialized (c : Call α)
    (hc : ∀ p, PrefixPreserves (Inv deviceIndex (PtrRing.init n)) (Safe (PtrRing.init n)) (checksum p))
    (hs : PrefixPreserves (Inv deviceIndex (PtrRing.init n)) (Safe (PtrRing.init n)) softirq)
    (hr : PrefixPreserves (Inv deviceIndex (PtrRing.init n)) (Safe (PtrRing.init n)) resched)
    (hw : cell w = some (deviceIndex, PtrRing.init n)) :
    let out := runPrefix (c.observe checksum softirq resched) w []
    ∃ r, Initialized n out.2 r ∧
      match out.1 with
      | .error _ => True
      | .ok (_, v) => cell v = some (deviceIndex, r) :=
  Ring.Source.initialized (c.preserves hc hs hr) hw

end Leanux.Proofs.WG.Queues.TxRing
