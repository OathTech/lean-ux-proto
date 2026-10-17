import Leanux.Proofs.WG.Keypairs.Affiliation
import Leanux.Proofs.WG.KeyTimes.Receive
import Leanux.Proofs.WG.Queues.TxDispositionBorrow
import Leanux.Proofs.WG.KeyTimes.Staging

/-! Local source acquisition and authenticated-decryption cuts. Snapshot facts
retain full records, including allocation stamps and the actual owner word.
The original run premise is separate from the snapshot predicate.
These contracts do not assert initialized path coverage or public-key intent. -/
namespace Leanux.Proofs.WG.Affiliation
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.CounterWindow Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-- A snapshot predicate retaining full owner/peer records, hence epoch and
allocation stamps. It asserts neither execution reachability nor stamp
uniqueness; `acquisition_certificate` derives it from a separate original run.
As a fact about that input it survives later NULL store-back, but it does not
assert that the current word remains non-NULL. -/
def OwnerCertificate (owner : IndexOwner) (pid : PeerId) (w : WGWorld) : Prop :=
  ∃ d p, w.dev = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
    match owner with
    | .handshake id => ∃ ownerPeer, d.peers[id]? = some ownerPeer ∧ ownerPeer.handshakeEntryPeer = some pid
    | .keypair id => ∃ key, d.keypairs[id]? = some key ∧ key.peer = some pid

theorem acquisition_certificate (owner : IndexOwner) (pid : PeerId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((acquireOwner owner).run w).run ambient = .ok ((some pid, v), ambient')) :
    OwnerCertificate owner pid w := by
  obtain ⟨word, u, b, readAmbient, borrowedAmbient, read, get, store⟩ :=
    acquireOwner_acquisition owner w v (some pid) ambient ambient' hr
  have hk : u = w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerWord_preserves owner (fun t => t = w)) w ambient word u readAmbient rfl read
  subst u
  have facts := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec word (wgStoreView w)) w readAmbient (some pid) b borrowedAmbient rfl get
  have hw : word = some pid := (facts.1.resolve_left (by simp)).symm
  obtain ⟨d, p, hd, hp, hpos, hb⟩ := facts.2
  change w.dev = some d at hd
  refine ⟨d, p, hd, hp, hpos, ?_⟩
  cases owner with
  | handshake id =>
    cases ho : d.peers[id]? with
    | none =>
      simp [IndexOwner.peerWord, getPeer, getDev, hd, ho, invariant, AmbientM.invariant] at read
      cases read
    | some op =>
      simp [IndexOwner.peerWord, getPeer, getDev, hd, ho] at read
      exact ⟨op, ho, read.1.trans hw⟩
  | keypair id =>
    cases ho : d.keypairs[id]? with
    | none =>
      simp [IndexOwner.peerWord, getKeypair, getDev, hd, ho, invariant, AmbientM.invariant] at read
      cases read
    | some key =>
      simp [IndexOwner.peerWord, getKeypair, getDev, hd, ho] at read
      exact ⟨key, ho, read.1.trans hw⟩

/-- Exact original sending acquisition at Send.lean's staging handoff. -/
def sendAcquire (kid : KeypairId) : WG.M Unit := do
  peerGet (← IndexOwner.peerDeref (.keypair kid))

theorem sendAcquire_certificate (kid : KeypairId) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((sendAcquire kid).run w).run ambient = .ok (((), v), ambient')) :
    ∃ d k pid p, w.dev = some d ∧ d.keypairs[kid]? = some k ∧
      k.peer = some pid ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      PeerBorrow.Borrowed (wgStoreView w) (some pid) (wgStoreView v) := by
  unfold sendAcquire at hr
  simp only [StateT.run_bind] at hr
  cases hderef : ((IndexOwner.peerDeref (.keypair kid)).run w).run ambient with
  | error e => simp [hderef] at hr
  | ok out =>
    rcases out with ⟨⟨pid, u⟩, readAmbient⟩
    have hstate : u = w := (hoare_iff_run_ambient _ _ _).mp
      (indexOwner_peerDeref_preserves (.keypair kid) (fun t => t = w))
      w ambient pid u readAmbient rfl hderef
    subst u
    simp only [hderef, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    have hb := (hoare_iff_run_ambient _ _ _).mp
      (PeerBorrow.strict_acquire_spec pid (wgStoreView w)) w readAmbient () v ambient' rfl hr
    obtain ⟨d, p, hd, hp, hpos, hv⟩ := hb
    change w.dev = some d at hd
    cases hkey : d.keypairs[kid]? with
    | none =>
      simp [IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getDev, hd, hkey,
        invariant, AmbientM.invariant] at hderef
      cases hderef
    | some k =>
      cases hw : k.peer with
      | none =>
        simp [IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getDev, hd, hkey, hw,
          unsupported, AmbientM.unsupported] at hderef
        cases hderef
      | some actual =>
        simp [IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getDev, hd, hkey, hw] at hderef
        obtain ⟨rfl, rfl⟩ := hderef
        exact ⟨d, k, actual, p, hd, hkey, hw, hp, hpos, d, p, hd, hp, hpos, hv⟩

/-- The actual non-NULL word and slot compatibility identify the sending peer;
no non-NULL or reference-credit premise is added. -/
theorem sendAcquire_owner (kid pid : Nat) (p : Peer) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hi : Inv w) (hd : w.dev = some d) (hp : d.peers[pid]? = some p)
    (hs : p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid)
    (hr : ((sendAcquire kid).run w).run ambient = .ok (((), v), ambient')) :
    PeerBorrow.Borrowed (wgStoreView w) (some pid) (wgStoreView v) := by
  obtain ⟨e, k, borrowed, peer, he, hk, hw, hpeer, hpos, hb⟩ := sendAcquire_certificate kid w v ambient ambient' hr
  have eqd : e = d := Option.some.inj (he.symm.trans hd)
  subst e
  have hc := slot_word w pid p kid k hi hd hp hs hk
  have heq : borrowed = pid := by simpa [Compatible, hw] using hc
  simpa [heq] using hb

/-- Successful AEAD in the original tail preserves packet affiliation fields
and exposes the exact receiving key and ciphertext equation. -/
theorem receiveTail_fields (pkt out : RxPacket) (k : Keypair) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((KeyTimes.receiveTail pkt k).run w).run ambient = .ok ((some out, v), ambient')) :
    out.peer = pkt.peer ∧ out.keypair = pkt.keypair ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = some out.bytes := by
  have hspec : ⦃fun _ => ⌜True⌝⦄ KeyTimes.receiveTail pkt k
      ⦃⇓? result _ => ⌜∀ out, result = some out → out.peer = pkt.peer ∧ out.keypair = pkt.keypair ∧
        aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = some out.bytes⌝⦄ := by
    have ha : ⦃fun (_ : WGWorld) => ⌜True⌝⦄ (hiddenAlloc .skbCowDataRx : WG.M Bool)
        ⦃⇓? _ _ => ⌜True⌝⦄ :=
      hoare_liftAmbient (AmbientM.hiddenAlloc .skbCowDataRx) (fun (_ : WGWorld) => True)
    mvcgen [KeyTimes.receiveTail, WG.orM, ha,
      branch, invariant, AmbientM.branch, AmbientM.invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  exact (hoare_iff_run_ambient _ _ _).mp hspec w ambient (some out) v ambient' True.intro hr out rfl

/-- Source-linked AEAD statement for the complete original decrypt call. -/
theorem decryptPacket_fields (pkt out : RxPacket) (w v : WGWorld)
    (ambient ambient' : Ambient)
    (hr : ((decryptPacket pkt).run w).run ambient = .ok ((some out, v), ambient')) :
    ∃ d k, w.dev = some d ∧ d.keypairs[pkt.keypair]? = some k ∧
      out.peer = pkt.peer ∧ out.keypair = pkt.keypair ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = some out.bytes := by
  rw [KeyTimes.decryptPacket_factor] at hr
  simp only [branch, StateT.run_monadLift, monadLift_self, StateT.run_bind,
    Leanux.Proofs.WG.CounterWindow.branch_run, except_ok_bind, StateT.run_pure, except_pure,
    Bool.false_eq_true, ↓reduceIte] at hr
  cases hg : ((getKeypair pkt.keypair).run w).run (record ambient .decNoKeypair false) with
  | error e =>
    simp only [hg] at hr
    change (Except.error e : Except Stop _) = _ at hr
    cases hr
  | ok result =>
    rcases result with ⟨⟨k, entered⟩, enteredAmbient⟩
    obtain ⟨he, ha, d, hd, hk⟩ := KeyTimes.getKeypair_return pkt.keypair w entered k _ enteredAmbient hg
    subst entered
    subst enteredAmbient
    simp only [hg, except_ok_bind] at hr
    cases hj : ((KeyTimes.receiveReject k).run w).run (record ambient .decNoKeypair false) with
    | error e =>
      simp only [hj] at hr
      change (Except.error e : Except Stop _) = _ at hr
      cases hr
    | ok result =>
      rcases result with ⟨⟨reject, checked⟩, checkedAmbient⟩
      cases reject with
      | false =>
        simp only [hj, except_ok_bind, Bool.false_eq_true, ↓reduceIte] at hr
        exact ⟨d, k, hd, hk, receiveTail_fields pkt out k checked v checkedAmbient ambient' hr⟩
      | true =>
        simp only [hj, except_ok_bind, ↓reduceIte] at hr
        cases hp : ((getKeypair pkt.keypair).run checked).run checkedAmbient with
        | error e =>
          simp only [StateT.run_bind, hp] at hr
          change (Except.error e : Except Stop _) = _ at hr
          cases hr
        | ok result =>
          rcases result with ⟨⟨fresh, updated⟩, updatedAmbient⟩
          simp [hp, Leanux.Proofs.WG.CounterWindow.setKeypair_run] at hr


/-- Literal original staging with the existing out-nokey expression and the
strict acquisition named. This establishes occurrence of the local expression,
not its input invariant at every initialized reached call. -/
def sendStagedSource (pid : PeerId) : WG.M Unit := do
  let p ← getPeer pid
  if ← branch .stagedEmpty p.staged.isEmpty then return
  let packets := p.staged
  setPeer pid {p with staged := []}
  let keypair ← keypairGet p.keypairCurrent
  let outNokey := Lifetimes.stagedOutNokey pid packets keypair
  if ← branch .stagedNoKeypair keypair.isNone then return ← outNokey false
  let some id := keypair | invariant "unreachable"
  let k ← getKeypair id
  if ← branch .stagedKeyInvalid !k.sending.isValid then return ← outNokey false
  if ← branchExpired .stagedBirthdateExpired k.sending.birthdate REJECT_AFTER_TIME then return ← outNokey true
  let mut packetsCb : List DataPacket := []
  for pkt in packets do
    _ ← branch .stagedNonceIterate true
    let ds ← ipTunnelEcnEncap pkt
    let k ← getKeypair id
    let nonce := k.sendingCounter
    setKeypair id {k with sendingCounter := k.sendingCounter + 1}
    if ← branchCmp .stagedNonceRejected (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES then return ← outNokey true
    packetsCb := packetsCb ++ [{peer := pid, keypair := id, nonce, plaintext := pkt, ds}]
  _ ← branch .stagedNonceIterate false
  sendAcquire id
  let item ← packetsCb.mapM newTxSkb
  createData pid item

theorem sendStagedSource_eq (pid : PeerId) : sendStagedSource pid = sendStagedPackets pid := by
  simp only [sendStagedSource, sendStagedPackets, sendAcquire, Lifetimes.stagedOutNokey, bind_assoc]
  rfl

/-- The existing original staging observer already derives common peer/key
fields for its actual allocated batch. This does not constrain arbitrary TX
batches or equate each packet's key field with an arbitrary encrypt argument. -/
theorem staging_common_batch (a : KeyTimes.TxAdmission) (ha : a.Valid) :
    ∀ pkt ∈ a.packets, pkt.peer = a.peer ∧ pkt.keypair = a.slot := by
  intro pkt hp
  exact ⟨(ha.2.2.2.2.1 pkt hp).1, (ha.2.2.2.2.1 pkt hp).2.1⟩


/-- The exact nullable entry-to-key acquisition expression in consumeData. -/
def receiveKeyAcquire (entry : Option (IndexOwner × PeerId)) : WG.M (Option KeypairId × Option PeerId) := do
  let (keypair, peer) ← match entry with
    | none => pure (none, none)
    | some (.keypair kp, pid) => pure (some kp, some pid)
    | some (.handshake _, _) => invariant "a handshake entry under the keypair mask"
  let kp ← match keypair with
    | none => do keypairGetNull; pure none
    | some kp => keypairGet (some kp)
  return (kp, peer)

theorem receiveKeyAcquire_spec (entry : Option (IndexOwner × PeerId)) (s : Option State) :
    ⦃fun w => ⌜view w = s⌝⦄ receiveKeyAcquire entry
    ⦃⇓? result w => ⌜view w = s ∧ ∀ kid pid,
      result = (some kid, some pid) → entry = some (.keypair kid, pid)⌝⦄ := by
  have hk := fun kp => keypairGet_affiliation kp s
  cases entry with
  | none => mvcgen [receiveKeyAcquire, keypairGetNull, branch, AmbientM.branch] <;> simp_all
  | some entry =>
    rcases entry with ⟨owner, pid⟩
    cases owner <;> mvcgen [receiveKeyAcquire, hk, invariant, AmbientM.invariant]
    all_goals simp_all
    all_goals grind

/-- Literal full receive admission with only its existing acquisition named. -/
def consumeDataSource (msg : List UInt8) (src : SkbSource) (ds : Nat) : WG.M Unit := do
  let entry ← indexLookup [.keypair] (u32le msg 4)
  let (kp, peer) ← receiveKeyAcquire entry
  if ← branch .dataNoKeypair kp.isNone then
    peerPut peer
    return
  let some id := kp | invariant "unreachable"
  let some pid := peer | invariant "a keypair entry without a peer"
  if ← branch .dataPeerDead (← getPeer pid).isDead then
    keypairPut (some id) false
    peerPut peer
    return
  let skb ← newRxSkb {peer := pid, keypair := id, bytes := msg, source := src, ds}
  let ret ← enqueuePerDeviceAndPeerRx skb
  if ← branch .dataEpipe (ret == -EPIPE) then enqueuePerPeerRx (pure ()) skb .dead
  if ← WG.orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
  keypairPut (some id) false
  peerPut peer
  freeRxSkb skb

theorem consumeDataSource_eq (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    consumeDataSource msg src ds = consumeData msg src ds := by
  unfold consumeDataSource consumeData
  congr 1
  funext entry
  cases entry with
  | none => simp [receiveKeyAcquire]
  | some entry =>
    rcases entry with ⟨owner, pid⟩
    cases owner <;> simp [receiveKeyAcquire, bind_assoc, pure_bind]
    all_goals rfl

end Leanux.Proofs.WG.Affiliation
