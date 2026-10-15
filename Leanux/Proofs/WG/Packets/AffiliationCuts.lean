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
def OwnerCertificate (owner : IndexOwner) (pid : PeerId) (w : World) : Prop :=
  ∃ d p, w.k.wg = some d ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
    match owner with
    | .handshake id => ∃ ownerPeer, d.peers[id]? = some ownerPeer ∧ ownerPeer.handshakeEntryPeer = some pid
    | .keypair id => ∃ key, d.keypairs[id]? = some key ∧ key.peer = some pid

theorem acquisition_certificate (owner : IndexOwner) (pid : PeerId) (w v : World)
    (hr : (acquireOwner owner).run w = .ok (some pid, v)) : OwnerCertificate owner pid w := by
  obtain ⟨word, u, b, read, get, store⟩ := acquireOwner_acquisition owner w v (some pid) hr
  have hk := indexOwner_peerWord_sameKernel owner w word u read
  have facts := (hoare_iff_triple _ _ _).mpr (PeerBorrow.acquire_spec word u.k) u (some pid) b rfl get
  have hw : word = some pid := (facts.1.resolve_left (by simp)).symm
  obtain ⟨d, p, hd, hp, hpos, hb⟩ := facts.2
  refine ⟨d, p, hk ▸ hd, hp, hpos, ?_⟩
  cases owner with
  | handshake id =>
    cases ho : d.peers[id]? with
    | none => simp [IndexOwner.peerWord, getPeer, getDev, getK, ← hk, hd, ho, invariant] at read
    | some op =>
      have hdw : w.k.wg = some d := hk ▸ hd
      simp [IndexOwner.peerWord, getPeer, getDev, getK, hdw, ho] at read
      exact ⟨op, ho, read.1.trans hw⟩
  | keypair id =>
    cases ho : d.keypairs[id]? with
    | none => simp [IndexOwner.peerWord, getKeypair, getDev, getK, ← hk, hd, ho, invariant] at read
    | some key =>
      have hdw : w.k.wg = some d := hk ▸ hd
      simp [IndexOwner.peerWord, getKeypair, getDev, getK, hdw, ho] at read
      exact ⟨key, ho, read.1.trans hw⟩

/-- Exact original sending acquisition at Send.lean's staging handoff. -/
def sendAcquire (kid : KeypairId) : M Unit := do
  peerGet (← IndexOwner.peerDeref (.keypair kid))

theorem sendAcquire_certificate (kid : KeypairId) (w v : World)
    (hr : (sendAcquire kid).run w = .ok ((), v)) :
    ∃ d k pid p, w.k.wg = some d ∧ d.keypairs[kid]? = some k ∧
      k.peer = some pid ∧ d.peers[pid]? = some p ∧ 0 < p.refcount ∧
      PeerBorrow.Borrowed w.k (some pid) v.k := by
  unfold sendAcquire at hr
  simp only [StateT.run_bind] at hr
  cases hderef : (IndexOwner.peerDeref (.keypair kid)).run w with
  | error e => simp [hderef] at hr
  | ok out =>
    rcases out with ⟨pid, u⟩
    have hkernel := indexOwner_peerDeref_sameKernel (.keypair kid) w pid u hderef
    simp only [hderef, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    have hb := (hoare_iff_triple _ _ _).mpr (PeerBorrow.strict_acquire_spec pid u.k) u () v rfl hr
    obtain ⟨d, p, hd, hp, hpos, hv⟩ := hb
    have hdw : w.k.wg = some d := hkernel ▸ hd
    cases hkey : d.keypairs[kid]? with
    | none => simp [IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getDev, getK, hdw, hkey, invariant] at hderef
    | some k =>
      cases hw : k.peer with
      | none => simp [IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getDev, getK, hdw, hkey, hw, unsupported] at hderef
      | some actual =>
        simp [IndexOwner.peerDeref, IndexOwner.peerWord, getKeypair, getDev, getK, hdw, hkey, hw] at hderef
        obtain ⟨rfl, rfl⟩ := hderef
        exact ⟨d, k, actual, p, hdw, hkey, hw, hp, hpos, d, p, hdw, hp, hpos, hv⟩

/-- The actual non-NULL word and slot compatibility identify the sending peer;
no non-NULL or reference-credit premise is added. -/
theorem sendAcquire_owner (kid pid : Nat) (p : Peer) (w v : World)
    (hi : Inv w) (hd : w.k.wg = some d) (hp : d.peers[pid]? = some p)
    (hs : p.keypairCurrent = some kid ∨ p.keypairPrevious = some kid ∨ p.keypairNext = some kid)
    (hr : (sendAcquire kid).run w = .ok ((), v)) : PeerBorrow.Borrowed w.k (some pid) v.k := by
  obtain ⟨e, k, borrowed, peer, he, hk, hw, hpeer, hpos, hb⟩ := sendAcquire_certificate kid w v hr
  have eqd : e = d := Option.some.inj (he.symm.trans hd)
  subst e
  have hc := slot_word w pid p kid k hi hd hp hs hk
  have heq : borrowed = pid := by simpa [Compatible, hw] using hc
  simpa [heq] using hb

/-- Successful AEAD in the original tail preserves packet affiliation fields
and exposes the exact receiving key and ciphertext equation. -/
theorem receiveTail_fields (pkt out : RxPacket) (k : Keypair) (w v : World)
    (hr : (KeyTimes.receiveTail pkt k).run w = .ok (some out, v)) :
    out.peer = pkt.peer ∧ out.keypair = pkt.keypair ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = some out.bytes := by
  have hspec : ⦃fun _ => ⌜True⌝⦄ KeyTimes.receiveTail pkt k
      ⦃⇓? result _ => ⌜∀ out, result = some out → out.peer = pkt.peer ∧ out.keypair = pkt.keypair ∧
        aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = some out.bytes⌝⦄ := by
    have ha := sameKernel_wp _ (hiddenAlloc_sameKernel .skbCowDataRx) (fun _ => True)
    mvcgen [KeyTimes.receiveTail, WG.orM, ha, branch, invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  exact (hoare_iff_triple _ _ _).mpr hspec w (some out) v True.intro hr out rfl

/-- Source-linked AEAD statement for the complete original decrypt call. -/
theorem decryptPacket_fields (pkt out : RxPacket) (w v : World)
    (hr : (decryptPacket pkt).run w = .ok (some out, v)) :
    ∃ d k, w.k.wg = some d ∧ d.keypairs[pkt.keypair]? = some k ∧
      out.peer = pkt.peer ∧ out.keypair = pkt.keypair ∧
      aeadDecrypt k.receiving.key (counterNonce (u64le pkt.bytes 8)) (pkt.bytes.drop 16) [] = some out.bytes := by
  rw [KeyTimes.decryptPacket_factor] at hr
  simp only [StateT.run_bind, Leanux.Proofs.WG.CounterWindow.branch_run,
    Leanux.Proofs.WG.CounterWindow.except_ok_bind, Bool.false_eq_true, ↓reduceIte] at hr
  cases hg : (getKeypair pkt.keypair).run (record w .decNoKeypair false) with
  | error e => simp [hg] at hr
  | ok result =>
    rcases result with ⟨k, entered⟩
    obtain ⟨he, d, hd, hk⟩ := KeyTimes.getKeypair_return pkt.keypair _ entered k hg
    subst entered
    simp only [hg, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
    cases hj : (KeyTimes.receiveReject k).run (record w .decNoKeypair false) with
    | error e => simp [hj] at hr
    | ok result =>
      rcases result with ⟨reject, checked⟩
      cases reject with
      | false =>
        simp only [hj, Leanux.Proofs.WG.CounterWindow.except_ok_bind, Bool.false_eq_true, ↓reduceIte] at hr
        exact ⟨d, k, hd, hk, receiveTail_fields pkt out k checked v hr⟩
      | true =>
        simp only [StateT.run_bind, hj, Leanux.Proofs.WG.CounterWindow.except_ok_bind, ↓reduceIte] at hr
        cases hp : (getKeypair pkt.keypair).run checked with
        | error e => simp [hp] at hr
        | ok result =>
          rcases result with ⟨fresh, updated⟩
          simp [hp, Leanux.Proofs.WG.CounterWindow.setKeypair_run] at hr


/-- Literal original staging with the existing out-nokey expression and the
strict acquisition named. This establishes occurrence of the local expression,
not its input invariant at every initialized reached call. -/
def sendStagedSource (pid : PeerId) : M Unit := do
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
  simp only [sendStagedSource, sendStagedPackets, sendAcquire, Lifetimes.stagedOutNokey, bind_assoc, pure_bind]
  rfl

/-- The existing original staging observer already derives common peer/key
fields for its actual allocated batch. This does not constrain arbitrary TX
batches or equate each packet's key field with an arbitrary encrypt argument. -/
theorem staging_common_batch (a : KeyTimes.TxAdmission) (ha : a.Valid) :
    ∀ pkt ∈ a.packets, pkt.peer = a.peer ∧ pkt.keypair = a.slot := by
  intro pkt hp
  exact ⟨(ha.2.2.2.2.1 pkt hp).1, (ha.2.2.2.2.1 pkt hp).2.1⟩


/-- The exact nullable entry-to-key acquisition expression in consumeData. -/
def receiveKeyAcquire (entry : Option (IndexOwner × PeerId)) : M (Option KeypairId × Option PeerId) := do
  let (keypair, peer) ← match entry with
    | none => pure (none, none)
    | some (.keypair kp, pid) => pure (some kp, some pid)
    | some (.handshake _, _) => invariant "a handshake entry under the keypair mask"
  let kp ← match keypair with
    | none => do keypairGetCurrent; pure none
    | some kp => keypairGet (some kp)
  return (kp, peer)

theorem receiveKeyAcquire_spec (entry : Option (IndexOwner × PeerId)) (s : Option State) :
    ⦃fun w => ⌜view w = s⌝⦄ receiveKeyAcquire entry
    ⦃⇓? result w => ⌜view w = s ∧ ∀ kid pid,
      result = (some kid, some pid) → entry = some (.keypair kid, pid)⌝⦄ := by
  have hk := fun kp => keypairGet_affiliation kp s
  have hn := (kernel Lifetimes.keypairGetCurrent_sameKernel).wp (fun t => t = s)
  cases entry with
  | none => mvcgen [receiveKeyAcquire, hn] <;> simp_all
  | some entry =>
    rcases entry with ⟨owner, pid⟩
    cases owner <;> mvcgen [receiveKeyAcquire, hk, invariant]
    all_goals simp_all
    all_goals grind

/-- Literal full receive admission with only its existing acquisition named. -/
def consumeDataSource (msg : List UInt8) (src : SkbSource) (ds : Nat) : M Unit := do
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
