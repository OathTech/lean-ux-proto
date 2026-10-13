import Leanux.Proofs.WG.Peers.Access
import Leanux.Proofs.WG.Peers.Allocation
import Leanux.Proofs.Framing.Kernel

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Peer creation observed at its first insertion and throughout initialization.
The invariant bounds both resident and previously released identities; the latter
is needed to distinguish a new allocation from arbitrary initial history. -/
namespace Leanux.Proofs.WG.Peers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.Lifetimes

structure CreationInv (h : List PeerEvent) (w : World) : Prop where
  access : AccessInv h w
  bounded : Bounded (snapshot w)
  pastBounded : ∀ stamp, AccessEvent.Released h stamp → stamp ≤ (snapshot w).frontier

theorem CreationInv.congr (hi : CreationInv h w) (he : snapshot v = snapshot w) :
    CreationInv h v := by
  rcases hi with ⟨ha, hb, hp⟩
  exact ⟨by simpa only [AccessInv, he] using ha, he ▸ hb, by simpa only [he] using hp⟩

theorem CreationInv.read (hi : CreationInv h w)
    (hl : (snapshot w).slots pid = some stamp) :
    CreationInv (h ++ [.read pid stamp]) w := by
  have hn : ¬ AccessEvent.Released h stamp := fun hr => hi.access.2.2 _ hr pid hl
  refine ⟨⟨AccessEvent.safe_append_read hi.access.1 hn, hi.access.2.1, ?_⟩,
    hi.bounded, ?_⟩
  · intro s hs
    exact hi.access.2.2 s (AccessEvent.released_append_read.mp hs)
  · intro s hs
    exact hi.pastBounded s (AccessEvent.released_append_read.mp hs)

theorem CreationInv.write (hi : CreationInv h w)
    (hl : (snapshot w).slots pid = some stamp) :
    CreationInv (h ++ [.write pid stamp]) w := by
  have hn : ¬ AccessEvent.Released h stamp := fun hr => hi.access.2.2 _ hr pid hl
  refine ⟨⟨AccessEvent.safe_append_write hi.access.1 hn, hi.access.2.1, ?_⟩,
    hi.bounded, ?_⟩
  · intro s hs
    exact hi.access.2.2 s (AccessEvent.released_append_write.mp hs)
  · intro s hs
    exact hi.pastBounded s (AccessEvent.released_append_write.mp hs)

abbrev CreationSpec (P : Store PeerId → Prop) (g : PrefixM PeerEvent α)
    (Q : α → Store PeerId → Prop) :=
  PrefixEnsures (fun h w => CreationInv h w ∧ P (snapshot w)) AccessEvent.Safe g
    (fun x h w => CreationInv h w ∧ Q x (snapshot w))

theorem creation_pure (P : Store PeerId → Prop) (x : α) :
    CreationSpec P (pure x) (fun _ => P) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1.access.1) (fun _ _ hi => hi)

theorem creation_lift (P : Store PeerId → Prop) (a : M α) (ha : SamePeerSnapshot a) :
    CreationSpec P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun _ _ hi => hi.1.access.1)
  intro h w x v hi hr
  have he := ha w x v hr
  exact ⟨hi.1.congr he, he ▸ hi.2⟩

theorem creation_kernel (P : Store PeerId → Prop) (a : M α) (ha : SameKernel a) :
    CreationSpec P (liftPrefix a) (fun _ => P) :=
  creation_lift P a (samePeerSnapshot_of_sameKernel ha)

theorem creation_get (P : Store PeerId → Prop) (pid : PeerId) :
    CreationSpec P (getPeerPrefix pid) (fun p s => P s ∧ s.slots pid = some p.internalId) := by
  intro w h hi
  rw [getPeerPrefix_run]
  cases hr : (getPeer pid).run w with
  | error _ => exact ⟨[], by simp, hi.1.access.1, True.intro⟩
  | ok out =>
    rcases out with ⟨p, v⟩
    obtain ⟨rfl, live⟩ := getPeer_current pid w v p hr
    have hn := hi.1.read live
    exact ⟨[.read pid p.internalId], rfl, hn.access.1, hn, hi.2, live⟩

theorem creation_set (P : Store PeerId → Prop) (pid : PeerId) (p : Peer) :
    CreationSpec (fun s => P s ∧ s.slots pid = some p.internalId)
      (setPeerPrefix pid p) (fun _ => P) := by
  intro w h hi
  rw [setPeerPrefix_run]
  cases hd : w.k.wg with
  | none => simp [snapshot, hd] at hi
  | some d =>
    have hr : (setPeer pid p).run w = .ok ((),
        { w with k := { w.k with wg := some { d with peers := d.peers.insert pid p } } }) := by
      simp [setPeer, modifyDev, modifyK, hd]
    rw [hr]
    simp only [Option.isSome_some, ↓reduceIte]
    have he := setPeer_same pid p w _ hi.2.2 hr
    have hn := (hi.1.write hi.2.2).congr he
    exact ⟨[.write pid p.internalId], rfl, hn.access.1, hn, he ▸ hi.2.1⟩

/-- A same-store observer can retain any cached identity predicate. -/
theorem creation_forget (hg : CreationSpec P g Q)
    (hq : ∀ x s, Q x s → R x s) : CreationSpec P g R :=
  hg.consequence (fun _ _ h => h) (fun x _ _ h => ⟨h.1, hq x _ h.2⟩)

theorem creation_branch (P : Store PeerId → Prop) (d : Decision) (b : Bool) :
    CreationSpec P (liftPrefix (branch d b)) (fun _ => P) :=
  creation_kernel P _ (sameKernel_branch d b)

theorem creation_world (P : Store PeerId → Prop) :
    CreationSpec P (liftPrefix (get : M World)) (fun _ => P) :=
  creation_kernel P _ (fun _ _ _ hr => by cases hr; rfl)

theorem creation_dev (P : Store PeerId → Prop) :
    CreationSpec P (liftPrefix getDev) (fun _ => P) := by
  apply creation_kernel
  apply sameKernel_of_wp
  intro k
  mvcgen [getDev, getK, invariant]

theorem creation_stop (P : Store PeerId → Prop) (what : String) :
    CreationSpec P (liftPrefix (unsupported (α := α) what)) (fun _ => P) :=
  creation_lift P _ (samePeerSnapshot_of_sameWGKernel (KernelFrames.unsupported_sameWGKernel what))

theorem creation_require (P : Store PeerId → Prop) (pid : PeerId) (what : String) :
    CreationSpec P (requireNotPendingPrefix pid what) (fun _ => P) := by
  unfold requireNotPendingPrefix
  apply PrefixEnsures.bind (creation_get P pid)
  intro p
  apply PrefixEnsures.bind (creation_world (fun s => P s ∧ s.slots pid = some p.internalId))
  intro w
  split
  · exact creation_forget (creation_stop (fun s => P s ∧ s.slots pid = some p.internalId) _) (fun _ _ h => h.1)
  · exact creation_forget (creation_pure (fun s => P s ∧ s.slots pid = some p.internalId) ()) (fun _ _ h => h.1)

def dstCacheResetPrefix (pid : PeerId) : PrefixM PeerEvent Unit := do
  let w ← liftPrefix (get : M World)
  if !(w.armRecords && w.dstCacheRecords) then return
  let ts ← liftPrefix (hiddenJiffies .dstCacheResetTs)
  let p ← getPeerPrefix pid
  setPeerPrefix pid { p with dstCache := { p.dstCache with resetTs := ts } }

def resetLastSentHandshakePrefix (pid : PeerId) : PrefixM PeerEvent Unit := do
  let now ← liftPrefix (hiddenClock64 .resetLastSent)
  setPeerPrefix pid { (← getPeerPrefix pid) with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }

def precomputeStaticStaticPrefix (pid : PeerId) : PrefixM PeerEvent Unit := do
  requireNotPendingPrefix pid "recomputing the static-static key"
  let identity := (← liftPrefix getDev).staticIdentity
  let p ← getPeerPrefix pid
  let zero ← do
    if ← liftPrefix (branch .precomputeNoIdentity !identity.hasIdentity) then pure true
    else
      let (out, nonNull) := curve25519 identity.staticPrivate p.remoteStatic
      setPeerPrefix pid { p with precomputedStaticStatic := out }
      liftPrefix (branch .precomputeNullPoint !nonNull)
  if zero then setPeerPrefix pid { (← getPeerPrefix pid) with precomputedStaticStatic := List.replicate 32 0 }

def handshakeInitPrefix (pid : PeerId) (psk : Option Key) : PrefixM PeerEvent Unit := do
  if ← liftPrefix (branch .handshakeInitHasPsk psk.isSome) then
    let p ← getPeerPrefix pid
    setPeerPrefix pid { p with presharedKey := psk.getD p.presharedKey }
  precomputeStaticStaticPrefix pid

theorem dstCacheResetPrefix_erases (pid : PeerId) :
    ErasesPrefix (dstCacheResetPrefix pid) (dstCacheReset pid) := by
  unfold dstCacheResetPrefix dstCacheReset
  repeat' first
    | contradiction
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible exact getPeerPrefix_erases _
    | with_reducible exact setPeerPrefix_erases _ _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | intro_forall
    | dsimp only
    | split

theorem resetLastSentHandshakePrefix_erases (pid : PeerId) :
    ErasesPrefix (resetLastSentHandshakePrefix pid) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshakePrefix resetLastSentHandshake
  exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
    erasesPrefix_bind (getPeerPrefix_erases _) (fun _ => setPeerPrefix_erases _ _))

theorem precomputeStaticStaticPrefix_erases (pid : PeerId) :
    ErasesPrefix (precomputeStaticStaticPrefix pid) (precomputeStaticStatic pid) := by
  unfold precomputeStaticStaticPrefix precomputeStaticStatic
  repeat' first
    | contradiction
    | with_reducible exact requireNotPendingPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible exact getPeerPrefix_erases _
    | with_reducible exact setPeerPrefix_erases _ _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | intro_forall
    | dsimp only
    | split

theorem handshakeInitPrefix_erases (pid : PeerId) (psk : Option Key) :
    ErasesPrefix (handshakeInitPrefix pid psk) (handshakeInit pid psk) := by
  unfold handshakeInitPrefix handshakeInit
  repeat' first
    | contradiction
    | with_reducible exact precomputeStaticStaticPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible exact getPeerPrefix_erases _
    | with_reducible exact setPeerPrefix_erases _ _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | intro_forall
    | dsimp only
    | split

theorem dstCacheResetPrefix_spec (P : Store PeerId → Prop) (pid : PeerId) :
    CreationSpec P (dstCacheResetPrefix pid) (fun _ => P) := by
  unfold dstCacheResetPrefix
  apply PrefixEnsures.bind (creation_world P)
  intro w
  split
  · exact creation_pure _ ()
  · apply PrefixEnsures.bind (creation_kernel P _ (hiddenJiffies_sameKernel _))
    intro ts
    apply PrefixEnsures.bind (creation_get P pid)
    intro p
    exact creation_set P pid { p with dstCache := { p.dstCache with resetTs := ts } }

theorem resetLastSentHandshakePrefix_spec (P : Store PeerId → Prop) (pid : PeerId) :
    CreationSpec P (resetLastSentHandshakePrefix pid) (fun _ => P) := by
  unfold resetLastSentHandshakePrefix
  apply PrefixEnsures.bind (creation_kernel P _ (Framing.hiddenClock64_sameKernel _))
  intro now
  apply PrefixEnsures.bind (creation_get P pid)
  intro p
  exact creation_set P pid { p with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }

theorem precomputeStaticStaticPrefix_spec (P : Store PeerId → Prop) (pid : PeerId) :
    CreationSpec P (precomputeStaticStaticPrefix pid) (fun _ => P) := by
  unfold precomputeStaticStaticPrefix
  apply PrefixEnsures.bind (creation_require P pid _)
  intro _
  apply PrefixEnsures.bind (creation_dev P)
  intro d
  apply PrefixEnsures.bind (creation_get P pid)
  intro p
  apply PrefixEnsures.bind (creation_branch (fun s => P s ∧ s.slots pid = some p.internalId) _ _)
  intro b
  split
  · dsimp only
    simp only [pure_bind, ↓reduceIte]
    apply PrefixEnsures.bind (creation_get (fun s => P s ∧ s.slots pid = some p.internalId) pid)
    intro q
    exact creation_forget (creation_set (fun s => P s ∧ s.slots pid = some p.internalId) pid { q with precomputedStaticStatic := List.replicate 32 0 })
      (fun _ _ h => h.1)
  · dsimp only
    apply PrefixEnsures.bind (creation_set P pid
      { p with precomputedStaticStatic := (curve25519 d.staticIdentity.staticPrivate p.remoteStatic).1 })
    intro _
    apply PrefixEnsures.bind (creation_branch P _ _)
    intro zero
    dsimp only
    split
    · apply PrefixEnsures.bind (creation_get P pid)
      intro q
      exact creation_set P pid { q with precomputedStaticStatic := List.replicate 32 0 }
    · exact creation_pure P ()

theorem handshakeInitPrefix_spec (P : Store PeerId → Prop) (pid : PeerId) (psk : Option Key) :
    CreationSpec P (handshakeInitPrefix pid psk) (fun _ => P) := by
  unfold handshakeInitPrefix
  apply PrefixEnsures.bind (creation_branch P _ _)
  intro b
  split
  · apply PrefixEnsures.bind (creation_get P pid)
    intro p
    apply PrefixEnsures.bind (creation_set P pid { p with presharedKey := psk.getD p.presharedKey })
    intro _
    exact precomputeStaticStaticPrefix_spec P pid
  · exact precomputeStaticStaticPrefix_spec P pid

/-- The original non-failing allocation cut, before any initialization reads.
The first setter can overwrite a malformed occupied nextPeer slot; the observer
records the new allocation, without inventing an old release in that case. -/
def createdPeer (publicKey : Key) (internalId : Nat) : Peer :=
  { remoteStatic := publicKey, presharedKey := List.replicate 32 0,
    precomputedStaticStatic := List.replicate 32 0, internalId,
    cookieDecryptionKey := blake2s 32 [] ("cookie--".toUTF8.toList ++ publicKey),
    cookieMac1Key := blake2s 32 [] ("mac1----".toUTF8.toList ++ publicKey) }

def peerCreateCore (pid : PeerId) (publicKey : Key) : M Unit := do
  let internalId := (← getK).peerCounter + 1
  modifyK fun k => { k with peerCounter := internalId }
  modifyDev fun d => { d with nextPeer := pid + 1 }
  setPeer pid (createdPeer publicKey internalId)

def peerCreateCorePrefix (pid : PeerId) (publicKey : Key) : PrefixM PeerEvent Unit :=
  fun w => ExceptT.mk fun h => ((peerCreateCore pid publicKey).run w,
    if w.k.wg.isSome then h ++ [.allocate pid (w.k.peerCounter + 1), .write pid (w.k.peerCounter + 1)]
    else h)

@[simp] theorem peerCreateCorePrefix_run (pid : PeerId) (key : Key) (w : World) (h : List PeerEvent) :
    runPrefix (peerCreateCorePrefix pid key) w h = ((peerCreateCore pid key).run w,
      if w.k.wg.isSome then h ++ [.allocate pid (w.k.peerCounter + 1), .write pid (w.k.peerCounter + 1)]
      else h) := rfl

theorem peerCreateCorePrefix_erases (pid : PeerId) (key : Key) :
    ErasesPrefix (peerCreateCorePrefix pid key) (peerCreateCore pid key) := fun _ _ => rfl

def creationCoreWorld (w : World) (pid : PeerId) (publicKey : Key) : World :=
  { w with
    k := { w.k with
      peerCounter := w.k.peerCounter + 1
      wg := w.k.wg.map fun d => { d with
        nextPeer := pid + 1
        peers := d.peers.insert pid (createdPeer publicKey (w.k.peerCounter + 1)) } } }

theorem peerCreateCore_run (pid : PeerId) (key : Key) (w : World) :
    (peerCreateCore pid key).run w = .ok ((), creationCoreWorld w pid key) := by
  simp [peerCreateCore, creationCoreWorld, getK, modifyK, modifyDev, setPeer,
    StateT.run_bind, StateT.run_get, StateT.run_modify]
  cases w.k.wg <;> rfl

theorem creationCore_snapshot (pid : PeerId) (key : Key) (w : World) (d : Device)
    (hd : w.k.wg = some d) :
    snapshot (creationCoreWorld w pid key) = (snapshot w).allocate pid := by
  simpa [creationCoreWorld, snapshot, hd, mapStore] using
    mapStore_allocate w.k.peerCounter d.peers pid (createdPeer key (w.k.peerCounter + 1)) rfl

theorem CreationInv.allocate (hi : CreationInv h w)
    (he : snapshot v = (snapshot w).allocate pid) :
    CreationInv (h ++ [.allocate pid ((snapshot w).frontier + 1),
      .write pid ((snapshot w).frontier + 1)]) v := by
  have hn : ¬ AccessEvent.Released h ((snapshot w).frontier + 1) := by
    intro hr
    have := hi.pastBounded _ hr
    omega
  have hsafe := AccessEvent.safe_append_write (slot := pid)
    (AccessEvent.safe_append_allocate (slot := pid) hi.access.1 hn)
    (by simpa only [AccessEvent.released_append_allocate] using hn)
  refine ⟨⟨by simpa only [List.append_assoc, List.cons_append, List.nil_append] using hsafe,
    ?_, ?_⟩, ?_, ?_⟩
  · rw [he]
    exact allocate_unique _ pid hi.bounded hi.access.2.1
  · intro stamp hr
    have old : AccessEvent.Released h stamp := by simpa [AccessEvent.Released] using hr
    rw [he]
    exact (allocate_transition _ pid).absent (hi.pastBounded _ old) (hi.access.2.2 _ old)
  · rw [he]
    exact allocate_bounded _ pid hi.bounded
  · intro stamp hr
    have old : AccessEvent.Released h stamp := by simpa [AccessEvent.Released] using hr
    rw [he]
    exact Nat.le_trans (hi.pastBounded _ old) (Nat.le_succ _)

theorem peerCreateCorePrefix_preserves (pid : PeerId) (key : Key) :
    PrefixPreserves CreationInv AccessEvent.Safe (peerCreateCorePrefix pid key) := by
  intro w h hi
  rw [peerCreateCorePrefix_run, peerCreateCore_run]
  cases hd : w.k.wg with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    refine ⟨[], by simp, hi.access.1, ?_⟩
    refine ⟨⟨hi.access.1, ?_, ?_⟩, ?_, ?_⟩
    · simp [snapshot, creationCoreWorld, hd, Unique]
    · simp [snapshot, creationCoreWorld, hd, Absent]
    · simp [snapshot, creationCoreWorld, hd, Bounded]
    · intro stamp hr
      exact Nat.le_trans (hi.pastBounded _ hr) (Nat.le_succ _)
  | some d =>
    simp only [Option.isSome_some, ↓reduceIte]
    have hinv := hi.allocate (creationCore_snapshot pid key w d hd)
    exact ⟨[.allocate pid (w.k.peerCounter + 1), .write pid (w.k.peerCounter + 1)],
      rfl, hinv.access.1, hinv⟩

/-- A proof-side regrouping of exactly the original creation body. -/
def peerCreateFactored (key : Key) (psk : Option Key) : M (Except Int PeerId) := do
  let d ← getDev
  if ← branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE then
    return .error (-ENOMEM)
  if ← branch .peerCreateNoMem !(← hiddenAlloc .kmemCacheZallocPeer) then return .error (-ENOMEM)
  if ← branch .peerCreateDstCacheFail false then return .error (-ENOMEM)
  let pid := d.nextPeer
  peerCreateCore pid key
  dstCacheReset pid
  handshakeInit pid psk
  resetLastSentHandshake pid
  modifyDev fun d => { d with peerList := d.peerList ++ [pid], peerHashtable := (key, pid) :: d.peerHashtable, numPeers := d.numPeers + 1 }
  return .ok pid

theorem peerCreateFactored_eq (key : Key) (psk : Option Key) :
    peerCreateFactored key psk = peerCreate key psk := by
  simp only [peerCreateFactored, peerCreate, peerCreateCore, createdPeer, bind_assoc]

def peerCreatePrefix (key : Key) (psk : Option Key) : PrefixM PeerEvent (Except Int PeerId) := do
  let d ← liftPrefix getDev
  if ← liftPrefix (branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE) then
    return .error (-ENOMEM)
  if ← liftPrefix (branch .peerCreateNoMem !(← liftPrefix (hiddenAlloc .kmemCacheZallocPeer))) then
    return .error (-ENOMEM)
  if ← liftPrefix (branch .peerCreateDstCacheFail false) then return .error (-ENOMEM)
  let pid := d.nextPeer
  peerCreateCorePrefix pid key
  dstCacheResetPrefix pid
  handshakeInitPrefix pid psk
  resetLastSentHandshakePrefix pid
  liftPrefix (modifyDev fun d => { d with peerList := d.peerList ++ [pid], peerHashtable := (key, pid) :: d.peerHashtable, numPeers := d.numPeers + 1 })
  return .ok pid

theorem peerCreatePrefix_erases (key : Key) (psk : Option Key) :
    ErasesPrefix (peerCreatePrefix key psk) (peerCreate key psk) := by
  rw [← peerCreateFactored_eq]
  unfold peerCreatePrefix peerCreateFactored
  repeat' first
    | contradiction
    | with_reducible exact peerCreateCorePrefix_erases _ _
    | with_reducible exact dstCacheResetPrefix_erases _
    | with_reducible exact handshakeInitPrefix_erases _ _
    | with_reducible exact resetLastSentHandshakePrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_ite
    | with_reducible apply erasesPrefix_bind
    | intro_forall
    | dsimp only
    | split

theorem core_creation_spec (pid : PeerId) (key : Key) :
    CreationSpec (fun _ => True) (peerCreateCorePrefix pid key) (fun _ _ => True) :=
  (show PrefixEnsures CreationInv AccessEvent.Safe (peerCreateCorePrefix pid key)
      (fun _ => CreationInv) from peerCreateCorePrefix_preserves pid key).consequence
    (fun _ _ h => h.1) (fun _ _ _ h => ⟨h, True.intro⟩)

theorem modifyDev_samePeerSnapshot (f : Device → Device) (hf : ∀ d, (f d).peers = d.peers) :
    SamePeerSnapshot (modifyDev f) := by
  apply samePeerSnapshot_of_wp
  intro s
  exact modifyDev_peer_spec (fun t => t = s) f hf

theorem peerCreatePrefix_preserves (key : Key) (psk : Option Key) :
    PrefixPreserves CreationInv AccessEvent.Safe (peerCreatePrefix key psk) := by
  have full : CreationSpec (fun _ => True) (peerCreatePrefix key psk) (fun _ _ => True) := by
    unfold peerCreatePrefix
    apply PrefixEnsures.bind (creation_dev (fun _ => True))
    intro d
    apply PrefixEnsures.bind (creation_lift (fun _ => True) _
      (samePeerSnapshot_of_sameWGKernel (KernelFrames.branchCmp_sameWGKernel _ _ _ _)))
    intro full
    split
    · exact creation_pure (fun _ => True) _
    · apply PrefixEnsures.bind (creation_kernel (fun _ => True) _ (Framing.hiddenAlloc_sameKernel _))
      intro allocated
      apply PrefixEnsures.bind (creation_branch (fun _ => True) _ _)
      intro failed
      split
      · exact creation_pure (fun _ => True) _
      · apply PrefixEnsures.bind (creation_branch (fun _ => True) _ _)
        intro failed
        split
        · exact creation_pure (fun _ => True) _
        · apply PrefixEnsures.bind (core_creation_spec d.nextPeer key)
          intro _
          apply PrefixEnsures.bind (dstCacheResetPrefix_spec (fun _ => True) d.nextPeer)
          intro _
          apply PrefixEnsures.bind (handshakeInitPrefix_spec (fun _ => True) d.nextPeer psk)
          intro _
          apply PrefixEnsures.bind (resetLastSentHandshakePrefix_spec (fun _ => True) d.nextPeer)
          intro _
          apply PrefixEnsures.bind (creation_lift (fun _ => True) _
            (modifyDev_samePeerSnapshot
              (fun v => { v with peerList := v.peerList ++ [d.nextPeer], peerHashtable := (key, d.nextPeer) :: v.peerHashtable, numPeers := v.numPeers + 1 })
              (fun _ => rfl)))
          intro _
          exact creation_pure (fun _ => True) _
  exact (full.consequence (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => hi.1)).preserves

theorem peerPutPrefix_creation_preserves (peer : Option PeerId) :
    PrefixPreserves CreationInv AccessEvent.Safe (peerPutPrefix peer) := by
  intro w h hi
  rw [peerPutPrefix_run]
  refine ⟨peerPutEvents peer w, rfl, peerPutEvents_safe peer w h hi.access, ?_⟩
  cases hr : (peerPut peer).run w with
  | error _ => trivial
  | ok out =>
    rcases out with ⟨result, v⟩
    cases result
    have retained := peerPut_retained peer w () v hr
    have ha := (peerPutPrefix_preserves peer w h hi.access).choose_spec.2.2
    rw [peerPutPrefix_run, hr] at ha
    refine ⟨ha, retained.bounded hi.bounded, ?_⟩
    intro stamp released
    rw [retained.1]
    rcases AccessEvent.released_append.mp released with old | fresh
    · exact hi.pastBounded _ old
    · obtain ⟨pid, p, _, hp, _, rfl⟩ := peerPutEvents_release peer w stamp fresh
      apply hi.bounded pid p.internalId
      change (w.k.wg.bind (fun d => d.peers[pid]?)).map (·.internalId) = _
      rw [hp]; rfl

theorem creation_lift_preserves (a : M α) (ha : SamePeerSnapshot a) :
    PrefixPreserves CreationInv AccessEvent.Safe (liftPrefix a) :=
  ((creation_lift (fun _ => True) a ha).consequence
    (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => hi.1)).preserves

theorem wgGetDeviceDonePrefix_creation_preserves (ctx : DumpCtx) :
    PrefixPreserves CreationInv AccessEvent.Safe (wgGetDeviceDonePrefix ctx) := by
  unfold wgGetDeviceDonePrefix
  exact PrefixPreserves.bind
    (creation_lift_preserves _ (samePeerSnapshot_of_sameKernel (sameKernel_branch _ _)))
    (fun _ => peerPutPrefix_creation_preserves ctx.nextPeer)

theorem dstCacheResetPrefix_hidden_failure (pid : PeerId) (w : World) (h : List PeerEvent)
    (e : Stop) (ha : w.armRecords = true) (hc : w.dstCacheRecords = true)
    (hr : (hiddenJiffies .dstCacheResetTs).run w = .error e) :
    runPrefix (dstCacheResetPrefix pid) w h = (.error e, h) := by
  simp [dstCacheResetPrefix, runPrefix_bind, StateT.run_get, ha, hc, hr]

/-- The first initializer's record failure happens after allocation and its
initial write, which remain visible despite the absence of a final World. -/
theorem creation_core_clock_failure (pid : PeerId) (key : Key) (w : World)
    (h : List PeerEvent) (e : Stop) (hd : w.k.wg.isSome = true)
    (ha : w.armRecords = true) (hc : w.dstCacheRecords = true)
    (hr : (hiddenJiffies .dstCacheResetTs).run (creationCoreWorld w pid key) = .error e) :
    runPrefix (do peerCreateCorePrefix pid key; dstCacheResetPrefix pid) w h =
      (.error e, h ++ [.allocate pid (w.k.peerCounter + 1), .write pid (w.k.peerCounter + 1)]) := by
  rw [runPrefix_bind, peerCreateCorePrefix_run, peerCreateCore_run]
  simp only [hd, ↓reduceIte]
  exact dstCacheResetPrefix_hidden_failure pid _ _ e ha hc hr

/-- Finite sequences of the three complete original callers, discarding their
ordinary return values but retaining the exact World and first Stop. -/
inductive CreationCall where
  | create (key : Key) (psk : Option Key)
  | put (peer : Option PeerId)
  | dumpDone (ctx : DumpCtx)

namespace CreationCall

def original : CreationCall → M Unit
  | .create key psk => do let _ ← peerCreate key psk; pure ()
  | .put peer => peerPut peer
  | .dumpDone ctx => wgGetDeviceDone ctx

def observed : CreationCall → PrefixM PeerEvent Unit
  | .create key psk => do let _ ← peerCreatePrefix key psk; pure ()
  | .put peer => peerPutPrefix peer
  | .dumpDone ctx => wgGetDeviceDonePrefix ctx

def execute : List CreationCall → M Unit
  | [] => pure ()
  | call :: calls => call.original >>= fun _ => execute calls

def observe : List CreationCall → PrefixM PeerEvent Unit
  | [] => pure ()
  | call :: calls => call.observed >>= fun _ => observe calls

theorem erases (call : CreationCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | create key psk => exact erasesPrefix_bind (peerCreatePrefix_erases key psk) (fun _ => erasesPrefix_pure ())
  | put peer => exact peerPutPrefix_erases peer
  | dumpDone ctx => exact wgGetDeviceDonePrefix_erases ctx

theorem preserves (call : CreationCall) : PrefixPreserves CreationInv AccessEvent.Safe call.observed := by
  cases call with
  | create key psk =>
    exact PrefixPreserves.bind (peerCreatePrefix_preserves key psk)
      (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.access.1) ())
  | put peer => exact peerPutPrefix_creation_preserves peer
  | dumpDone ctx => exact wgGetDeviceDonePrefix_creation_preserves ctx

theorem observe_erases (calls : List CreationCall) : ErasesPrefix (observe calls) (execute calls) := by
  induction calls with
  | nil => exact erasesPrefix_pure ()
  | cons call calls ih => exact erasesPrefix_bind call.erases (fun _ => ih)

theorem observe_preserves (calls : List CreationCall) :
    PrefixPreserves CreationInv AccessEvent.Safe (observe calls) := by
  induction calls with
  | nil => exact PrefixPreserves.pure (fun _ _ h => h.access.1) ()
  | cons call calls ih => exact PrefixPreserves.bind call.preserves (fun _ => ih)

end CreationCall

end Leanux.Proofs.WG.Peers
