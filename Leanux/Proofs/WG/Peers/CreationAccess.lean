import Leanux.Proofs.WG.Peers.Allocation
import Leanux.Proofs.WG.Peers.Access
import Leanux.Proofs.WG.Lifetimes.Events
import Leanux.Proofs.Logged.WGPrefix

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Peer creation observed at insertion and throughout initialization. Generic
contracts retain actual product actions; concrete observers run on WG/Ambient.
The invariant bounds resident and previously released identities, distinguishing
fresh allocations from arbitrary initial history. -/
namespace Leanux.Proofs.WG.Peers
open Leanux Leanux.WG Leanux.Proofs.WG.Lifetimes
open Leanux.Proofs.Framing Leanux.Proofs.Logged
structure CreationStoreInv (h : List PeerEvent) (s : Store PeerId) : Prop where
  access : AccessEvent.Safe h ∧ Unique s ∧ ∀ stamp, AccessEvent.Released h stamp → Absent s stamp
  bounded : Bounded s
  pastBounded : ∀ stamp, AccessEvent.Released h stamp → stamp ≤ s.frontier

theorem CreationStoreInv.congr (hi : CreationStoreInv h w) (he : v = w) :
    CreationStoreInv h v := he ▸ hi
theorem CreationStoreInv.read (hi : CreationStoreInv h w)
    (hl : w.slots pid = some stamp) :
    CreationStoreInv (h ++ [.read pid stamp]) w := by
  have hn : ¬ AccessEvent.Released h stamp := fun hr => hi.access.2.2 _ hr pid hl
  refine ⟨⟨AccessEvent.safe_append_read hi.access.1 hn, hi.access.2.1, ?_⟩,
    hi.bounded, ?_⟩
  · intro s hs
    exact hi.access.2.2 s (AccessEvent.released_append_read.mp hs)
  · intro s hs
    exact hi.pastBounded s (AccessEvent.released_append_read.mp hs)

theorem CreationStoreInv.write (hi : CreationStoreInv h w)
    (hl : w.slots pid = some stamp) :
    CreationStoreInv (h ++ [.write pid stamp]) w := by
  have hn : ¬ AccessEvent.Released h stamp := fun hr => hi.access.2.2 _ hr pid hl
  refine ⟨⟨AccessEvent.safe_append_write hi.access.1 hn, hi.access.2.1, ?_⟩,
    hi.bounded, ?_⟩
  · intro s hs
    exact hi.access.2.2 s (AccessEvent.released_append_write.mp hs)
  · intro s hs
    exact hi.pastBounded s (AccessEvent.released_append_write.mp hs)
theorem CreationStoreInv.allocate (hi : CreationStoreInv h w)
    (he : v = w.allocate pid) :
    CreationStoreInv (h ++ [.allocate pid (w.frontier + 1),
      .write pid (w.frontier + 1)]) v := by
  have hn : ¬ AccessEvent.Released h (w.frontier + 1) := by
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

variable {S α : Type}
abbrev CreationSpec (view : S → Store PeerId) (P : Store PeerId → Prop)
    (g : PrefixT PeerEvent S α) (Q : α → Store PeerId → Prop) :=
  PrefixEnsures (fun h w => CreationStoreInv h (view w) ∧ P (view w))
    AccessEvent.Safe g (fun x h w => CreationStoreInv h (view w) ∧ Q x (view w))

theorem creation_pure (view : S → Store PeerId) (P : Store PeerId → Prop) (x : α) :
    CreationSpec view P (pure x) (fun _ => P) :=
  PrefixEnsures.pure (fun _ _ hi => hi.1.access.1) (fun _ _ hi => hi)

theorem creation_lift (view : S → Store PeerId) (P : Store PeerId → Prop)
    (a : StateT S (Except Stop) α) (ha : SameView view a) :
    CreationSpec view P (liftPrefix a) (fun _ => P) := by
  apply PrefixEnsures.lift a (fun _ _ hi => hi.1.access.1)
  intro h w x v hi hr
  have he := (ProjectedAction.iff_run _ _ _).mp ha w x v hr
  exact ⟨hi.1.congr he, he ▸ hi.2⟩

theorem creation_forget {view : S → Store PeerId} {P : Store PeerId → Prop}
    {g : PrefixT PeerEvent S α} {Q R : α → Store PeerId → Prop}
    (hg : CreationSpec view P g Q) (hq : ∀ x s, Q x s → R x s) :
    CreationSpec view P g R :=
  hg.consequence (fun _ _ h => h) (fun x _ _ h => ⟨h.1, hq x _ h.2⟩)

theorem creation_world (view : S → Store PeerId) (P : Store PeerId → Prop) :
    CreationSpec view P (liftPrefix (get : StateT S (Except Stop) S)) (fun _ => P) := by
  apply creation_lift
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w x v hr
  cases hr
  rfl

theorem creation_lift_preserves (view : S → Store PeerId)
    (a : StateT S (Except Stop) α) (ha : SameView view a) :
    PrefixPreserves (fun h w => CreationStoreInv h (view w)) AccessEvent.Safe (liftPrefix a) :=
  ((creation_lift view (fun _ => True) a ha).consequence
    (fun _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ hi => hi.1)).preserves

abbrev CreationInv (h : List PeerEvent) (wg : WGWorld) :=
  CreationStoreInv h (snapshot wg)

abbrev WGCreationSpec (P : Store PeerId → Prop) (g : WGPrefix PeerEvent α)
    (Q : α → Store PeerId → Prop) :=
  StatePrefixEnsures (fun h w _ => CreationInv h w ∧ P (snapshot w)) AccessEvent.Safe g
    (fun x h w _ => CreationInv h w ∧ Q x (snapshot w))

theorem creation_state_pure (P : Store PeerId → Prop) (x : α) :
    WGCreationSpec P (pure x) (fun _ => P) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi.1.access.1) (fun _ _ _ hi => hi)

theorem creation_state_lift (P : Store PeerId → Prop) (a : WG.M α)
    (ha : SameView snapshot a) :
    WGCreationSpec P (liftWGPrefix a) (fun _ => P) := by
  apply StatePrefixEnsures.lift a (fun _ _ _ hi => hi.1.access.1)
  intro h w ambient x v ambient' hi hr
  have he := (ProjectedAction.iff_run_ambient _ _ _).mp ha w ambient x v ambient' hr
  exact ⟨hi.1.congr he, he ▸ hi.2⟩

theorem creation_state_forget {P : Store PeerId → Prop} {g : WGPrefix PeerEvent α}
    {Q R : α → Store PeerId → Prop}
    (hg : WGCreationSpec P g Q) (hq : ∀ x s, Q x s → R x s) :
    WGCreationSpec P g R :=
  hg.consequence (fun _ _ _ h => h) (fun x _ _ _ h => ⟨h.1, hq x _ h.2⟩)

theorem creation_state_world (P : Store PeerId → Prop) :
    WGCreationSpec P (liftWGPrefix (get : WG.M WGWorld)) (fun _ => P) := by
  apply creation_state_lift
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  rfl

/-- Initial contents at the non-failing allocation cut. An occupied nextPeer
slot may be overwritten; its observer records allocation/write and no invented
release of the old resident. -/
def createdPeer (publicKey : Key) (internalId : Nat) : Peer :=
  { remoteStatic := publicKey, presharedKey := List.replicate 32 0,
    precomputedStaticStatic := List.replicate 32 0, internalId,
    cookieDecryptionKey := blake2s 32 [] ("cookie--".toUTF8.toList ++ publicKey),
    cookieMac1Key := blake2s 32 [] ("mac1----".toUTF8.toList ++ publicKey) }

def peerCreateCore (pid : PeerId) (publicKey : Key) : WG.M Unit := do
  let internalId := (← get).peerCounter + 1
  modify fun w => { w with peerCounter := internalId }
  modifyDev fun d => { d with nextPeer := pid + 1 }
  setPeer pid (createdPeer publicKey internalId)

def peerCreateCorePrefix (pid : PeerId) (publicKey : Key) : WGPrefix PeerEvent Unit :=
  fun w ambient => ExceptT.mk fun h => (((peerCreateCore pid publicKey).run w).run ambient,
    if w.dev.isSome then h ++ [.allocate pid (w.peerCounter + 1), .write pid (w.peerCounter + 1)]
    else h)

@[simp] theorem peerCreateCorePrefix_run (pid : PeerId) (key : Key)
    (w : WGWorld) (ambient : Ambient) (h : List PeerEvent) :
    runStatePrefix (peerCreateCorePrefix pid key) w ambient h =
      (((peerCreateCore pid key).run w).run ambient,
        if w.dev.isSome then h ++ [.allocate pid (w.peerCounter + 1), .write pid (w.peerCounter + 1)]
        else h) := rfl

theorem peerCreateCorePrefix_erases (pid : PeerId) (key : Key) :
    ErasesStatePrefix (peerCreateCorePrefix pid key) (peerCreateCore pid key) := fun _ _ _ => rfl

def creationCoreWorld (w : WGWorld) (pid : PeerId) (publicKey : Key) : WGWorld :=
  { w with
    peerCounter := w.peerCounter + 1
    dev := w.dev.map fun d => { d with
      nextPeer := pid + 1
      peers := d.peers.insert pid (createdPeer publicKey (w.peerCounter + 1)) } }

theorem peerCreateCore_run (pid : PeerId) (key : Key) (w : WGWorld) (ambient : Ambient) :
    ((peerCreateCore pid key).run w).run ambient = .ok (((), creationCoreWorld w pid key), ambient) := by
  simp [peerCreateCore, creationCoreWorld, modifyDev, setPeer,
    StateT.run_bind, StateT.run_get, StateT.run_modify]
  cases w.dev <;> rfl

theorem creationCore_snapshot (pid : PeerId) (key : Key) (w : WGWorld) (d : Device)
    (hd : w.dev = some d) :
    snapshot (creationCoreWorld w pid key) = (snapshot w).allocate pid := by
  simpa [creationCoreWorld, snapshot, hd, mapStore] using
    mapStore_allocate w.peerCounter d.peers pid (createdPeer key (w.peerCounter + 1)) rfl

theorem peerCreateCorePrefix_preserves (pid : PeerId) (key : Key) :
    StatePrefixPreserves (fun h w _ => CreationInv h w) AccessEvent.Safe
      (peerCreateCorePrefix pid key) := by
  intro w ambient h hi
  change ∃ suffix, (runStatePrefix (peerCreateCorePrefix pid key) w ambient h).2 = h ++ suffix ∧
    AccessEvent.Safe (runStatePrefix (peerCreateCorePrefix pid key) w ambient h).2 ∧
    match (runStatePrefix (peerCreateCorePrefix pid key) w ambient h).1 with
    | .error _ => True
    | .ok ((_, v), _) => CreationInv (runStatePrefix (peerCreateCorePrefix pid key) w ambient h).2 v
  rw [peerCreateCorePrefix_run, peerCreateCore_run]
  cases hd : w.dev with
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
    exact ⟨[.allocate pid (w.peerCounter + 1), .write pid (w.peerCounter + 1)],
      rfl, hinv.access.1, hinv⟩

/-- A proof-side regrouping of exactly the original creation body. -/
def peerCreateFactored (key : Key) (psk : Option Key) : WG.M (Except Int PeerId) := do
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

theorem core_creation_spec (pid : PeerId) (key : Key) :
    WGCreationSpec (fun _ => True) (peerCreateCorePrefix pid key) (fun _ _ => True) :=
  (show StatePrefixEnsures (fun h w _ => CreationInv h w) AccessEvent.Safe
      (peerCreateCorePrefix pid key) (fun _ h w _ => CreationInv h w)
      from peerCreateCorePrefix_preserves pid key).consequence
    (fun _ _ _ h => h.1) (fun _ _ _ _ h => ⟨h, True.intro⟩)


def dstCacheResetPrefix (pid : PeerId) : WGPrefix PeerEvent Unit := do
  if !((← liftWGPrefix getAmbient).armRecords && (← liftWGPrefix (get : WG.M WGWorld)).dstCacheRecords) then return
  let ts ← liftWGPrefix (hiddenJiffies .dstCacheResetTs)
  let p ← getPeerPrefix pid
  setPeerPrefix pid { p with dstCache := { p.dstCache with resetTs := ts } }

def resetLastSentHandshakePrefix (pid : PeerId) : WGPrefix PeerEvent Unit := do
  let now ← liftWGPrefix (hiddenClock64 .resetLastSent)
  setPeerPrefix pid { (← getPeerPrefix pid) with
    lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }

def precomputeStaticStaticPrefix (pid : PeerId) : WGPrefix PeerEvent Unit := do
  requireNotPendingPrefix pid "recomputing the static-static key"
  let identity := (← liftWGPrefix getDev).staticIdentity
  let p ← getPeerPrefix pid
  let zero ← do
    if ← liftWGPrefix (branch .precomputeNoIdentity !identity.hasIdentity) then pure true
    else
      let (out, nonNull) := curve25519 identity.staticPrivate p.remoteStatic
      setPeerPrefix pid { p with precomputedStaticStatic := out }
      liftWGPrefix (branch .precomputeNullPoint !nonNull)
  if zero then setPeerPrefix pid { (← getPeerPrefix pid) with precomputedStaticStatic := List.replicate 32 0 }

def handshakeInitPrefix (pid : PeerId) (psk : Option Key) : WGPrefix PeerEvent Unit := do
  setPeerPrefix pid { (← getPeerPrefix pid) with handshakeEntryPeer := some pid }
  if ← liftWGPrefix (branch .handshakeInitHasPsk psk.isSome) then
    let p ← getPeerPrefix pid
    setPeerPrefix pid { p with presharedKey := psk.getD p.presharedKey }
  precomputeStaticStaticPrefix pid

theorem dstCacheResetPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (dstCacheResetPrefix pid) (dstCacheReset pid) := by
  unfold dstCacheResetPrefix dstCacheReset
  repeat' first
    | contradiction
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | exact getPeerPrefix_erases _
    | exact setPeerPrefix_erases _ _
    | apply erasesStatePrefix_bind
    | dsimp only
    | split
    | intro x

theorem resetLastSentHandshakePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (resetLastSentHandshakePrefix pid) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshakePrefix resetLastSentHandshake
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _ =>
    erasesStatePrefix_bind (getPeerPrefix_erases _) (fun _ => setPeerPrefix_erases _ _))

theorem precomputeStaticStaticPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (precomputeStaticStaticPrefix pid) (precomputeStaticStatic pid) := by
  unfold precomputeStaticStaticPrefix precomputeStaticStatic
  repeat' first
    | contradiction
    | exact requireNotPendingPrefix_erases _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | exact getPeerPrefix_erases _
    | exact setPeerPrefix_erases _ _
    | apply erasesStatePrefix_bind
    | dsimp only
    | split
    | intro x

theorem handshakeInitPrefix_erases (pid : PeerId) (psk : Option Key) :
    ErasesStatePrefix (handshakeInitPrefix pid psk) (handshakeInit pid psk) := by
  unfold handshakeInitPrefix handshakeInit IndexOwner.setPeerWord
  simp only [bind_assoc]
  repeat' first
    | contradiction
    | exact precomputeStaticStaticPrefix_erases _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | exact getPeerPrefix_erases _
    | exact setPeerPrefix_erases _ _
    | apply erasesStatePrefix_bind
    | dsimp only
    | split
    | intro x

theorem dstCacheResetPrefix_hidden_failure (pid : PeerId) (w : WGWorld)
    (ambient : Ambient) (h : List PeerEvent) (e : Stop)
    (ha : ambient.armRecords = true) (hc : w.dstCacheRecords = true)
    (hr : ((hiddenJiffies .dstCacheResetTs : WG.M UInt64).run w).run ambient = .error e) :
    runStatePrefix (dstCacheResetPrefix pid) w ambient h = (.error e, h) := by
  simp [dstCacheResetPrefix, runStatePrefix_bind, runStatePrefix_lift,
    liftWGPrefix, getAmbient, StateT.run_get, ha, hc, hr]

/-- A clock Stop after the allocation cut retains its observed events,
with no final WG or Ambient endpoint. -/
theorem creation_core_clock_failure (pid : PeerId) (key : Key) (w : WGWorld)
    (ambient : Ambient) (h : List PeerEvent) (e : Stop) (hd : w.dev.isSome = true)
    (ha : ambient.armRecords = true) (hc : w.dstCacheRecords = true)
    (hr : ((hiddenJiffies .dstCacheResetTs : WG.M UInt64).run
      (creationCoreWorld w pid key)).run ambient = .error e) :
    runStatePrefix (do peerCreateCorePrefix pid key; dstCacheResetPrefix pid) w ambient h =
      (.error e, h ++ [.allocate pid (w.peerCounter + 1), .write pid (w.peerCounter + 1)]) := by
  rw [runStatePrefix_bind, peerCreateCorePrefix_run, peerCreateCore_run]
  simp only [hd, ↓reduceIte]
  exact dstCacheResetPrefix_hidden_failure pid _ _ _ e ha hc hr

theorem creation_get (P : Store PeerId → Prop) (pid : PeerId) :
    WGCreationSpec P (getPeerPrefix pid) (fun p s => P s ∧ s.slots pid = some p.internalId) := by
  intro w ambient h hi
  have he := getPeerPrefix_run pid w ambient h
  change runPrefix ((getPeerPrefix pid).run w) ambient h = _ at he
  rw [he]
  cases hr : ((getPeer pid).run w).run ambient with
  | error _ => exact ⟨[], by simp, hi.1.access.1, True.intro⟩
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, live⟩ := getPeer_current pid w v p ambient ambient' hr
    have hn := hi.1.read live
    exact ⟨[.read pid p.internalId], rfl, hn.access.1, hn, hi.2, live⟩

theorem creation_set (P : Store PeerId → Prop) (pid : PeerId) (p : Peer) :
    WGCreationSpec (fun s => P s ∧ s.slots pid = some p.internalId)
      (setPeerPrefix pid p) (fun _ => P) := by
  intro w ambient h hi
  have he := setPeerPrefix_run pid p w ambient h
  change runPrefix ((setPeerPrefix pid p).run w) ambient h = _ at he
  rw [he]
  cases hd : w.dev with
  | none => simp [snapshot, hd] at hi
  | some d =>
    have hr : ((setPeer pid p).run w).run ambient = .ok (((),
        { w with dev := some { d with peers := d.peers.insert pid p } }), ambient) := by
      simp [setPeer, modifyDev, hd]
    rw [hr]
    simp only [Option.isSome_some, ↓reduceIte]
    have hs := setPeer_same pid p w _ ambient ambient hi.2.2 hr
    have hn := (hi.1.write hi.2.2).congr hs
    exact ⟨[.write pid p.internalId], rfl, hn.access.1, hn, hs ▸ hi.2.1⟩

theorem creation_dev (P : Store PeerId → Prop) :
    WGCreationSpec P (liftWGPrefix getDev) (fun _ => P) := by
  apply creation_state_lift
  apply SameView.of_wp
  intro initial
  mvcgen [getDev, invariant, AmbientM.invariant]
  all_goals simp_all

theorem creation_require (P : Store PeerId → Prop) (pid : PeerId) (what : String) :
    WGCreationSpec P (requireNotPendingPrefix pid what) (fun _ => P) := by
  exact creation_state_pure P ()
theorem dstCacheResetPrefix_spec (P : Store PeerId → Prop) (pid : PeerId) :
    WGCreationSpec P (dstCacheResetPrefix pid) (fun _ => P) := by
  unfold dstCacheResetPrefix
  apply StatePrefixEnsures.bind (creation_state_lift P _ (fun initial => hoare_liftAmbient (get : AmbientM Ambient) (fun w => snapshot w = initial)))
  intro ambient
  apply StatePrefixEnsures.bind (creation_state_world P)
  intro w
  split
  · exact creation_state_pure _ ()
  · apply StatePrefixEnsures.bind (creation_state_lift P _ (fun initial => hoare_liftAmbient (AmbientM.hiddenJiffies _) (fun w => snapshot w = initial)))
    intro ts
    apply StatePrefixEnsures.bind (creation_get P pid)
    intro p
    exact creation_set P pid { p with dstCache := { p.dstCache with resetTs := ts } }

theorem resetLastSentHandshakePrefix_spec (P : Store PeerId → Prop) (pid : PeerId) :
    WGCreationSpec P (resetLastSentHandshakePrefix pid) (fun _ => P) := by
  unfold resetLastSentHandshakePrefix
  apply StatePrefixEnsures.bind (creation_state_lift P _ (fun initial => hoare_liftAmbient (AmbientM.hiddenClock64 _) (fun w => snapshot w = initial)))
  intro now
  apply StatePrefixEnsures.bind (creation_get P pid)
  intro p
  exact creation_set P pid { p with lastSentHandshake := now - (REKEY_TIMEOUT + 1 : Nat).toInt64 * NSEC_PER_SEC64 }

theorem precomputeStaticStaticPrefix_spec (P : Store PeerId → Prop) (pid : PeerId) :
    WGCreationSpec P (precomputeStaticStaticPrefix pid) (fun _ => P) := by
  unfold precomputeStaticStaticPrefix
  apply StatePrefixEnsures.bind (creation_require P pid _)
  intro _
  apply StatePrefixEnsures.bind (creation_dev P)
  intro d
  apply StatePrefixEnsures.bind (creation_get P pid)
  intro p
  apply StatePrefixEnsures.bind (creation_state_lift (fun s => P s ∧ s.slots pid = some p.internalId) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => snapshot w = initial)))
  intro b
  split
  · dsimp only
    simp only [pure_bind, ↓reduceIte]
    apply StatePrefixEnsures.bind (creation_get (fun s => P s ∧ s.slots pid = some p.internalId) pid)
    intro q
    exact creation_state_forget (creation_set (fun s => P s ∧ s.slots pid = some p.internalId) pid { q with precomputedStaticStatic := List.replicate 32 0 })
      (fun _ _ h => h.1)
  · dsimp only
    apply StatePrefixEnsures.bind (creation_set P pid
      { p with precomputedStaticStatic := (curve25519 d.staticIdentity.staticPrivate p.remoteStatic).1 })
    intro _
    apply StatePrefixEnsures.bind (creation_state_lift P _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => snapshot w = initial)))
    intro zero
    dsimp only
    split
    · apply StatePrefixEnsures.bind (creation_get P pid)
      intro q
      exact creation_set P pid { q with precomputedStaticStatic := List.replicate 32 0 }
    · exact creation_state_pure P ()

theorem handshakeInitPrefix_spec (P : Store PeerId → Prop) (pid : PeerId) (psk : Option Key) :
    WGCreationSpec P (handshakeInitPrefix pid psk) (fun _ => P) := by
  unfold handshakeInitPrefix
  apply StatePrefixEnsures.bind (creation_get P pid)
  intro p
  apply StatePrefixEnsures.bind (creation_set P pid {p with handshakeEntryPeer := some pid})
  intro _
  apply StatePrefixEnsures.bind (creation_state_lift P _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => snapshot w = initial)))
  intro b
  split
  · apply StatePrefixEnsures.bind (creation_get P pid)
    intro p
    apply StatePrefixEnsures.bind (creation_set P pid { p with presharedKey := psk.getD p.presharedKey })
    intro _
    exact precomputeStaticStaticPrefix_spec P pid
  · exact precomputeStaticStaticPrefix_spec P pid

def peerCreatePrefix (key : Key) (psk : Option Key) : WGPrefix PeerEvent (Except Int PeerId) := do
  let d ← liftWGPrefix getDev
  if ← liftWGPrefix (branchCmp .peerCreateMaxPeers (d.numPeers ≥ MAX_PEERS_PER_DEVICE) d.numPeers MAX_PEERS_PER_DEVICE) then
    return .error (-ENOMEM)
  if ← liftWGPrefix (branch .peerCreateNoMem !(← liftWGPrefix (hiddenAlloc .kmemCacheZallocPeer))) then
    return .error (-ENOMEM)
  if ← liftWGPrefix (branch .peerCreateDstCacheFail false) then return .error (-ENOMEM)
  let pid := d.nextPeer
  peerCreateCorePrefix pid key
  dstCacheResetPrefix pid
  handshakeInitPrefix pid psk
  resetLastSentHandshakePrefix pid
  liftWGPrefix (modifyDev fun d => { d with peerList := d.peerList ++ [pid], peerHashtable := (key, pid) :: d.peerHashtable, numPeers := d.numPeers + 1 })
  return .ok pid

theorem peerCreatePrefix_erases (key : Key) (psk : Option Key) :
    ErasesStatePrefix (peerCreatePrefix key psk) (peerCreate key psk) := by
  rw [← peerCreateFactored_eq]
  unfold peerCreatePrefix peerCreateFactored
  repeat' first
    | contradiction
    | exact peerCreateCorePrefix_erases _ _
    | exact dstCacheResetPrefix_erases _
    | exact handshakeInitPrefix_erases _ _
    | exact resetLastSentHandshakePrefix_erases _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | dsimp only
    | split
    | intro x

theorem modifyDev_samePeerSnapshot (f : Device → Device) (hf : ∀ d, (f d).peers = d.peers) :
    SamePeerSnapshot (modifyDev f) := by
  apply samePeerSnapshot_of_wp
  intro s
  exact modifyDev_peer_spec (fun t => t = s) f hf

theorem peerCreatePrefix_preserves (key : Key) (psk : Option Key) :
    StatePrefixPreserves (fun h w _ => CreationInv h w) AccessEvent.Safe (peerCreatePrefix key psk) := by
  have full : WGCreationSpec (fun _ => True) (peerCreatePrefix key psk) (fun _ _ => True) := by
    unfold peerCreatePrefix
    apply StatePrefixEnsures.bind (creation_dev (fun _ => True))
    intro d
    apply StatePrefixEnsures.bind (creation_state_lift (fun _ => True) _
      (fun initial => hoare_liftAmbient (AmbientM.branchCmp _ _ _ _) (fun w => snapshot w = initial)))
    intro full
    split
    · exact creation_state_pure (fun _ => True) _
    · apply StatePrefixEnsures.bind (creation_state_lift (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.hiddenAlloc _) (fun w => snapshot w = initial)))
      intro allocated
      apply StatePrefixEnsures.bind (creation_state_lift (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => snapshot w = initial)))
      intro failed
      split
      · exact creation_state_pure (fun _ => True) _
      · apply StatePrefixEnsures.bind (creation_state_lift (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => snapshot w = initial)))
        intro failed
        split
        · exact creation_state_pure (fun _ => True) _
        · apply StatePrefixEnsures.bind (core_creation_spec d.nextPeer key)
          intro _
          apply StatePrefixEnsures.bind (dstCacheResetPrefix_spec (fun _ => True) d.nextPeer)
          intro _
          apply StatePrefixEnsures.bind (handshakeInitPrefix_spec (fun _ => True) d.nextPeer psk)
          intro _
          apply StatePrefixEnsures.bind (resetLastSentHandshakePrefix_spec (fun _ => True) d.nextPeer)
          intro _
          apply StatePrefixEnsures.bind (creation_state_lift (fun _ => True) _
            (modifyDev_samePeerSnapshot
              (fun v => { v with peerList := v.peerList ++ [d.nextPeer], peerHashtable := (key, d.nextPeer) :: v.peerHashtable, numPeers := v.numPeers + 1 })
              (fun _ => rfl)))
          intro _
          exact creation_state_pure (fun _ => True) _
  exact full.consequence (fun _ _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ _ hi => hi.1)


theorem peerPutPrefix_creation_preserves (peer : Option PeerId) :
    StatePrefixPreserves (fun h w _ => CreationInv h w) AccessEvent.Safe (peerPutPrefix peer) := by
  intro w ambient h hi
  have he : runPrefix ((peerPutPrefix peer).run w) ambient h =
      (((peerPut peer).run w).run ambient, h ++ peerPutEvents peer w) :=
    peerPutPrefix_run peer w ambient h
  rw [he]
  refine ⟨peerPutEvents peer w, rfl, peerPutEvents_safe peer w h hi.access, ?_⟩
  cases hr : ((peerPut peer).run w).run ambient with
  | error _ => trivial
  | ok out =>
    rcases out with ⟨⟨result, v⟩, ambient'⟩
    cases result
    have retained := (ProjectedAction.iff_run_ambient _ _ _).mp (peerPut_retained peer)
      w ambient () v ambient' hr
    have ha := (peerPutPrefix_preserves peer w ambient h hi.access).choose_spec.2.2
    rw [he, hr] at ha
    refine ⟨ha, retained.bounded hi.bounded, ?_⟩
    intro stamp released
    rw [retained.1]
    rcases AccessEvent.released_append.mp released with old | fresh
    · exact hi.pastBounded _ old
    · obtain ⟨pid, p, _, hp, _, rfl⟩ := peerPutEvents_release peer w stamp fresh
      apply hi.bounded pid p.internalId
      change (w.dev.bind (fun d => d.peers[pid]?)).map (·.internalId) = _
      rw [hp]; rfl

theorem wgGetDeviceDonePrefix_creation_preserves (ctx : DumpCtx) :
    StatePrefixPreserves (fun h w _ => CreationInv h w) AccessEvent.Safe (wgGetDeviceDonePrefix ctx) := by
  unfold wgGetDeviceDonePrefix
  apply StatePrefixEnsures.bind (g := liftWGPrefix (branch .getDoneHasWg ctx.hasWg))
  · exact (creation_state_lift (fun _ => True) _
      (fun initial => hoare_liftAmbient (AmbientM.branch _ _) (fun w => snapshot w = initial))).consequence
        (fun _ _ _ hi => ⟨hi, True.intro⟩) (fun _ _ _ _ hi => hi.1)
  · intro _
    exact peerPutPrefix_creation_preserves ctx.nextPeer
/-- Complete original callers with ordinary return values discarded. An outer
Stop terminates the sequence and retains exactly its observed prefix. -/
inductive CreationCall where
  | create (key : Key) (psk : Option Key)
  | put (peer : Option PeerId)
  | dumpDone (ctx : DumpCtx)

namespace CreationCall

def original : CreationCall → WG.M Unit
  | .create key psk => do let _ ← peerCreate key psk; pure ()
  | .put peer => peerPut peer
  | .dumpDone ctx => wgGetDeviceDone ctx

def observed : CreationCall → WGPrefix PeerEvent Unit
  | .create key psk => do let _ ← peerCreatePrefix key psk; pure ()
  | .put peer => peerPutPrefix peer
  | .dumpDone ctx => wgGetDeviceDonePrefix ctx

def execute : List CreationCall → WG.M Unit
  | [] => pure ()
  | call :: calls => call.original >>= fun _ => execute calls

def observe : List CreationCall → WGPrefix PeerEvent Unit
  | [] => pure ()
  | call :: calls => call.observed >>= fun _ => observe calls

theorem erases (call : CreationCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | create key psk => exact erasesStatePrefix_bind (peerCreatePrefix_erases key psk) (fun _ => erasesStatePrefix_pure ())
  | put peer => exact peerPutPrefix_erases peer
  | dumpDone ctx => exact wgGetDeviceDonePrefix_erases ctx

theorem preserves (call : CreationCall) : StatePrefixPreserves (fun h w _ => CreationInv h w) AccessEvent.Safe call.observed := by
  cases call with
  | create key psk =>
    exact StatePrefixEnsures.bind (peerCreatePrefix_preserves key psk)
      (fun _ => StatePrefixEnsures.pure () (fun _ _ _ hi => hi.access.1) (fun _ _ _ hi => hi))
  | put peer => exact peerPutPrefix_creation_preserves peer
  | dumpDone ctx => exact wgGetDeviceDonePrefix_creation_preserves ctx

theorem observe_erases (calls : List CreationCall) : ErasesStatePrefix (observe calls) (execute calls) := by
  induction calls with
  | nil => exact erasesStatePrefix_pure ()
  | cons call calls ih => exact erasesStatePrefix_bind call.erases (fun _ => ih)

theorem observe_preserves (calls : List CreationCall) :
    StatePrefixPreserves (fun h w _ => CreationInv h w) AccessEvent.Safe (observe calls) := by
  induction calls with
  | nil => exact StatePrefixEnsures.pure () (fun _ _ _ hi => hi.access.1) (fun _ _ _ hi => hi)
  | cons call calls ih => exact StatePrefixEnsures.bind call.preserves (fun _ => ih)

end CreationCall


end Leanux.Proofs.WG.Peers
