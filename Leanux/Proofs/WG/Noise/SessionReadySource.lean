import Leanux.Proofs.WG.Noise.SessionReadyFrames
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Index.SessionCoherenceFrames
import Init.Internal.Order.While

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.WG.Config Std.Do

theorem sessionAllocationRecord_run (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (w : World)
    (present : w.hidden = some ({site := 80, bytes := bytes} :: rest)) :
    (hidden (.alloc .kzallocKeypair)).run w = .ok (bytes, {w with hidden := some rest}) := by
  have passive : HiddenSite.passive 80 = false := by decide
  simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    present, HiddenSite.info, AllocSite.info, AllocSite.hiddenId, passive,
    Worker.sectionId, Worker.index, Except.pure, Except.bind, width,
    List.drop_eq_nil_of_le (by omega : bytes.length ≤ 40), List.take_of_length_le (by omega : bytes.length ≤ 40)]

theorem sessionBirthdateRecord_run (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 8) (w : World)
    (present : w.hidden = some ({site := 13, bytes := bytes} :: rest)) :
    (hidden .deriveKeysBirthdate).run w = .ok (bytes, {w with hidden := some rest}) := by
  have passive : HiddenSite.passive 13 = false := by decide
  simp [hidden, skipAmbient, noteNetRxStart, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    present, HiddenSite.info, passive,
    Worker.sectionId, Worker.index, Except.pure, Except.bind, width,
    List.drop_eq_nil_of_le (by omega : bytes.length ≤ 8), List.take_of_length_le (by omega : bytes.length ≤ 8)]

def sessionAllocationLoop (encounter : M Bool) (s : Option Bool × Nat) : M (Option Bool × Nat) :=
  Lean.Loop.forIn Lean.Loop.mk s fun _ state => do
    if state.2 < 1 then
      if !(← encounter) then return .done (some false, state.2)
      return .yield (none, state.2 + 1)
    else return .done (none, state.2)

theorem sessionAllocation_source : hiddenAlloc .kzallocKeypair = (do
    let w ← get
    let placeholders := w.hidden.isNone && w.hiddenPlaceholders
    if !placeholders && !w.allocArmed.contains "kzallocKeypair" then return true
    let encounter := if placeholders then
      (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.allocPlaceholder) .kzallocKeypair
      else (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.allocRecord) .kzallocKeypair
    let out ← sessionAllocationLoop encounter (none, 0)
    match out.1 with
    | some result => pure result
    | none => pure true) := by
  simp only [hiddenAlloc, AllocSite.info, sessionAllocationLoop]
  apply bind_congr
  intro w
  split
  · rfl
  · apply bind_congr
    intro out
    cases out.1 <;> rfl

theorem sessionAllocationLoop_unfold (encounter : M Bool) (s : Option Bool × Nat) :
    sessionAllocationLoop encounter s = (do
      if s.2 < 1 then
        if !(← encounter) then return (some false, s.2)
        sessionAllocationLoop encounter (none, s.2 + 1)
      else return (none, s.2)) := by
  unfold sessionAllocationLoop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  split
  · simp only [bind_assoc]
    apply bind_congr
    intro result
    cases result <;> simp
  · rfl

theorem sessionAllocation_returns (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (success : bytes.headD 2 = 1) (P : Kernel → Prop) :
    Returns (hiddenAlloc .kzallocKeypair)
      (fun w => P w.k ∧ w.hidden = some ({site := 80, bytes := bytes} :: rest) ∧
        w.allocArmed.contains "kzallocKeypair" = true)
      (fun ok w => ok = true ∧ P w.k ∧ w.hidden = some rest) := by
  intro w pre
  have record : ((noise_const _private.Leanux.Kernel.Defs.«0».Leanux.allocRecord)
      .kzallocKeypair).run w = .ok (true, {w with hidden := some rest}) := by
    change ((do
      let bs ← hidden (.alloc .kzallocKeypair)
      match bs.headD 2 with
      | 1 => pure true
      | 0 => pure false
      | b => throw (Stop.hidden s!"kzallocKeypair: outcome byte {b}, expected 0 or 1")).run w) = _
    rw [StateT.run_bind,
      sessionAllocationRecord_run bytes rest width w pre.2.1]
    simp only [bind, Except.bind]
    rw [success]
    rfl
  refine ⟨true, {w with hidden := some rest}, ?_, rfl, pre.1, rfl⟩
  rw [sessionAllocation_source]
  simp only [StateT.run_bind, StateT.run_get, pre.2.1, Option.isNone_some,
    Bool.false_and, Bool.not_false, pre.2.2, Bool.not_true, Bool.true_and,
    Bool.false_eq_true, ite_false, pure_bind, Except.bind]
  rw [sessionAllocationLoop_unfold]
  simp only [Nat.zero_lt_one, ite_true, StateT.run_bind, record]
  rw [sessionAllocationLoop_unfold]
  rfl


theorem sessionBirthdate_returns (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 8) (P : Kernel → Prop) :
    Returns (hiddenClock64 .deriveKeysBirthdate)
      (fun w => P w.k ∧ w.hidden = some ({site := 13, bytes := bytes} :: rest))
      (fun _ w => P w.k) := by
  have hh : Returns (hidden .deriveKeysBirthdate)
      (fun w => P w.k ∧ w.hidden = some ({site := 13, bytes := bytes} :: rest))
      (fun _ w => P w.k) := by
    intro w pre
    exact ⟨bytes, {w with hidden := some rest},
      sessionBirthdateRecord_run bytes rest width w pre.2, pre.1⟩
  have hs := (returns_iff _ _ _).mp hh
  rw [returns_iff]
  mvcgen [hiddenClock64, hiddenClock, hs]

theorem sessionCreate_returns (peer : Option PeerId) (d : Device) (counter : Nat)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (success : bytes.headD 2 = 1) :
    Returns (keypairCreate peer)
      (fun w => (w.k.wg = some d ∧ w.k.keypairCounter = counter) ∧
        w.hidden = some ({site := 80, bytes := bytes} :: rest) ∧
        w.allocArmed.contains "kzallocKeypair" = true)
      (fun result w => result = some d.nextKeypairId ∧
        w.k.wg = some (Index.createdDevice d counter peer) ∧
        w.k.keypairCounter = counter + 1 ∧ w.hidden = some rest) := by
  have hh := (returns_iff _ _ _).mp
    (sessionAllocation_returns bytes rest width success
      (fun k => k.wg = some d ∧ k.keypairCounter = counter))
  rw [returns_iff]
  mvcgen [keypairCreate, getDev, getK, setKeypair, modifyDev, modifyK, branch, invariant, hh]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Index.createdDevice]

theorem deriveKeys_returns (kp : KeypairId) (initiator : Bool) (ck : List UInt8)
    (d : Device) (k : Keypair) (resident : d.keypairs[kp]? = some k)
    (bytes : List UInt8) (rest : List HiddenRecord) (width : bytes.length = 8) :
    Returns (deriveKeys kp initiator ck)
      (fun w => w.k.wg = some d ∧ w.hidden = some ({site := 13, bytes := bytes} :: rest))
      (fun _ w => ∃ birth, w.k.wg = some {d with keypairs := d.keypairs.insert kp (sessionDerivedKey k initiator ck birth)}) := by
  have hh := (returns_iff _ _ _).mp
    (sessionBirthdate_returns bytes rest width (fun k => k.wg = some d))
  have hk := sessionKdf_returns ck (fun k => k.wg = some d)
  rw [returns_iff]
  mvcgen [deriveKeys, kdfOut, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK, invariant, hh, hk]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [sessionDerivedKey]
  all_goals grind

theorem sessionPublish_returns (pid : PeerId) (kp : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true) :
    Returns (sessionPublish pid kp) (fun w => w.k.wg = some d)
      (fun ok _ => ok = true) := by
  have someWord : ∃ stored, p.handshakeEntryPeer = some stored := by
    cases h : p.handshakeEntryPeer <;> simp_all
  obtain ⟨stored, hword⟩ := someWord
  rw [returns_iff]
  mvcgen [sessionPublish, IndexOwner.peerDeref, IndexOwner.peerWord, indexReplaceHandshake,
    indexHashed, getPeer, getDev, getK, branch, invariant, unsupported, modifyDev, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all
  all_goals grind


theorem handshakeZero_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (handshakeZero pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some {d with peers := d.peers.insert pid (sessionZeroPeer p)}) := by
  rw [returns_iff]
  mvcgen [handshakeZero, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [sessionZeroPeer]

/-- The original ordered rotation followed immediately by publication. -/
def sessionRotationPublish (pid : PeerId) (kp : KeypairId) : M Bool := do
  addNewKeypair pid kp
  sessionPublish pid kp

theorem sessionRotationPublish_returns (pid : PeerId) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (resident : d.peers[pid]? = some p)
    (key : d.keypairs[kp]? = some k) (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : ClearReady d (rotationReleases (rotationPlan p k.iAmTheInitiator kp))) :
    Returns (sessionRotationPublish pid kp) (fun w => w.k.wg = some d)
      (fun ok _ => ok = true) := by
  apply returns_bind _ _ (addNewKeypair_returns_ready pid kp d p k resident key ready)
  intro u w pre
  obtain ⟨out, device, steps⟩ := pre
  exact sessionPublish_returns pid kp out (rotationPeer (rotationPlan p k.iAmTheInitiator kp) p)
    (rotationRun_peer steps p resident) (by simpa only [rotationPeer_word] using word)
    (rotationRun_handshake_hashed steps pid hashed) w device

/-- The original alive guard at the cut immediately after handshake zeroing. -/
def sessionAliveFinish (pid : PeerId) (kp : KeypairId) : M Bool := do
  if ← branch .sessionAlive !(← getPeer pid).isDead then
    sessionRotationPublish pid kp
  else unsupported "a dead peer finishing a session"

theorem sessionFinish_ready_source (pid : PeerId) (kp : KeypairId) :
    sessionFinish pid kp = (handshakeZero pid >>= fun _ => sessionAliveFinish pid kp) := by rfl

theorem sessionFinish_returns (pid : PeerId) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (resident : d.peers[pid]? = some p)
    (key : d.keypairs[kp]? = some k) (alive : p.isDead = false)
    (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : ClearReady d (rotationReleases (rotationPlan (sessionZeroPeer p) k.iAmTheInitiator kp))) :
    Returns (sessionFinish pid kp) (fun w => w.k.wg = some d) (fun ok _ => ok = true) := by
  let zeroed := {d with peers := d.peers.insert pid (sessionZeroPeer p)}
  have hr := (returns_iff _ _ _).mp (sessionRotationPublish_returns pid kp zeroed
    (sessionZeroPeer p) k (by simp [zeroed]) key word hashed ready)
  rw [sessionFinish_ready_source]
  apply returns_bind _ _ (handshakeZero_returns pid d p resident)
  intro u
  rw [returns_iff]
  mvcgen [sessionAliveFinish, getPeer, getDev, getK, branch, invariant, unsupported, hr]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all only [Std.TreeMap.getElem?_insert_self, Option.some.injEq]
  all_goals subst_vars
  all_goals simp_all [zeroed, sessionZeroPeer]
  all_goals subst_vars
  all_goals simp_all

theorem sessionPrepare_returns (pid : PeerId) (st : Nat) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (resident : d.peers[pid]? = some p)
    (key : d.keypairs[kp]? = some k) (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 8) :
    Returns (sessionPrepare pid st kp)
      (fun w => w.k.wg = some d ∧ w.hidden = some ({site := 13, bytes := bytes} :: rest))
      (fun _ w => ∃ birth, w.k.wg = some (sessionDerivedDevice d kp p k st birth)) := by
  let assigned := {d with keypairs := d.keypairs.insert kp (sessionAssignedKey k p st)}
  have hd := (returns_iff _ _ _).mp (deriveKeys_returns kp
    (st == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey assigned (sessionAssignedKey k p st)
    (by simp [assigned]) bytes rest width)
  rw [returns_iff]
  cases mode : (st == HANDSHAKE_CONSUMED_RESPONSE) <;>
    simp only [sessionPrepare, sessionAssignedKey, mode] at hd ⊢
  all_goals mvcgen [getPeer, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, invariant, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [sessionDerivedDevice, sessionAssignedKey, assigned]
  all_goals subst_vars
  all_goals mvcgen [hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [sessionDerivedDevice, sessionAssignedKey]
  all_goals have mode' : (st == HANDSHAKE_CONSUMED_RESPONSE) = false := by simpa using mode
  all_goals simp_all only [mode']
  all_goals grind

/-- Total original suffix after allocation, under an entry-state release
budget calculated after the allocator's actual overwrite. -/
theorem sessionAfterAllocation_returns_ready (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p) (alive : p.isDead = false)
    (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : SessionReady d p counter)
    (bytes : List UInt8) (rest : List HiddenRecord) (width : bytes.length = 8) :
    Returns (Index.sessionAfterAllocation pid p.handshakeState d.nextKeypairId)
      (fun w => w.k.wg = some (Index.createdDevice d counter p.handshakeEntryPeer) ∧
        w.hidden = some ({site := 13, bytes := bytes} :: rest)) (fun ok _ => ok = true) := by
  rw [sessionAfterAllocation_prepare]
  refine returns_bind _ _ (sessionPrepare_returns pid p.handshakeState d.nextKeypairId
    (Index.createdDevice d counter p.handshakeEntryPeer) p
    {internalId := counter + 1, peer := p.handshakeEntryPeer}
    resident (by simp [Index.createdDevice]) bytes rest width) ?_
  intro u w pre
  obtain ⟨birth, device⟩ := pre
  let derived := sessionDerivedDevice (Index.createdDevice d counter p.handshakeEntryPeer)
    d.nextKeypairId p {internalId := counter + 1, peer := p.handshakeEntryPeer} p.handshakeState birth
  let dk := sessionDerivedKey
    (sessionAssignedKey {internalId := counter + 1, peer := p.handshakeEntryPeer} p p.handshakeState)
    (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey birth
  have key : derived.keypairs[d.nextKeypairId]? = some dk := by
    simp [derived, dk, sessionDerivedDevice]
  have role : dk.iAmTheInitiator = (p.handshakeState == HANDSHAKE_CONSUMED_RESPONSE) := by
    dsimp [dk, sessionDerivedKey]
    split <;> rfl
  have budget : ClearReady derived
      (rotationReleases (rotationPlan (sessionZeroPeer p) dk.iAmTheInitiator d.nextKeypairId)) := by
    rw [role]
    exact sessionPrepared_ready pid d p counter birth ready
  exact sessionFinish_returns pid d.nextKeypairId derived p dk resident key alive word hashed budget w device


theorem sessionAfterCreate_returns_ready (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p) (alive : p.isDead = false)
    (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : SessionReady d p counter)
    (bytes : List UInt8) (rest : List HiddenRecord) (width : bytes.length = 8) :
    Returns (Index.sessionAfterCreate pid p.handshakeState (some d.nextKeypairId))
      (fun w => w.k.wg = some (Index.createdDevice d counter p.handshakeEntryPeer) ∧
        w.hidden = some ({site := 13, bytes := bytes} :: rest)) (fun ok _ => ok = true) := by
  have hs := (returns_iff _ _ _).mp (sessionAfterAllocation_returns_ready pid d p counter
    resident alive word hashed ready bytes rest width)
  rw [returns_iff]
  mvcgen [Index.sessionAfterCreate, branch, invariant, hs]

theorem sessionReadyPeer_read (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (P : World → Prop) :
    Returns (getPeer pid) (fun w => w.k.wg = some d ∧ P w)
      (fun result w => result = p ∧ w.k.wg = some d ∧ P w) := by
  rw [returns_iff]
  mvcgen [getPeer, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

/-- Every concrete realization of the static premises completes the original
entry point successfully; no normal execution is an input hypothesis. -/
theorem beginSession_returns_ready (pid : PeerId) (d : Device) (p : Peer) (counter : Nat)
    (resident : d.peers[pid]? = some p)
    (accepted : p.handshakeState = HANDSHAKE_CREATED_RESPONSE ∨
      p.handshakeState = HANDSHAKE_CONSUMED_RESPONSE)
    (alive : p.isDead = false) (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : SessionReady d p counter) (allocation clock : List UInt8)
    (allocWidth : allocation.length = 40) (allocSuccess : allocation.headD 2 = 1)
    (clockWidth : clock.length = 8) (rest : List HiddenRecord) :
    Returns (beginSession pid)
      (fun w => (w.k.wg = some d ∧ w.k.keypairCounter = counter) ∧
        w.hidden = some (sessionReadyRecords allocation clock rest) ∧
        w.allocArmed.contains "kzallocKeypair" = true)
      (fun ok _ => ok = true) := by
  have hg := (returns_iff _ _ _).mp (sessionReadyPeer_read pid d p resident
    (fun w => w.k.keypairCounter = counter ∧
      w.hidden = some (sessionReadyRecords allocation clock rest) ∧
      w.allocArmed.contains "kzallocKeypair" = true))
  have hc := (returns_iff _ _ _).mp (sessionCreate_returns p.handshakeEntryPeer d counter
    allocation ({site := 13, bytes := clock} :: rest) allocWidth allocSuccess)
  have hs := (returns_iff _ _ _).mp (sessionAfterCreate_returns_ready pid d p counter resident
    alive word hashed ready clock rest clockWidth)
  rw [Index.beginSession_owner_source, returns_iff]
  mvcgen [IndexOwner.peerWord, WG.andM, branch, invariant, hg]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all only [Option.some.injEq]
  all_goals subst_vars
  all_goals try simp_all [sessionReadyRecords, HiddenSite.info, AllocSite.info, AllocSite.hiddenId]
  all_goals mvcgen [hc, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals subst_vars
  all_goals intro s created device count records
  all_goals exact hs s ⟨device, records⟩

end Leanux.Proofs.WG.Noise
