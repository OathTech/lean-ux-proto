import Leanux.Proofs.WG.Noise.SessionReadyFrames
import Leanux.Proofs.WG.Noise.SessionReadyReadFrames
import Leanux.Proofs.WG.Noise.SessionSource
import Leanux.Proofs.WG.Index.SessionCoherenceFrames
import Init.Internal.Order.While

/-! Total native session contracts with explicit ambient record premises.
The allocation loop retains arbitrary callback states; full-product reads are
in `SessionReadyReadFrames`. -/

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG Leanux.Proofs.WG.Config Std.Do

theorem sessionAllocationRecord_run (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (w : Ambient)
    (present : w.hidden = some ({site := 80, bytes := bytes} :: rest)) :
    (AmbientM.hidden (.alloc .kzallocKeypair)).run w = .ok (bytes, {w with hidden := some rest}) := by
  have passive : HiddenSite.passive 80 = false := by decide
  simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    present, HiddenSite.info, AllocSite.info, AllocSite.hiddenId, passive,
    Worker.sectionId, Worker.index, Except.pure, Except.bind, width,
    List.drop_eq_nil_of_le (by omega : bytes.length ≤ 40), List.take_of_length_le (by omega : bytes.length ≤ 40)]

theorem sessionBirthdateRecord_run (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 8) (w : Ambient)
    (present : w.hidden = some ({site := 13, bytes := bytes} :: rest)) :
    (AmbientM.hidden .deriveKeysBirthdate).run w = .ok (bytes, {w with hidden := some rest}) := by
  have passive : HiddenSite.passive 13 = false := by decide
  simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart, StateT.run, bind, pure,
    get, getThe, MonadStateOf.get, set, StateT.bind, StateT.pure, StateT.get, StateT.set,
    present, HiddenSite.info, passive,
    Worker.sectionId, Worker.index, Except.pure, Except.bind, width,
    List.drop_eq_nil_of_le (by omega : bytes.length ≤ 8), List.take_of_length_le (by omega : bytes.length ≤ 8)]

def sessionAllocationLoop {σ : Type} (encounter : StateT σ (Except Stop) Bool)
    (s : Option Bool × Nat) : StateT σ (Except Stop) (Option Bool × Nat) :=
  Lean.Loop.forIn Lean.Loop.mk s fun _ state => do
    if state.2 < 1 then
      if !(← encounter) then return .done (some false, state.2)
      return .yield (none, state.2 + 1)
    else return .done (none, state.2)

theorem sessionAllocation_source : AmbientM.hiddenAlloc .kzallocKeypair = (do
    let w ← get
    let placeholders := w.hidden.isNone && w.hiddenPlaceholders
    if !placeholders && !w.allocArmed.contains "kzallocKeypair" then return true
    let encounter := if placeholders then
      (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocPlaceholder) .kzallocKeypair
      else (noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocRecord) .kzallocKeypair
    let out ← sessionAllocationLoop encounter (none, 0)
    match out.1 with
    | some result => pure result
    | none => pure true) := by
  simp only [AmbientM.hiddenAlloc, AllocSite.info, sessionAllocationLoop]
  apply bind_congr
  intro w
  split
  · rfl
  · apply bind_congr
    intro out
    cases out.1 <;> rfl

theorem sessionAllocationLoop_unfold {σ : Type} (encounter : StateT σ (Except Stop) Bool) (s : Option Bool × Nat) :
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

theorem sessionAllocation_returns {σ : Type} (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (success : bytes.headD 2 = 1) (P : σ → Prop) (s : σ) :
    Config.Product.Returns ((hiddenAlloc .kzallocKeypair : StateT σ AmbientM Bool).run s)
      (fun ambient => P s ∧ ambient.hidden = some ({site := 80, bytes := bytes} :: rest) ∧
        ambient.allocArmed.contains "kzallocKeypair" = true)
      (fun (ok, current) ambient => ok = true ∧ P current ∧ ambient.hidden = some rest) := by
  intro ambient pre
  have record : ((noise_const _private.Leanux.Kernel.Defs.«0».Leanux.AmbientM.allocRecord)
      .kzallocKeypair).run ambient = .ok (true, {ambient with hidden := some rest}) := by
    change ((do
      let bs ← AmbientM.hidden (.alloc .kzallocKeypair)
      match bs.headD 2 with
      | 1 => pure true
      | 0 => pure false
      | b => throw (Stop.hidden s!"kzallocKeypair: outcome byte {b}, expected 0 or 1")).run ambient) = _
    rw [StateT.run_bind, sessionAllocationRecord_run bytes rest width ambient pre.2.1]
    simp only [bind, Except.bind]
    rw [success]
    rfl
  have native : (AmbientM.hiddenAlloc .kzallocKeypair).run ambient =
      .ok (true, {ambient with hidden := some rest}) := by
    rw [sessionAllocation_source]
    simp only [StateT.run_bind, StateT.run_get, pre.2.1, Option.isNone_some,
      Bool.false_and, Bool.not_false, pre.2.2, Bool.not_true, Bool.true_and,
      Bool.false_eq_true, ite_false, pure_bind]
    rw [sessionAllocationLoop_unfold]
    simp only [Nat.zero_lt_one, ite_true, StateT.run_bind, record]
    rw [sessionAllocationLoop_unfold]
    rfl
  refine ⟨(true, s), {ambient with hidden := some rest}, ?_, rfl, pre.1, rfl⟩
  change ((AmbientM.hiddenAlloc .kzallocKeypair).run ambient).map
    (fun (value, after) => ((value, s), after)) = _
  rw [native]
  rfl

theorem sessionBirthdate_returns {σ : Type} (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 8) (P : σ → Prop) (s : σ) :
    Config.Product.Returns ((hiddenClock64 .deriveKeysBirthdate : StateT σ AmbientM Int64).run s)
      (fun ambient => P s ∧ ambient.hidden = some ({site := 13, bytes := bytes} :: rest))
      (fun (_, current) _ => P current) := by
  intro ambient pre
  let birth := (bytes.foldr (fun (b : UInt8) (acc : Nat) => acc * 256 + b.toNat) 0).toUInt64.toInt64
  refine ⟨(birth, s), {ambient with hidden := some rest}, ?_, pre.1⟩
  change (((AmbientM.hidden .deriveKeysBirthdate).run ambient >>= fun (bytes, a) =>
    Except.ok ((bytes.foldr (fun (b : UInt8) acc => acc * 256 + b.toNat) 0).toUInt64.toInt64, a))).map
      (fun (value, after) => ((value, s), after)) = _
  rw [sessionBirthdateRecord_run bytes rest width ambient pre.2]
  rfl

theorem sessionCreate_returns (peer : Option PeerId) (d : Device) (counter : Nat)
    (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 40) (success : bytes.headD 2 = 1) (g : WGWorld) :
    Config.Product.Returns ((keypairCreate peer).run g)
      (fun ambient => (g.dev = some d ∧ g.keypairCounter = counter) ∧
        ambient.hidden = some ({site := 80, bytes := bytes} :: rest) ∧
        ambient.allocArmed.contains "kzallocKeypair" = true)
      (fun (result, current) ambient => result = some d.nextKeypairId ∧
        current.dev = some (Index.createdDevice d counter peer) ∧
        current.keypairCounter = counter + 1 ∧ ambient.hidden = some rest) := by
  intro ambient pre
  obtain ⟨⟨ok, middle⟩, next, allocRun, allocated, ⟨device, count⟩, records⟩ :=
    sessionAllocation_returns bytes rest width success
      (fun g : WGWorld => g.dev = some d ∧ g.keypairCounter = counter) g ambient pre
  subst ok
  let final := {middle with dev := some (Index.createdDevice d counter peer), keypairCounter := counter + 1}
  let after := {next with steps := next.steps.push {
    decision := .keypairCreateNoMem, outcome := false, netRx := next.netRxSection}}
  refine ⟨(some d.nextKeypairId, final), after, ?_, rfl, rfl, rfl, records⟩
  simp only [keypairCreate, StateT.run_bind]
  rw [allocRun]
  simp [branch, AmbientM.branch, getDev, setKeypair, modifyDev,
    device, count, final, after, Index.createdDevice]
  rfl

theorem deriveKeys_returns (kp : KeypairId) (initiator : Bool) (ck : List UInt8)
    (d : Device) (k : Keypair) (resident : d.keypairs[kp]? = some k)
    (bytes : List UInt8) (rest : List HiddenRecord) (width : bytes.length = 8) (g : WGWorld) :
    Config.Product.Returns ((deriveKeys kp initiator ck).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some ({site := 13, bytes := bytes} :: rest))
      (fun (_, current) _ => ∃ birth, current.dev = some {d with keypairs := d.keypairs.insert kp (sessionDerivedKey k initiator ck birth)}) := by
  intro ambient pre
  obtain ⟨⟨birth, middle⟩, next, clockRun, device⟩ :=
    sessionBirthdate_returns bytes rest width (fun g : WGWorld => g.dev = some d) g ambient pre
  obtain ⟨outs, beforeWrite, writeAmbient, kdfRun, value, same⟩ :=
    (returns_iff _ _ _).mpr (sessionKdf_returns ck (fun g => g.dev = some d)) middle next device
  subst outs
  let final := {beforeWrite with dev := some {d with keypairs := d.keypairs.insert kp (sessionDerivedKey k initiator ck birth)}}
  refine ⟨((), final), writeAmbient, ?_, birth, rfl⟩
  simp only [deriveKeys, StateT.run_bind]
  rw [clockRun]
  simp only [bind, Except.bind]
  rw [kdfRun]
  cases initiator <;>
    simp [kdfOut, getKeypair, getDev, setKeypair, modifyDev, final, sessionDerivedKey]
  all_goals simp [StateT.run, StateT.pure, Pure.pure, Except.pure, bind, Except.bind, same, resident]
  all_goals rfl

theorem sessionPublish_returns (pid : PeerId) (kp : KeypairId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true) :
    Returns (sessionPublish pid kp) (fun w => w.dev = some d)
      (fun ok _ => ok = true) := by
  intro g ambient device
  cases hword : p.handshakeEntryPeer with
  | none => exact False.elim (word hword)
  | some owner =>
    let final := {g with dev := some {d with indexTable := Index.replaceOwner pid kp d.indexTable}}
    let after := {ambient with steps := ambient.steps.push {
      decision := .idxReplaceUnhashed, outcome := false, netRx := ambient.netRxSection}}
    refine ⟨true, final, after, ?_, rfl⟩
    have lifted : (monadLift (indexReplaceHandshake pid kp) : WG.M Bool) =
        liftIndex (indexReplaceHandshake pid kp) := rfl
    simp only [sessionPublish, lifted]
    simp [IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev, device, resident,
      hword, indexReplaceHandshake, indexHashed, liftIndex, branch, AmbientM.branch,
      modifyDev, hashed, final, after, Index.replaceOwner, -List.any_eq_false]
    rfl

theorem handshakeZero_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (handshakeZero pid) (fun w => w.dev = some d)
      (fun _ w => w.dev = some {d with peers := d.peers.insert pid (sessionZeroPeer p)}) := by
  intro g ambient device
  refine ⟨(), {g with dev := some {d with peers := d.peers.insert pid (sessionZeroPeer p)}},
    ambient, ?_, rfl⟩
  simp [handshakeZero, getPeer, getDev, device, resident, setPeer, modifyDev, sessionZeroPeer]
  rfl

/-- The original ordered rotation followed immediately by publication. -/
def sessionRotationPublish (pid : PeerId) (kp : KeypairId) : WG.M Bool := do
  addNewKeypair pid kp
  sessionPublish pid kp

theorem sessionRotationPublish_returns (pid : PeerId) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (resident : d.peers[pid]? = some p)
    (key : d.keypairs[kp]? = some k) (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : ClearReady d (rotationReleases (rotationPlan p k.iAmTheInitiator kp))) :
    Returns (sessionRotationPublish pid kp) (fun w => w.dev = some d)
      (fun ok _ => ok = true) := by
  apply returns_bind _ _ (addNewKeypair_returns_ready pid kp d p k resident key ready)
  intro u w ambient pre
  obtain ⟨out, device, steps⟩ := pre
  exact sessionPublish_returns pid kp out (rotationPeer (rotationPlan p k.iAmTheInitiator kp) p)
    (rotationRun_peer steps p resident) (by simpa only [rotationPeer_word] using word)
    (rotationRun_handshake_hashed steps pid hashed) w ambient device

/-- The original alive guard at the cut immediately after handshake zeroing. -/
def sessionAliveFinish (pid : PeerId) (kp : KeypairId) : WG.M Bool := do
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
    Returns (sessionFinish pid kp) (fun w => w.dev = some d) (fun ok _ => ok = true) := by
  let zeroed := {d with peers := d.peers.insert pid (sessionZeroPeer p)}
  rw [sessionFinish_ready_source]
  apply returns_bind _ _ (handshakeZero_returns pid d p resident)
  intro u g ambient device
  let marked := {ambient with steps := ambient.steps.push {
    decision := .sessionAlive, outcome := true, netRx := ambient.netRxSection}}
  obtain ⟨ok, final, after, run, yes⟩ :=
    sessionRotationPublish_returns pid kp zeroed (sessionZeroPeer p) k
      (by simp [zeroed]) key word hashed ready g marked device
  refine ⟨ok, final, after, ?_, yes⟩
  have source : ((sessionAliveFinish pid kp).run g).run ambient =
      ((sessionRotationPublish pid kp).run g).run marked := by
    simp [sessionAliveFinish, getPeer, getDev, device, branch, AmbientM.branch,
      sessionZeroPeer, alive, marked]
  exact source.trans run

theorem sessionPrepare_returns (pid : PeerId) (st : Nat) (kp : KeypairId) (d : Device)
    (p : Peer) (k : Keypair) (resident : d.peers[pid]? = some p)
    (key : d.keypairs[kp]? = some k) (bytes : List UInt8) (rest : List HiddenRecord)
    (width : bytes.length = 8) (g : WGWorld) :
    Config.Product.Returns ((sessionPrepare pid st kp).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some ({site := 13, bytes := bytes} :: rest))
      (fun (_, current) _ => ∃ birth, current.dev = some (sessionDerivedDevice d kp p k st birth)) := by
  intro ambient pre
  let assigned := {d with keypairs := d.keypairs.insert kp (sessionAssignedKey k p st)}
  let start := {g with dev := some assigned}
  let marked := {ambient with steps := ambient.steps.push {
    decision := .sessionInitiator, outcome := st == HANDSHAKE_CONSUMED_RESPONSE,
    netRx := ambient.netRxSection}}
  obtain ⟨⟨u, final⟩, after, run, birth, device⟩ :=
    deriveKeys_returns kp (st == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey assigned
      (sessionAssignedKey k p st) (by simp [assigned]) bytes rest width start marked ⟨rfl, pre.2⟩
  refine ⟨(u, final), after, ?_, birth, ?_⟩
  · have source : ((sessionPrepare pid st kp).run g).run ambient =
        ((deriveKeys kp (st == HANDSHAKE_CONSUMED_RESPONSE) p.chainingKey).run start).run marked := by
      cases mode : st == HANDSHAKE_CONSUMED_RESPONSE <;>
        simp [sessionPrepare, getPeer, getKeypair, getDev, pre.1, resident, key,
          setKeypair, modifyDev, branch, AmbientM.branch, mode, start, assigned, sessionAssignedKey, marked]
      all_goals rfl
    exact source.trans run
  · simpa [sessionDerivedDevice, assigned] using device

/-- Total original suffix after allocation, under an entry-state release
budget calculated after the allocator's actual overwrite. -/
theorem sessionAfterAllocation_returns_ready (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p) (alive : p.isDead = false)
    (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : SessionReady d p counter)
    (bytes : List UInt8) (rest : List HiddenRecord) (width : bytes.length = 8) (g : WGWorld) :
    Config.Product.Returns ((Index.sessionAfterAllocation pid p.handshakeState d.nextKeypairId).run g)
      (fun ambient => g.dev = some (Index.createdDevice d counter p.handshakeEntryPeer) ∧
        ambient.hidden = some ({site := 13, bytes := bytes} :: rest)) (fun (ok, _) _ => ok = true) := by
  intro ambient pre
  obtain ⟨⟨u, middle⟩, next, prepareRun, birth, device⟩ :=
    sessionPrepare_returns pid p.handshakeState d.nextKeypairId
      (Index.createdDevice d counter p.handshakeEntryPeer) p
      {internalId := counter + 1, peer := p.handshakeEntryPeer}
      resident (by simp [Index.createdDevice]) bytes rest width g ambient pre
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
  obtain ⟨ok, final, after, finishRun, yes⟩ :=
    sessionFinish_returns pid d.nextKeypairId derived p dk resident key alive word hashed budget
      middle next device
  refine ⟨(ok, final), after, ?_, yes⟩
  rw [sessionAfterAllocation_prepare]
  change (((sessionPrepare pid p.handshakeState d.nextKeypairId).run g).run ambient >>=
    fun ((_, w), a) => ((sessionFinish pid d.nextKeypairId).run w).run a) = _
  rw [prepareRun]
  exact finishRun

theorem sessionAfterCreate_returns_ready (pid : PeerId) (d : Device) (p : Peer)
    (counter : Nat) (resident : d.peers[pid]? = some p) (alive : p.isDead = false)
    (word : p.handshakeEntryPeer ≠ none)
    (hashed : d.indexTable.any (·.owner == .handshake pid) = true)
    (ready : SessionReady d p counter)
    (bytes : List UInt8) (rest : List HiddenRecord) (width : bytes.length = 8) (g : WGWorld) :
    Config.Product.Returns ((Index.sessionAfterCreate pid p.handshakeState (some d.nextKeypairId)).run g)
      (fun ambient => g.dev = some (Index.createdDevice d counter p.handshakeEntryPeer) ∧
        ambient.hidden = some ({site := 13, bytes := bytes} :: rest)) (fun (ok, _) _ => ok = true) := by
  intro ambient pre
  let marked := {ambient with steps := ambient.steps.push {
    decision := .sessionNoKeypair, outcome := false, netRx := ambient.netRxSection}}
  obtain ⟨out, after, run, yes⟩ :=
    sessionAfterAllocation_returns_ready pid d p counter resident alive word hashed ready
      bytes rest width g marked pre
  refine ⟨out, after, ?_, yes⟩
  have source : ((Index.sessionAfterCreate pid p.handshakeState (some d.nextKeypairId)).run g).run ambient =
      ((Index.sessionAfterAllocation pid p.handshakeState d.nextKeypairId).run g).run marked := by
    simp [Index.sessionAfterCreate, branch, AmbientM.branch, marked]
  exact source.trans run

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
    (clockWidth : clock.length = 8) (rest : List HiddenRecord) (g : WGWorld) :
    Config.Product.Returns ((beginSession pid).run g)
      (fun ambient => (g.dev = some d ∧ g.keypairCounter = counter) ∧
        ambient.hidden = some (sessionReadyRecords allocation clock rest) ∧
        ambient.allocArmed.contains "kzallocKeypair" = true)
      (fun (ok, _) _ => ok = true) := by
  intro ambient pre
  let first := {ambient with steps := ambient.steps.push {
    decision := .sessionNotCreatedResponse, outcome := p.handshakeState != HANDSHAKE_CREATED_RESPONSE,
    netRx := ambient.netRxSection}}
  let marked := if p.handshakeState != HANDSHAKE_CREATED_RESPONSE then
    {first with steps := first.steps.push {
      decision := .sessionNotConsumedResponse, outcome := p.handshakeState != HANDSHAKE_CONSUMED_RESPONSE,
      netRx := first.netRxSection}} else first
  have markHidden : marked.hidden = ambient.hidden := by unfold marked; split <;> rfl
  have markArmed : marked.allocArmed = ambient.allocArmed := by unfold marked; split <;> rfl
  have source : ((beginSession pid).run g).run ambient =
      (((do let key ← keypairCreate p.handshakeEntryPeer
            Index.sessionAfterCreate pid p.handshakeState key) : WG.M Bool).run g).run marked := by
    rcases accepted with created | consumed
    · rw [Index.beginSession_owner_source]
      simp [getPeer, getDev, pre.1.1, resident, WG.andM, branch, AmbientM.branch,
        IndexOwner.peerWord, created, marked, first]
    · rw [Index.beginSession_owner_source]
      simp [getPeer, getDev, pre.1.1, resident, WG.andM, branch, AmbientM.branch,
        IndexOwner.peerWord, consumed, marked, first, HANDSHAKE_CREATED_RESPONSE, HANDSHAKE_CONSUMED_RESPONSE]
  obtain ⟨⟨created, middle⟩, next, createRun, value, device, count, records⟩ :=
    sessionCreate_returns p.handshakeEntryPeer d counter allocation ({site := 13, bytes := clock} :: rest)
      allocWidth allocSuccess g marked ⟨pre.1, by simpa [markHidden, sessionReadyRecords, HiddenSite.info, AllocSite.info, AllocSite.hiddenId] using pre.2.1,
        by simpa [markArmed] using pre.2.2⟩
  subst created
  obtain ⟨out, after, finishRun, yes⟩ :=
    sessionAfterCreate_returns_ready pid d p counter resident alive word hashed ready
      clock rest clockWidth middle next ⟨device, records⟩
  refine ⟨out, after, ?_, yes⟩
  rw [source]
  change (((keypairCreate p.handshakeEntryPeer).run g).run marked >>=
    fun ((key, w), a) => ((Index.sessionAfterCreate pid p.handshakeState key).run w).run a) = _
  rw [createRun]
  exact finishRun

end Leanux.Proofs.WG.Noise
