import Leanux.Proofs.WG.Noise.InitiationReadyContinuationSource
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
/-! Total contracts for original initiation stages. The final factorization checks
that these cuts compose to the unmodified original call. Native Device and Ambient
intermediate posts stay in this source file; public claims use the projection. -/
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do
def afterRandom (pid : PeerId) (staticPublic precomputed remote hash : List UInt8) :
    WG.M (Option (List UInt8)) := do
  let secret := clamp (← hidden .initEphemeral)
  setSecret pid secret
  afterPublic pid staticPublic precomputed secret remote hash

def randomEffect (pid : PeerId) (d : Device) (p : Peer)
    (staticPublic precomputed remote hash ephemeral clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) : Option (List UInt8) → WGWorld → Ambient → Prop :=
  ephemeralEffect pid (secretDevice pid d p (clamp ephemeral)) {p with ephemeralPrivate := clamp ephemeral}
    staticPublic precomputed (curve25519 (clamp ephemeral) basePoint).1
    (clamp ephemeral) remote hash clock index rest

theorem afterRandom_returns (pid : PeerId)
    (staticPublic precomputed remote hash : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : precomputed ≠ List.replicate 32 0)
    (ephemeral clock : List UInt8) (randomWidth : ephemeral.length = 32) (width : clock.length = 16)
    (secretNonNull : clamp ephemeral ≠ nullPoint)
    (pubOk : (curve25519 (clamp ephemeral) basePoint).2 = true)
    (dhOk : (curve25519 (clamp ephemeral) remote).2 = true)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) (g : WGWorld) :
    Config.Product.Returns ((afterRandom pid staticPublic precomputed remote hash).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun (out, current) ambient => randomEffect pid d p staticPublic precomputed remote hash ephemeral clock fresh.value rest out current ambient) := by
  intro ambient pre
  obtain ⟨⟨bytes, afterRead⟩, readAmbient, readRun, value, device, records⟩ :=
    hidden_returns false ephemeral _ randomWidth d g ambient pre
  subst bytes
  change ((hidden .initEphemeral : WG.M (List UInt8)).run g).run ambient =
    .ok ((ephemeral, afterRead), readAmbient) at readRun
  obtain ⟨⟨u, changed⟩, changedAmbient, writeRun, changedDevice, tail⟩ :=
    setSecret_returns pid (clamp ephemeral) d p resident _ afterRead readAmbient ⟨device, records⟩
  obtain ⟨⟨out, final⟩, after, tailRun, post⟩ :=
    afterPublic_returns pid staticPublic precomputed (clamp ephemeral) remote hash
      (secretDevice pid d p (clamp ephemeral)) {p with ephemeralPrivate := clamp ephemeral}
      (by simp [secretDevice]) word nonnull secretNonNull pubOk dhOk clock width
      collisions fresh rest allCollide isFresh changed changedAmbient ⟨changedDevice, tail⟩
  refine ⟨(out, final), after, ?_, post⟩
  change (((hidden .initEphemeral : WG.M (List UInt8)).run g).run ambient >>= _) = _
  rw [readRun]
  change (((setSecret pid (clamp ephemeral)).run afterRead).run readAmbient >>= fun ((_, current), a) =>
    ((afterPublic pid staticPublic precomputed (clamp ephemeral) remote hash).run current).run a) = _
  rw [writeRun]
  exact tailRun


def body (pid : PeerId) (staticPublic : List UInt8) (p : Peer) : WG.M (Option (List UInt8)) := do
  let h := noiseHash (handshakeInitHash ++ p.remoteStatic)
  setChain pid handshakeInitChainingKey h
  afterRandom pid staticPublic p.precomputedStaticStatic p.remoteStatic h

def bodyEffect (pid : PeerId) (d : Device) (p : Peer) (ephemeral clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) : Option (List UInt8) → WGWorld → Ambient → Prop :=
  let h := noiseHash (handshakeInitHash ++ p.remoteStatic)
  randomEffect pid (chainDevice pid d p handshakeInitChainingKey h)
    {p with chainingKey := handshakeInitChainingKey, hash := h}
    d.staticIdentity.staticPublic p.precomputedStaticStatic p.remoteStatic h ephemeral clock index rest

theorem body_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (word : p.handshakeEntryPeer ≠ none)
    (nonnull : p.precomputedStaticStatic ≠ List.replicate 32 0)
    (ephemeral clock : List UInt8) (randomWidth : ephemeral.length = 32) (width : clock.length = 16)
    (secretNonNull : clamp ephemeral ≠ nullPoint)
    (pubOk : (curve25519 (clamp ephemeral) basePoint).2 = true)
    (dhOk : (curve25519 (clamp ephemeral) p.remoteStatic).2 = true)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) (g : WGWorld) :
    Config.Product.Returns ((body pid d.staticIdentity.staticPublic p).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun (out, current) ambient => bodyEffect pid d p ephemeral clock fresh.value rest out current ambient) := by
  intro ambient pre
  let h := noiseHash (handshakeInitHash ++ p.remoteStatic)
  obtain ⟨⟨u, changed⟩, changedAmbient, writeRun, device, records⟩ :=
    chain_returns pid d p resident handshakeInitChainingKey h _ g ambient pre
  obtain ⟨⟨out, final⟩, after, tailRun, post⟩ :=
    afterRandom_returns pid d.staticIdentity.staticPublic p.precomputedStaticStatic p.remoteStatic h
      (chainDevice pid d p handshakeInitChainingKey h)
      {p with chainingKey := handshakeInitChainingKey, hash := h}
      (by simp [chainDevice]) word nonnull ephemeral clock randomWidth width
      secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh
      changed changedAmbient ⟨device, records⟩
  refine ⟨(out, final), after, ?_, post⟩
  change (((setChain pid handshakeInitChainingKey h).run g).run ambient >>= fun ((_, current), a) =>
    ((afterRandom pid d.staticIdentity.staticPublic p.precomputedStaticStatic p.remoteStatic h).run current).run a) = _
  rw [writeRun]
  exact tailRun


theorem createInitiation_factored (pid : PeerId) :
    createInitiation pid = (do
      let identity := (← getDev).staticIdentity
      if ← branch .initNoIdentity !identity.hasIdentity then return none
      let p ← getPeer pid
      body pid identity.staticPublic p) := by
  simp only [createInitiation, body, afterRandom, setSecret, afterPublic,
    afterEphemeral, afterDh, afterPrecomputed, afterClock, finish, bind_assoc]
  rfl

theorem createInitiation_ready (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (identity : d.staticIdentity.hasIdentity = true)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : p.precomputedStaticStatic ≠ List.replicate 32 0)
    (ephemeral clock : List UInt8) (randomWidth : ephemeral.length = 32) (width : clock.length = 16)
    (secretNonNull : clamp ephemeral ≠ nullPoint)
    (pubOk : (curve25519 (clamp ephemeral) basePoint).2 = true)
    (dhOk : (curve25519 (clamp ephemeral) p.remoteStatic).2 = true)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) (g : WGWorld) :
    Config.Product.Returns ((createInitiation pid).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun (out, current) ambient => bodyEffect pid d p ephemeral clock fresh.value rest out current ambient) := by
  intro ambient pre
  let next := {ambient with steps := ambient.steps.push {
    decision := Decision.initNoIdentity, outcome := false, netRx := ambient.netRxSection}}
  obtain ⟨⟨out, final⟩, after, bodyRun, post⟩ :=
    body_returns pid d p resident word nonnull ephemeral clock randomWidth width
      secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh g next pre
  refine ⟨(out, final), after, ?_, post⟩
  rw [createInitiation_factored]
  simp [getDev, getPeer, pre.1, identity, resident, branch, AmbientM.branch]
  exact bodyRun


theorem bodyEffect_result (pid : PeerId) (d : Device) (p : Peer) (ephemeral clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) (out : Option (List UInt8)) (w : WGWorld) (ambient : Ambient) :
    bodyEffect pid d p ephemeral clock index rest out w ambient ↔
      out = some (result pid d p ephemeral clock index).1 ∧
      w.dev = some (result pid d p ephemeral clock index).2 ∧ ambient.hidden = some rest := by rfl

theorem createInitiation_total (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (identity : d.staticIdentity.hasIdentity = true)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : p.precomputedStaticStatic ≠ List.replicate 32 0)
    (ephemeral clock : List UInt8) (randomWidth : ephemeral.length = 32) (width : clock.length = 16)
    (secretNonNull : clamp ephemeral ≠ nullPoint)
    (pubOk : (curve25519 (clamp ephemeral) basePoint).2 = true)
    (dhOk : (curve25519 (clamp ephemeral) p.remoteStatic).2 = true)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) (g : WGWorld) :
    Config.Product.Returns ((createInitiation pid).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun (out, current) ambient => out = some (result pid d p ephemeral clock fresh.value).1 ∧
        current.dev = some (result pid d p ephemeral clock fresh.value).2 ∧ ambient.hidden = some rest) :=
  createInitiation_ready pid d p resident identity word nonnull ephemeral clock randomWidth width
    secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh g
end Leanux.Proofs.WG.Noise.InitiationReady
