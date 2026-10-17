import Leanux.Proofs.WG.Noise.InitiationReadyClockSource
import Leanux.Proofs.WG.Noise.InitiationReadyCryptoModel
/-! Total initiation continuations with exact native Device and record effects. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG Leanux.Proofs.WG.Noise
def clockEffect (pid : PeerId) (d : Device) (p : Peer) (e encStatic ck key hash clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) (out : Option (List UInt8)) (w : WGWorld) (ambient : Ambient) : Prop :=
  let encTime := aeadEncrypt key noiseNonce (tai64n clock) hash
  let changed := chainDevice pid d p ck (noiseHash (hash ++ encTime))
  out = some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0) ∧
    w.dev = some {changed with
      peers := changed.peers.insert pid {{p with chainingKey := ck, hash := noiseHash (hash ++ encTime)}
        with handshakeState := HANDSHAKE_CREATED_INITIATION}
      indexTable := {index, owner := .handshake pid} :: Index.removeOwner (.handshake pid) d.indexTable} ∧
    ambient.hidden = some rest

def afterPrecomputed (pid : PeerId) (e encStatic ck precomputed hash : List UInt8) : WG.M (Option (List UInt8)) := do
  let ss ← mixPrecomputedDh ck precomputed
  if ← branch .initSsFailed ss.isNone then return none
  let some (ck, key) := ss | invariant "unreachable"
  afterClock pid e encStatic ck key hash

theorem afterPrecomputed_returns (pid : PeerId) (e encStatic ck precomputed hash : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : precomputed ≠ List.replicate 32 0)
    (clock : List UInt8) (width : clock.length = 16)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) (g : WGWorld) :
    Config.Product.Returns ((afterPrecomputed pid e encStatic ck precomputed hash).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun (out, current) ambient => clockEffect pid d p e encStatic (first ck precomputed) (second ck precomputed) hash clock fresh.value rest out current ambient) := by
  intro ambient pre
  have nonzero : (precomputed == (noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.zeroKey)) = false := by
    change (precomputed == List.replicate 32 0) = false
    exact beq_eq_false_iff_ne.mpr nonnull
  have native : ∃ middle,
      ((mixPrecomputedDh ck precomputed).run g).run ambient =
        .ok ((some (first ck precomputed, second ck precomputed), g), middle) ∧
      middle.hidden = ambient.hidden := by
    simp [mixPrecomputedDh, nonzero, kdf, kdf_pair, kdfOut]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨middle, nativeRun, hidden⟩ := native
  let next := {middle with steps := middle.steps.push {
    decision := Decision.initSsFailed, outcome := false, netRx := middle.netRxSection}}
  obtain ⟨⟨out, final⟩, after, tailRun, post⟩ :=
    afterClock_returns pid e encStatic (first ck precomputed) (second ck precomputed) hash
      d p resident word clock width collisions fresh rest allCollide isFresh g next
      ⟨pre.1, hidden.trans pre.2⟩
  refine ⟨(out, final), after, ?_, post⟩
  change (((mixPrecomputedDh ck precomputed).run g).run ambient >>= _) = _
  rw [nativeRun]
  change ((afterClock pid e encStatic (first ck precomputed) (second ck precomputed) hash).run g).run next = _
  exact tailRun


def afterDh (pid : PeerId) (staticPublic precomputed e ck secret remote hash : List UInt8) :
    WG.M (Option (List UInt8)) := do
  let es ← mixDh true ck secret remote
  if ← branch .initEsFailed es.isNone then return none
  let some (ck, key) := es | invariant "unreachable"
  let encStatic := aeadEncrypt key noiseNonce staticPublic hash
  let h := noiseHash (hash ++ encStatic)
  setChain pid ck h
  afterPrecomputed pid e encStatic ck precomputed h

def dhEffect (pid : PeerId) (d : Device) (p : Peer)
    (staticPublic precomputed e ck secret remote hash clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) : Option (List UInt8) → WGWorld → Ambient → Prop :=
  let ck2 := first ck (curve25519 secret remote).1
  let encStatic := aeadEncrypt (second ck (curve25519 secret remote).1) noiseNonce staticPublic hash
  let h2 := noiseHash (hash ++ encStatic)
  clockEffect pid (chainDevice pid d p ck2 h2) {p with chainingKey := ck2, hash := h2}
    e encStatic (first ck2 precomputed) (second ck2 precomputed) h2 clock index rest

theorem afterDh_returns (pid : PeerId)
    (staticPublic precomputed e ck secret remote hash : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : precomputed ≠ List.replicate 32 0)
    (dhOk : (curve25519 secret remote).2 = true)
    (clock : List UInt8) (width : clock.length = 16)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) (g : WGWorld) :
    Config.Product.Returns ((afterDh pid staticPublic precomputed e ck secret remote hash).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun (out, current) ambient => dhEffect pid d p staticPublic precomputed e ck secret remote hash clock fresh.value rest out current ambient) := by
  intro ambient pre
  let ck2 := first ck (curve25519 secret remote).1
  let encStatic := aeadEncrypt (second ck (curve25519 secret remote).1) noiseNonce staticPublic hash
  let h2 := noiseHash (hash ++ encStatic)
  have native : ∃ middle,
      ((mixDh true ck secret remote).run g).run ambient =
        .ok ((some (ck2, second ck (curve25519 secret remote).1), g), middle) ∧
      middle.hidden = ambient.hidden := by
    simp [mixDh, dhOk, kdf, kdf_pair, kdfOut, ck2]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨middle, nativeRun, hidden⟩ := native
  let next := {middle with steps := middle.steps.push {
    decision := Decision.initEsFailed, outcome := false, netRx := middle.netRxSection}}
  obtain ⟨⟨u, changed⟩, changedAmbient, chainRun, device, records⟩ :=
    chain_returns pid d p resident ck2 h2 _ g next ⟨pre.1, hidden.trans pre.2⟩
  obtain ⟨⟨out, final⟩, after, tailRun, post⟩ :=
    afterPrecomputed_returns pid e encStatic ck2 precomputed h2
      (chainDevice pid d p ck2 h2) {p with chainingKey := ck2, hash := h2}
      (by simp [chainDevice]) word nonnull clock width collisions fresh rest allCollide isFresh
      changed changedAmbient ⟨device, records⟩
  refine ⟨(out, final), after, ?_, post⟩
  change (((mixDh true ck secret remote).run g).run ambient >>= _) = _
  rw [nativeRun]
  change (((setChain pid ck2 h2).run g).run next >>= fun ((_, current), a) =>
    ((afterPrecomputed pid e encStatic ck2 precomputed h2).run current).run a) = _
  rw [chainRun]
  exact tailRun


def afterEphemeral (pid : PeerId) (staticPublic precomputed e secret remote hash : List UInt8) :
    WG.M (Option (List UInt8)) := do
  let (ck, h) ← messageEphemeral false e handshakeInitChainingKey hash
  setChain pid ck h
  afterDh pid staticPublic precomputed e ck secret remote h

def ephemeralEffect (pid : PeerId) (d : Device) (p : Peer)
    (staticPublic precomputed e secret remote hash clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) : Option (List UInt8) → WGWorld → Ambient → Prop :=
  let ck1 := first handshakeInitChainingKey e
  let h1 := noiseHash (hash ++ e)
  dhEffect pid (chainDevice pid d p ck1 h1) {p with chainingKey := ck1, hash := h1}
    staticPublic precomputed e ck1 secret remote h1 clock index rest

theorem afterEphemeral_returns (pid : PeerId)
    (staticPublic precomputed e secret remote hash : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : precomputed ≠ List.replicate 32 0)
    (dhOk : (curve25519 secret remote).2 = true)
    (clock : List UInt8) (width : clock.length = 16)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) (g : WGWorld) :
    Config.Product.Returns ((afterEphemeral pid staticPublic precomputed e secret remote hash).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun (out, current) ambient => ephemeralEffect pid d p staticPublic precomputed e secret remote hash clock fresh.value rest out current ambient) := by
  intro ambient pre
  let ck1 := first handshakeInitChainingKey e
  let h1 := noiseHash (hash ++ e)
  have native : ∃ middle,
      ((messageEphemeral false e handshakeInitChainingKey hash).run g).run ambient =
        .ok (((ck1, h1), g), middle) ∧ middle.hidden = ambient.hidden := by
    simp [messageEphemeral, kdf, kdf_single, kdfOut, ck1, h1]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨middle, nativeRun, hidden⟩ := native
  obtain ⟨⟨u, changed⟩, changedAmbient, chainRun, device, records⟩ :=
    chain_returns pid d p resident ck1 h1 _ g middle ⟨pre.1, hidden.trans pre.2⟩
  obtain ⟨⟨out, final⟩, after, tailRun, post⟩ :=
    afterDh_returns pid staticPublic precomputed e ck1 secret remote h1
      (chainDevice pid d p ck1 h1) {p with chainingKey := ck1, hash := h1}
      (by simp [chainDevice]) word nonnull dhOk clock width collisions fresh rest allCollide isFresh
      changed changedAmbient ⟨device, records⟩
  refine ⟨(out, final), after, ?_, post⟩
  change (((messageEphemeral false e handshakeInitChainingKey hash).run g).run ambient >>= _) = _
  rw [nativeRun]
  change (((setChain pid ck1 h1).run g).run middle >>= fun ((_, current), a) =>
    ((afterDh pid staticPublic precomputed e ck1 secret remote h1).run current).run a) = _
  rw [chainRun]
  exact tailRun


def afterPublic (pid : PeerId) (staticPublic precomputed secret remote hash : List UInt8) :
    WG.M (Option (List UInt8)) := do
  let (pub, ok) ← generatePublic secret
  if ← branch .initNoEphemeral !ok then return none
  let some e := pub | invariant "unreachable"
  afterEphemeral pid staticPublic precomputed e secret remote hash

theorem afterPublic_returns (pid : PeerId)
    (staticPublic precomputed secret remote hash : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer ≠ none) (nonnull : precomputed ≠ List.replicate 32 0)
    (secretNonNull : secret ≠ nullPoint) (pubOk : (curve25519 secret basePoint).2 = true)
    (dhOk : (curve25519 secret remote).2 = true)
    (clock : List UInt8) (width : clock.length = 16)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) (g : WGWorld) :
    Config.Product.Returns ((afterPublic pid staticPublic precomputed secret remote hash).run g)
      (fun ambient => g.dev = some d ∧ ambient.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun (out, current) ambient => ephemeralEffect pid d p staticPublic precomputed (curve25519 secret basePoint).1
        secret remote hash clock fresh.value rest out current ambient) := by
  intro ambient pre
  have nonzero : (secret == nullPoint) = false := beq_eq_false_iff_ne.mpr secretNonNull
  have native : ∃ middle,
      ((generatePublic secret).run g).run ambient =
        .ok (((some (curve25519 secret basePoint).1, true), g), middle) ∧
      middle.hidden = ambient.hidden := by
    simp only [generatePublic, nonzero, pubOk]
    exact ⟨_, rfl, rfl⟩
  obtain ⟨middle, nativeRun, hidden⟩ := native
  let next := {middle with steps := middle.steps.push {
    decision := Decision.initNoEphemeral, outcome := false, netRx := middle.netRxSection}}
  obtain ⟨⟨out, final⟩, after, tailRun, post⟩ :=
    afterEphemeral_returns pid staticPublic precomputed (curve25519 secret basePoint).1 secret remote hash
      d p resident word nonnull dhOk clock width collisions fresh rest allCollide isFresh g next
      ⟨pre.1, hidden.trans pre.2⟩
  refine ⟨(out, final), after, ?_, post⟩
  change (((generatePublic secret).run g).run ambient >>= _) = _
  rw [nativeRun]
  change ((afterEphemeral pid staticPublic precomputed (curve25519 secret basePoint).1 secret remote hash).run g).run next = _
  exact tailRun


end Leanux.Proofs.WG.Noise.InitiationReady
