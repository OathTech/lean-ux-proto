import Leanux.Proofs.WG.Noise.InitiationReadyContinuationSource
import Leanux.Proofs.WG.Noise.InitiationReadyClockSource
import Leanux.Proofs.WG.Noise.InitiationReadyFinishSource
import Leanux.Proofs.WG.Noise.InitiationReadyCryptoFrames
import Leanux.Proofs.WG.Noise.InitiationReadyInputSource
import Leanux.Proofs.WG.Noise.InitiationReadyModel
import Leanux.Proofs.WG.Noise.SessionReadySource
import Leanux.Proofs.WG.Index.DrawRecords
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
/-! Total contracts for original initiation stages. The final factorization checks
that these cuts compose to the unmodified original call. World-dependent
intermediate posts stay in this source file; public claims use the projection. -/
namespace Leanux.Proofs.WG.Noise.InitiationReady
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do
def afterRandom (pid : PeerId) (staticPublic precomputed remote hash : List UInt8) :
    M (Option (List UInt8)) := do
  let secret := clamp (← hidden .initEphemeral)
  setSecret pid secret
  afterPublic pid staticPublic precomputed secret remote hash

def randomEffect (pid : PeerId) (d : Device) (p : Peer)
    (staticPublic precomputed remote hash ephemeral clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) : Option (List UInt8) → World → Prop :=
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
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Returns (afterRandom pid staticPublic precomputed remote hash)
      (fun w => w.k.wg = some d ∧ w.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (randomEffect pid d p staticPublic precomputed remote hash ephemeral clock fresh.value rest) := by
  unfold afterRandom
  apply returns_bind _ _ (hidden_returns false ephemeral _ randomWidth d)
  intro bytes w pre
  obtain ⟨same, device, records⟩ := pre
  subst bytes
  apply returns_bind _ _ (setSecret_returns pid (clamp ephemeral) d p resident _) _ w ⟨device, records⟩
  intro u
  exact afterPublic_returns pid staticPublic precomputed (clamp ephemeral) remote hash
    (secretDevice pid d p (clamp ephemeral)) {p with ephemeralPrivate := clamp ephemeral}
    (by simp [secretDevice]) word nonnull secretNonNull pubOk dhOk clock width collisions fresh rest allCollide isFresh

def body (pid : PeerId) (staticPublic : List UInt8) (p : Peer) : M (Option (List UInt8)) := do
  let h := noiseHash (handshakeInitHash ++ p.remoteStatic)
  setChain pid handshakeInitChainingKey h
  afterRandom pid staticPublic p.precomputedStaticStatic p.remoteStatic h

def bodyEffect (pid : PeerId) (d : Device) (p : Peer) (ephemeral clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) : Option (List UInt8) → World → Prop :=
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
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Returns (body pid d.staticIdentity.staticPublic p)
      (fun w => w.k.wg = some d ∧ w.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (bodyEffect pid d p ephemeral clock fresh.value rest) := by
  unfold body
  apply returns_bind _ _ (chain_returns pid d p resident handshakeInitChainingKey
    (noiseHash (handshakeInitHash ++ p.remoteStatic)) _)
  intro u
  exact afterRandom_returns pid d.staticIdentity.staticPublic p.precomputedStaticStatic p.remoteStatic
    (noiseHash (handshakeInitHash ++ p.remoteStatic))
    (chainDevice pid d p handshakeInitChainingKey (noiseHash (handshakeInitHash ++ p.remoteStatic)))
    {p with chainingKey := handshakeInitChainingKey, hash := noiseHash (handshakeInitHash ++ p.remoteStatic)}
    (by simp [chainDevice]) word nonnull ephemeral clock randomWidth width secretNonNull pubOk dhOk
    collisions fresh rest allCollide isFresh

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
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Returns (createInitiation pid)
      (fun w => w.k.wg = some d ∧ w.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (bodyEffect pid d p ephemeral clock fresh.value rest) := by
  have hp := (returns_iff _ _ _).mp (sessionReadyPeer_read pid d p resident
    (fun w => w.hidden = some ({site := 1, bytes := ephemeral} ::
      {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest)))
  have hb := (returns_iff _ _ _).mp (body_returns pid d p resident word nonnull
    ephemeral clock randomWidth width secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh)
  rw [createInitiation_factored, returns_iff]
  mvcgen [getDev, getK, branch, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all only [Option.some.injEq]
  all_goals subst_vars
  all_goals try simp_all
  all_goals intro s same device records
  all_goals exact hb s ⟨device, records⟩

theorem bodyEffect_result (pid : PeerId) (d : Device) (p : Peer) (ephemeral clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) (out : Option (List UInt8)) (w : World) :
    bodyEffect pid d p ephemeral clock index rest out w ↔
      out = some (result pid d p ephemeral clock index).1 ∧
      w.k.wg = some (result pid d p ephemeral clock index).2 ∧ w.hidden = some rest := by rfl

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
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Returns (createInitiation pid)
      (fun w => w.k.wg = some d ∧ w.hidden = some ({site := 1, bytes := ephemeral} ::
        {site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun out w => out = some (result pid d p ephemeral clock fresh.value).1 ∧
        w.k.wg = some (result pid d p ephemeral clock fresh.value).2 ∧ w.hidden = some rest) :=
  createInitiation_ready pid d p resident identity word nonnull ephemeral clock randomWidth width
    secretNonNull pubOk dhOk collisions fresh rest allCollide isFresh
end Leanux.Proofs.WG.Noise.InitiationReady
