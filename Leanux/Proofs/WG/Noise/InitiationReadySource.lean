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
def finish (pid : PeerId) (e encStatic encTime : List UInt8) : M (Option (List UInt8)) := do
  _ ← IndexOwner.peerDeref (.handshake pid)
  let index ← indexInsert (.handshake pid)
  setPeer pid {(← getPeer pid) with handshakeState := HANDSHAKE_CREATED_INITIATION}
  return some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0)


theorem deref_returns (pid : PeerId) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (stored : PeerId) (word : p.handshakeEntryPeer = some stored) (records : Option (List HiddenRecord)) :
    Returns (IndexOwner.peerDeref (.handshake pid))
      (fun w => w.k.wg = some d ∧ w.hidden = records)
      (fun out w => out = stored ∧ w.k.wg = some d ∧ w.hidden = records) := by
  rw [returns_iff]
  mvcgen [IndexOwner.peerDeref, IndexOwner.peerWord, getPeer, getDev, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals grind

def finishTag (pid : PeerId) (index : Nat) (e encStatic encTime : List UInt8) : M (Option (List UInt8)) := do
  setPeer pid {(← getPeer pid) with handshakeState := HANDSHAKE_CREATED_INITIATION}
  return some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0)
theorem finishTag_returns (pid : PeerId) (index : Nat) (e encStatic encTime : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) (records : Option (List HiddenRecord)) :
    Returns (finishTag pid index e encStatic encTime)
      (fun w => w.k.wg = some d ∧ w.hidden = records)
      (fun out w => out = some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0) ∧
        w.k.wg = some {d with peers := d.peers.insert pid {p with handshakeState := HANDSHAKE_CREATED_INITIATION}} ∧
        w.hidden = records) := by
  rw [returns_iff]
  mvcgen [finishTag, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem finish_returns (pid : PeerId) (e encStatic encTime : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer ≠ none)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Returns (finish pid e encStatic encTime)
      (fun w => w.k.wg = some d ∧ w.hidden = some (Index.drawStream collisions fresh rest))
      (fun out w => out = some (le32 1 ++ le32 fresh.value ++ e ++ encStatic ++ encTime ++ List.replicate 32 0) ∧
        w.k.wg = some {d with
          peers := d.peers.insert pid {p with handshakeState := HANDSHAKE_CREATED_INITIATION}
          indexTable := {index := fresh.value, owner := .handshake pid} ::
            Index.removeOwner (.handshake pid) d.indexTable} ∧ w.hidden = some rest) := by
  have someWord : ∃ stored, p.handshakeEntryPeer = some stored := by
    cases h : p.handshakeEntryPeer <;> simp_all
  obtain ⟨stored, hword⟩ := someWord
  change Returns (IndexOwner.peerDeref (.handshake pid) >>= fun _ =>
    indexInsert (.handshake pid) >>= fun index => finishTag pid index e encStatic encTime) _ _
  apply returns_bind _ _ (deref_returns pid d p resident stored hword _)
  intro storedResult w pre
  apply returns_bind _ _ (Index.indexInsert_records (.handshake pid) d collisions fresh rest allCollide isFresh) _ w pre.2
  intro index v h
  obtain ⟨rfl, device, records⟩ := h
  exact finishTag_returns pid fresh.value e encStatic encTime
    {d with indexTable := {index := fresh.value, owner := .handshake pid} ::
      Index.removeOwner (.handshake pid) d.indexTable} p resident _ v ⟨device, records⟩

abbrev setChain := noise_const _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
theorem chain_returns (pid : PeerId) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (ck hash : List UInt8) (records : Option (List HiddenRecord)) :
    Returns (setChain pid ck hash) (fun w => w.k.wg = some d ∧ w.hidden = records)
      (fun _ w => w.k.wg = some (chainDevice pid d p ck hash) ∧ w.hidden = records) := by
  rw [returns_iff]
  noise_vcgen [setChain, _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain,
    getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [chainDevice]

def afterClock (pid : PeerId) (e encStatic ck key hash : List UInt8) : M (Option (List UInt8)) := do
  let timestamp := tai64n (← hidden .tai64nNow)
  let encTime := aeadEncrypt key noiseNonce timestamp hash
  let h := noiseHash (hash ++ encTime)
  setChain pid ck h
  finish pid e encStatic encTime

theorem afterClock_returns (pid : PeerId) (e encStatic ck key hash : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (word : p.handshakeEntryPeer ≠ none)
    (clock : List UInt8) (width : clock.length = 16)
    (collisions : List Index.Draw) (fresh : Index.Draw) (rest : List HiddenRecord)
    (allCollide : ∀ draw ∈ collisions,
      (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == draw.value) = true)
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    let encTime := aeadEncrypt key noiseNonce (tai64n clock) hash
    let changed := chainDevice pid d p ck (noiseHash (hash ++ encTime))
    Returns (afterClock pid e encStatic ck key hash)
      (fun w => w.k.wg = some d ∧ w.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (fun out w => out = some (le32 1 ++ le32 fresh.value ++ e ++ encStatic ++ encTime ++ List.replicate 32 0) ∧
        w.k.wg = some {changed with
          peers := changed.peers.insert pid {{p with chainingKey := ck, hash := noiseHash (hash ++ encTime)}
            with handshakeState := HANDSHAKE_CREATED_INITIATION}
          indexTable := {index := fresh.value, owner := .handshake pid} ::
            Index.removeOwner (.handshake pid) d.indexTable} ∧ w.hidden = some rest) := by
  dsimp only
  change Returns (hidden .tai64nNow >>= fun clock => do
    let encTime := aeadEncrypt key noiseNonce (tai64n clock) hash
    setChain pid ck (noiseHash (hash ++ encTime))
    finish pid e encStatic encTime) _ _
  apply returns_bind _ _ (hidden_returns true clock _ width d)
  intro now w pre
  obtain ⟨same, device, records⟩ := pre
  subst now
  apply returns_bind _ _ (chain_returns pid d p resident ck
    (noiseHash (hash ++ aeadEncrypt key noiseNonce (tai64n clock) hash)) _) _ w ⟨device, records⟩
  intro u
  exact finish_returns pid e encStatic (aeadEncrypt key noiseNonce (tai64n clock) hash)
    (chainDevice pid d p ck (noiseHash (hash ++ aeadEncrypt key noiseNonce (tai64n clock) hash)))
    {p with chainingKey := ck, hash := noiseHash (hash ++ aeadEncrypt key noiseNonce (tai64n clock) hash)}
    (by simp [chainDevice]) word collisions fresh rest allCollide isFresh

def clockEffect (pid : PeerId) (d : Device) (p : Peer) (e encStatic ck key hash clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) (out : Option (List UInt8)) (w : World) : Prop :=
  let encTime := aeadEncrypt key noiseNonce (tai64n clock) hash
  let changed := chainDevice pid d p ck (noiseHash (hash ++ encTime))
  out = some (le32 1 ++ le32 index ++ e ++ encStatic ++ encTime ++ List.replicate 32 0) ∧
    w.k.wg = some {changed with
      peers := changed.peers.insert pid {{p with chainingKey := ck, hash := noiseHash (hash ++ encTime)}
        with handshakeState := HANDSHAKE_CREATED_INITIATION}
      indexTable := {index, owner := .handshake pid} :: Index.removeOwner (.handshake pid) d.indexTable} ∧
    w.hidden = some rest

def afterPrecomputed (pid : PeerId) (e encStatic ck precomputed hash : List UInt8) : M (Option (List UInt8)) := do
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
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Returns (afterPrecomputed pid e encStatic ck precomputed hash)
      (fun w => w.k.wg = some d ∧ w.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (clockEffect pid d p e encStatic (first ck precomputed) (second ck precomputed) hash clock fresh.value rest) := by
  have hs := precomputed_returns ck precomputed nonnull
    (fun k records => k.wg = some d ∧ records = some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
  have ht := (returns_iff _ _ _).mp (afterClock_returns pid e encStatic
    (first ck precomputed) (second ck precomputed) hash d p resident word clock width collisions fresh rest allCollide isFresh)
  rw [returns_iff]
  mvcgen [afterPrecomputed, branch, invariant, hs]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all only [Option.some.injEq]
  all_goals subst_vars
  all_goals try simp_all [clockEffect]
  all_goals mvcgen [ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [clockEffect]

def afterDh (pid : PeerId) (staticPublic precomputed e ck secret remote hash : List UInt8) :
    M (Option (List UInt8)) := do
  let es ← mixDh true ck secret remote
  if ← branch .initEsFailed es.isNone then return none
  let some (ck, key) := es | invariant "unreachable"
  let encStatic := aeadEncrypt key noiseNonce staticPublic hash
  let h := noiseHash (hash ++ encStatic)
  setChain pid ck h
  afterPrecomputed pid e encStatic ck precomputed h

def dhEffect (pid : PeerId) (d : Device) (p : Peer)
    (staticPublic precomputed e ck secret remote hash clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) : Option (List UInt8) → World → Prop :=
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
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Returns (afterDh pid staticPublic precomputed e ck secret remote hash)
      (fun w => w.k.wg = some d ∧ w.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (dhEffect pid d p staticPublic precomputed e ck secret remote hash clock fresh.value rest) := by
  let ck2 := first ck (curve25519 secret remote).1
  let encStatic := aeadEncrypt (second ck (curve25519 secret remote).1) noiseNonce staticPublic hash
  let h2 := noiseHash (hash ++ encStatic)
  let records := some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest)
  have hd := dh_returns ck secret remote dhOk (fun k rs => k.wg = some d ∧ rs = records)
  have hc := (returns_iff _ _ _).mp (chain_returns pid d p resident ck2 h2 records)
  have ht := (returns_iff _ _ _).mp (afterPrecomputed_returns pid e encStatic ck2 precomputed h2
    (chainDevice pid d p ck2 h2) {p with chainingKey := ck2, hash := h2} (by simp [chainDevice])
    word nonnull clock width collisions fresh rest allCollide isFresh)
  rw [returns_iff]
  mvcgen [afterDh, branch, invariant, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all only [Option.some.injEq]
  all_goals subst_vars
  all_goals try simp_all [dhEffect]
  all_goals mvcgen [hc, ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [dhEffect, ck2, encStatic, h2, records]
  all_goals grind only

def afterEphemeral (pid : PeerId) (staticPublic precomputed e secret remote hash : List UInt8) :
    M (Option (List UInt8)) := do
  let (ck, h) ← messageEphemeral false e handshakeInitChainingKey hash
  setChain pid ck h
  afterDh pid staticPublic precomputed e ck secret remote h

def ephemeralEffect (pid : PeerId) (d : Device) (p : Peer)
    (staticPublic precomputed e secret remote hash clock : List UInt8)
    (index : Nat) (rest : List HiddenRecord) : Option (List UInt8) → World → Prop :=
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
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Returns (afterEphemeral pid staticPublic precomputed e secret remote hash)
      (fun w => w.k.wg = some d ∧ w.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (ephemeralEffect pid d p staticPublic precomputed e secret remote hash clock fresh.value rest) := by
  let records := some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest)
  unfold afterEphemeral
  apply returns_bind _ _ ((returns_iff _ _ _).mpr
    (ephemeral_returns e handshakeInitChainingKey hash (fun k rs => k.wg = some d ∧ rs = records)))
  intro pair w pre
  obtain ⟨same, device, stream⟩ := pre
  subst pair
  apply returns_bind _ _ (chain_returns pid d p resident (first handshakeInitChainingKey e)
    (noiseHash (hash ++ e)) records) _ w ⟨device, stream⟩
  intro u
  exact afterDh_returns pid staticPublic precomputed e (first handshakeInitChainingKey e) secret remote
    (noiseHash (hash ++ e)) (chainDevice pid d p (first handshakeInitChainingKey e) (noiseHash (hash ++ e)))
    {p with chainingKey := first handshakeInitChainingKey e, hash := noiseHash (hash ++ e)}
    (by simp [chainDevice]) word nonnull dhOk clock width collisions fresh rest allCollide isFresh

def afterPublic (pid : PeerId) (staticPublic precomputed secret remote hash : List UInt8) :
    M (Option (List UInt8)) := do
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
    (isFresh : (Index.removeOwner (.handshake pid) d.indexTable).any (·.index == fresh.value) = false) :
    Returns (afterPublic pid staticPublic precomputed secret remote hash)
      (fun w => w.k.wg = some d ∧ w.hidden =
        some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
      (ephemeralEffect pid d p staticPublic precomputed (curve25519 secret basePoint).1
        secret remote hash clock fresh.value rest) := by
  have hp := public_returns secret secretNonNull pubOk
    (fun k rs => k.wg = some d ∧ rs = some ({site := 3, bytes := clock} :: Index.drawStream collisions fresh rest))
  have ht := (returns_iff _ _ _).mp (afterEphemeral_returns pid staticPublic precomputed
    (curve25519 secret basePoint).1 secret remote hash d p resident word nonnull dhOk
    clock width collisions fresh rest allCollide isFresh)
  rw [returns_iff]
  mvcgen [afterPublic, branch, invariant, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq]
  all_goals subst_vars
  all_goals try simp_all
  all_goals mvcgen [ht]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals grind only

def setSecret (pid : PeerId) (secret : List UInt8) : M Unit := do
  setPeer pid {(← getPeer pid) with ephemeralPrivate := secret}
theorem setSecret_returns (pid : PeerId) (secret : List UInt8)
    (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) (records : Option (List HiddenRecord)) :
    Returns (setSecret pid secret) (fun w => w.k.wg = some d ∧ w.hidden = records)
      (fun _ w => w.k.wg = some (secretDevice pid d p secret) ∧ w.hidden = records) := by
  rw [returns_iff]
  mvcgen [setSecret, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [secretDevice]
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
