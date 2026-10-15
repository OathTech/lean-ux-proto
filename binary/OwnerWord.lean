import PeerScalars
import KeypairRepresentation
import Leanux.WG.Peer

set_option maxRecDepth 4096

namespace Binary.OwnerWord
open Leanux Leanux.WG

/-- The outer Option detects a missing owner; inner none is the owner's
    actual NULL peer word. Ownership never comes from the nullable word. -/
def value (device : Device) : IndexOwner → Option (Option PeerId)
  | .handshake id => (device.peers.get? id).map (·.handshakeEntryPeer)
  | .keypair id => (device.keypairs.get? id).map (·.peer)

def pointer (peers : PeerId → BitVec 64) : Option PeerId → BitVec 64
  | none => 0
  | some id => peers id

/-- Lifetime names include zero-count peers still represented in the store.
    Retirement requires a separate no-reader argument, not positivity. -/
structure PeerNames (present : PeerId → Prop) where
  address : PeerId → BitVec 64
  nonnull : ∀ id, present id → address id ≠ 0
  unique : ∀ i j, present i → present j → address i = address j → i = j

def Named (present : PeerId → Prop) : Option PeerId → Prop
  | none => True
  | some id => present id

def address (peers : PeerId → BitVec 64) (keypairs : KeypairId → BitVec 64) :
    IndexOwner → BitVec 64
  | .handshake id => peers id + .ofNat 64 peerHandshakePeerOffset
  | .keypair id => keypairs id + .ofNat 64 (Layouts.keypair_entry + Layouts.entry_peer)

/-- The address is the peer field itself; entry_peer is zero in this image. -/
def Field (peers : PeerId → BitVec 64) (memory : Mem 64) (location : BitVec 64)
    (word : Option PeerId) : Prop :=
  memory.loadInt location 8 = some ((pointer peers word).toNat : Int)

def At (peers : PeerId → BitVec 64) (keypairs : KeypairId → BitVec 64)
    (memory : Mem 64) (device : Device) (owner : IndexOwner) : Prop :=
  ∃ word, value device owner = some word ∧ Field peers memory (address peers keypairs owner) word

theorem pointer_injective {present} (names : PeerNames present)
    {first second : Option PeerId} (hf : Named present first) (hs : Named present second)
    (equal : pointer names.address first = pointer names.address second) : first = second := by
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some id => exact False.elim (names.nonnull id hs equal.symm)
  | some id =>
    cases second with
    | none => exact False.elim (names.nonnull id hf equal)
    | some other => exact congrArg some (names.unique id other hf hs equal)

theorem Field.functional {present} (names : PeerNames present) {memory location a b}
    (ha : Field names.address memory location a) (hb : Field names.address memory location b)
    (na : Named present a) (nb : Named present b) : a = b := by
  apply pointer_injective names na nb
  apply BitVec.eq_of_toNat_eq
  have words := Option.some.inj (ha.symm.trans hb)
  omega

theorem Field.store (peers : PeerId → BitVec 64) (memory : Mem 64)
    (location : BitVec 64) (word : Option PeerId) :
    Field peers (memory.storeInt location 8 (pointer peers word).toInt) location word :=
  load64_store memory location (pointer peers word)

theorem Field.frame {peers before after location word writes}
    (same : EqualOutside writes before after)
    (apart : ∀ i < 8, ¬writes (location + .ofNat 64 i))
    (h : Field peers before location word) : Field peers after location word :=
  (same.loadInt location 8 apart).symm.trans h

/-- The scalar keypair predicate does not separately encode its peer ID.
    Updating that ID is reflected by Field, not a second physical word. -/
theorem keypair_field_update (memory : Mem 64) (base word : BitVec 64)
    (kp : Keypair) (peer : Option PeerId) :
    Layouts.KeypairFields memory base word {kp with peer} ↔
      Layouts.KeypairFields memory base word kp := Iff.rfl

/-- A store through a handshake owner updates that same owner's unique
    field, including NULL; its identity remains independent of the value. -/
theorem handshake_store_at (peers : PeerId → BitVec 64) (keypairs : KeypairId → BitVec 64)
    (memory : Mem 64) (device : Device) (id : PeerId) (peer : Peer) (word : Option PeerId) :
    At peers keypairs
      (memory.storeInt (address peers keypairs (.handshake id)) 8 (pointer peers word).toInt)
      {device with peers := device.peers.insert id {peer with handshakeEntryPeer := word}}
      (.handshake id) := by
  refine ⟨word, ?_, Field.store _ _ _ _⟩
  simp [value]

theorem keypair_store_at (peers : PeerId → BitVec 64) (keypairs : KeypairId → BitVec 64)
    (memory : Mem 64) (device : Device) (id : KeypairId) (kp : Keypair) (word : Option PeerId) :
    At peers keypairs
      (memory.storeInt (address peers keypairs (.keypair id)) 8 (pointer peers word).toInt)
      {device with keypairs := device.keypairs.insert id {kp with peer := word}}
      (.keypair id) := by
  refine ⟨word, ?_, Field.store _ _ _ _⟩
  simp [value]

theorem handshake_stable_update (memory : Mem 64) (base : BitVec 64)
    (peer : Peer) (word : Option PeerId) :
    PeerStableFields memory base {peer with handshakeEntryPeer := word} ↔
      PeerStableFields memory base peer := by
  constructor
  · intro h; exact {persistentKeepaliveInterval := h.persistentKeepaliveInterval, isDead := h.isDead, serialWorkCpu := h.serialWorkCpu, internalId := h.internalId, lastSentHandshake := h.lastSentHandshake, txBytes := h.txBytes, rxBytes := h.rxBytes, walltimeLastHandshake := h.walltimeLastHandshake, timerHandshakeAttempts := h.timerHandshakeAttempts, timerNeedAnotherKeepalive := h.timerNeedAnotherKeepalive, sentLastminuteHandshake := h.sentLastminuteHandshake, remoteStatic := h.remoteStatic, presharedKey := h.presharedKey, precomputedStaticStatic := h.precomputedStaticStatic, lastInitiationConsumption := h.lastInitiationConsumption, handshakeState := h.handshakeState, latestTimestamp := h.latestTimestamp, remoteIndex := h.remoteIndex, ephemeralPrivate := h.ephemeralPrivate, remoteEphemeral := h.remoteEphemeral, chainingKey := h.chainingKey, hash := h.hash, cookieMac1Key := h.cookieMac1Key, lastMac1Sent := h.lastMac1Sent, haveSentMac1 := h.haveSentMac1, cookieDecryptionKey := h.cookieDecryptionKey, cookie := h.cookie, cookieBirthdate := h.cookieBirthdate, cookieIsValid := h.cookieIsValid}
  · intro h; exact {persistentKeepaliveInterval := h.persistentKeepaliveInterval, isDead := h.isDead, serialWorkCpu := h.serialWorkCpu, internalId := h.internalId, lastSentHandshake := h.lastSentHandshake, txBytes := h.txBytes, rxBytes := h.rxBytes, walltimeLastHandshake := h.walltimeLastHandshake, timerHandshakeAttempts := h.timerHandshakeAttempts, timerNeedAnotherKeepalive := h.timerNeedAnotherKeepalive, sentLastminuteHandshake := h.sentLastminuteHandshake, remoteStatic := h.remoteStatic, presharedKey := h.presharedKey, precomputedStaticStatic := h.precomputedStaticStatic, lastInitiationConsumption := h.lastInitiationConsumption, handshakeState := h.handshakeState, latestTimestamp := h.latestTimestamp, remoteIndex := h.remoteIndex, ephemeralPrivate := h.ephemeralPrivate, remoteEphemeral := h.remoteEphemeral, chainingKey := h.chainingKey, hash := h.hash, cookieMac1Key := h.cookieMac1Key, lastMac1Sent := h.lastMac1Sent, haveSentMac1 := h.haveSentMac1, cookieDecryptionKey := h.cookieDecryptionKey, cookie := h.cookie, cookieBirthdate := h.cookieBirthdate, cookieIsValid := h.cookieIsValid}

#print axioms handshake_store_at
#print axioms keypair_store_at
#print axioms handshake_stable_update

#print axioms pointer_injective
#print axioms Field.functional
#print axioms Field.store
#print axioms Field.frame
#print axioms keypair_field_update
end Binary.OwnerWord
