import Layouts
import Memory
import Leanux.Kernel.Defs

namespace Binary.FixtureKnowledge

/-- Only these documented fixture placeholders admit opaque initial values.
    This enumeration is not an arbitrary mask over the mirror's fields. -/
inductive Field where
  | cookieSecret | cookieBirthdate | pubkeyHashKey | ratelimiterKey
  deriving DecidableEq, BEq

def Field.bytes : Field → Nat
  | .cookieSecret => 32
  | .cookieBirthdate => 8
  | .pubkeyHashKey | .ratelimiterKey => 16

/-- A committed physical field write, rather than merely a consumed record.
    Cookie initialization/rotation commits after both input records. The
    complete trace relation must justify these events from that execution. -/
structure CommittedWrite where
  field : Field
  deviceEpoch : Nat
  bytes : List UInt8

/-- Fixed incoming fixture/history context, never selected anew at a cut.
    A recreated device cannot inherit knowledge from an earlier lifetime. -/
structure Past where
  deviceEpoch : Nat
  pretraceDeviceEpoch : Option Nat
  writes : List CommittedWrite

inductive Origin where
  | fixtureOpaque
  | recorded (bytes : List UInt8)

/-- The global ratelimiter key survives uninit, including a bare fixture;
    its initial physical value need not be BSS zero. Device fields can be
    opaque only for the device that actually predates the captured trace. -/
def origin (past : Past) (field : Field) : Option Origin :=
  match past.writes.reverse.find? (fun write => write.field == field &&
      (field == .ratelimiterKey || write.deviceEpoch == past.deviceEpoch)) with
  | some write => some (.recorded write.bytes)
  | none => if field == .ratelimiterKey || past.pretraceDeviceEpoch == some past.deviceEpoch
      then some .fixtureOpaque else none

/-- Opaque means an exact mirror placeholder with mapped physical bytes,
    not physical zero bytes. A recorded value has three-way exact equality. -/
def Bytes (source : Origin) (memory : Mem 64) (address : BitVec 64)
    (length : Nat) (mirror : List UInt8) : Prop :=
  ∃ physical, memory.loadBytes address length = some physical ∧ physical.length = length ∧
    match source with
    | .fixtureOpaque => mirror = List.replicate length 0
    | .recorded recorded => physical = recorded ∧ mirror = recorded

def FieldAt (past : Past) (field : Field) (memory : Mem 64) (address : BitVec 64)
    (mirror : List UInt8) : Prop :=
  ∃ source, origin past field = some source ∧ Bytes source memory address field.bytes mirror

theorem Bytes.functional {source memory address length a b}
    (ha : Bytes source memory address length a) (hb : Bytes source memory address length b) : a = b := by
  obtain ⟨pa, hpa, hla, ha⟩ := ha
  obtain ⟨pb, hpb, hlb, hb⟩ := hb
  cases source with
  | fixtureOpaque => exact ha.trans hb.symm
  | recorded bytes => exact ha.2.trans hb.2.symm

theorem Bytes.frame {source before after address length mirror writes}
    (same : EqualOutside writes before after)
    (disjoint : ∀ i < length, ¬writes (address + .ofNat 64 i))
    (h : Bytes source before address length mirror) : Bytes source after address length mirror := by
  obtain ⟨physical, loaded, size, observed⟩ := h
  exact ⟨physical, (same.loadBytes address length disjoint).symm.trans loaded, size, observed⟩

theorem FieldAt.functional {past field memory address a b}
    (ha : FieldAt past field memory address a) (hb : FieldAt past field memory address b) : a = b := by
  obtain ⟨sa, hsa, ha⟩ := ha
  obtain ⟨sb, hsb, hb⟩ := hb
  have equal : sa = sb := Option.some.inj (hsa.symm.trans hsb)
  subst sb
  exact Bytes.functional ha hb

theorem FieldAt.frame {past field before after address mirror writes}
    (same : EqualOutside writes before after)
    (disjoint : ∀ i < field.bytes, ¬writes (address + .ofNat 64 i))
    (h : FieldAt past field before address mirror) : FieldAt past field after address mirror := by
  obtain ⟨source, selected, h⟩ := h
  exact ⟨source, selected, Bytes.frame same disjoint h⟩

/-- DWARF locations; pointer-shaped pubkey table traversal is explicit.
    These four fields are a component of whole-World R, not the whole R. -/
def Fields (past : Past) (memory : Mem 64) (deviceAddress : BitVec 64)
    (device : Leanux.WG.Device) (ratelimiter : Leanux.Ratelimiter) : Prop :=
  FieldAt past .cookieSecret memory
    (deviceAddress + .ofNat 64 (Layouts.device_cookie_checker + Layouts.cookie_secret)) device.cookieSecret ∧
  FieldAt past .cookieBirthdate memory
    (deviceAddress + .ofNat 64 (Layouts.device_cookie_checker + Layouts.cookie_secret_birthdate))
    (Int.toBytes 8 device.cookieSecretBirthdate.toBitVec.toInt) ∧
  (∃ table : BitVec 64, table ≠ 0 ∧
    memory.loadInt (deviceAddress + .ofNat 64 Layouts.device_peer_hashtable) 8 = some table.toNat ∧
    FieldAt past .pubkeyHashKey memory (table + .ofNat 64 Layouts.pubkeyTable_key) device.pubkeyHashKey) ∧
  FieldAt past .ratelimiterKey memory Layouts.ratelimiterKeyAddress ratelimiter.key

/-- The footprint includes the pointer used to reach the pubkey table,
    not merely the pointee key. All offsets come from the pinned DWARF. -/
def locations (deviceAddress table : BitVec 64) : List (BitVec 64 × Nat) :=
  [(deviceAddress + .ofNat 64 (Layouts.device_cookie_checker + Layouts.cookie_secret), 32),
   (deviceAddress + .ofNat 64 (Layouts.device_cookie_checker + Layouts.cookie_secret_birthdate), 8),
   (deviceAddress + .ofNat 64 Layouts.device_peer_hashtable, 8),
   (table + .ofNat 64 Layouts.pubkeyTable_key, 16),
   (Layouts.ratelimiterKeyAddress, 16)]

theorem Fields.frame {past before after deviceAddress device ratelimiter writes}
    (same : EqualOutside writes before after)
    (separate : ∀ table : BitVec 64,
      before.loadInt (deviceAddress + .ofNat 64 Layouts.device_peer_hashtable) 8 = some table.toNat →
      ∀ location ∈ locations deviceAddress table, ∀ i < location.2,
        ¬writes (location.1 + .ofNat 64 i))
    (represented : Fields past before deviceAddress device ratelimiter) :
    Fields past after deviceAddress device ratelimiter := by
  obtain ⟨secret, birthdate, ⟨table, nonnull, pointer, key⟩, global⟩ := represented
  have disjoint := separate table pointer
  have ds := disjoint (deviceAddress + .ofNat 64 (Layouts.device_cookie_checker + Layouts.cookie_secret), 32)
    (by simp [locations])
  have db := disjoint (deviceAddress + .ofNat 64 (Layouts.device_cookie_checker + Layouts.cookie_secret_birthdate), 8)
    (by simp [locations])
  have dp := disjoint (deviceAddress + .ofNat 64 Layouts.device_peer_hashtable, 8) (by simp [locations])
  have dk := disjoint (table + .ofNat 64 Layouts.pubkeyTable_key, 16) (by simp [locations])
  have dg := disjoint (Layouts.ratelimiterKeyAddress, 16) (by simp [locations])
  exact ⟨FieldAt.frame same ds secret, FieldAt.frame same db birthdate,
    ⟨table, nonnull, (same.loadInt _ 8 dp).symm.trans pointer, FieldAt.frame same dk key⟩,
    FieldAt.frame same dg global⟩

#print axioms Fields.frame
#print axioms Bytes.functional
#print axioms Bytes.frame
#print axioms FieldAt.functional
end Binary.FixtureKnowledge
