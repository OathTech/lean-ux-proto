import Layouts
import Memory
set_option maxRecDepth 4096
namespace Binary
-- Generated from the pinned image by binary/device_layouts.py.
/-- Stable device words and exact non-placeholder keys. Pointer, ring,
    netdevice and ownership components remain separate. Signed CPU
    words use two's-complement decoding, never unbounded modular equality. -/
structure DeviceStableFields (m : Mem 64) (a : BitVec 64)
    (d : Leanux.WG.Device) : Prop where
  handshakeQueueLen : m.loadInt (a + .ofNat 64 568) 4 = some (d.handshakeQueueLen : Int)
  numPeers : m.loadInt (a + .ofNat 64 572) 4 = some (d.numPeers : Int)
  deviceUpdateGen : m.loadInt (a + .ofNat 64 576) 4 = some (d.deviceUpdateGen : Int)
  fwmark : m.loadInt (a + .ofNat 64 580) 4 = some (d.fwmark : Int)
  incomingPort : m.loadInt (a + .ofNat 64 584) 2 = some (d.incomingPort : Int)
  staticIdentity_staticPublic : m.loadBytes (a + .ofNat 64 176) 32 = some d.staticIdentity.staticPublic
  staticIdentity_staticPrivate : m.loadBytes (a + .ofNat 64 208) 32 = some d.staticIdentity.staticPrivate
  staticIdentity_hasIdentity : m.loadInt (a + .ofNat 64 272) 1 = some (if d.staticIdentity.hasIdentity then 1 else 0)
  cookieEncryptionKey : m.loadBytes (a + .ofNat 64 336) 32 = some d.cookieEncryptionKey
  mac1Key : m.loadBytes (a + .ofNat 64 368) 32 = some d.mac1Key
  encryptLastCpu : ∃ raw : BitVec 32, m.loadInt (a + .ofNat 64 48) 4 = some (raw.toNat : Int) ∧ raw.toInt = d.encryptLastCpu
  decryptLastCpu : ∃ raw : BitVec 32, m.loadInt (a + .ofNat 64 96) 4 = some (raw.toNat : Int) ∧ raw.toInt = d.decryptLastCpu
  handshakeLastCpu : ∃ raw : BitVec 32, m.loadInt (a + .ofNat 64 144) 4 = some (raw.toNat : Int) ∧ raw.toInt = d.handshakeLastCpu

def deviceStableOffsets : List (Nat × Nat) :=
  [(568, 4), (572, 4), (576, 4), (580, 4), (584, 2), (176, 32), (208, 32), (272, 1), (336, 32), (368, 32), (48, 4), (96, 4), (144, 4)]

def deviceStableLocations (a : BitVec 64) : List (BitVec 64 × Nat) :=
  deviceStableOffsets.map (fun cell => (a + .ofNat 64 cell.1, cell.2))

private theorem device_loadInt {before after : Mem 64} {writes : BitVec 64 → Prop}
    (a : BitVec 64) (same : EqualOutside writes before after)
    (apart : ∀ location ∈ deviceStableLocations a, ∀ i < location.2,
      ¬writes (location.1 + .ofNat 64 i))
    (off size : Nat) (member : (off, size) ∈ deviceStableOffsets) :
    before.loadInt (a + .ofNat 64 off) size = after.loadInt (a + .ofNat 64 off) size := by
  apply EqualOutside.loadInt same
  exact apart _ (List.mem_map_of_mem (f := fun cell : Nat × Nat =>
    (a + .ofNat 64 cell.1, cell.2)) member)

private theorem device_loadBytes {before after : Mem 64} {writes : BitVec 64 → Prop}
    (a : BitVec 64) (same : EqualOutside writes before after)
    (apart : ∀ location ∈ deviceStableLocations a, ∀ i < location.2,
      ¬writes (location.1 + .ofNat 64 i))
    (off size : Nat) (member : (off, size) ∈ deviceStableOffsets) :
    before.loadBytes (a + .ofNat 64 off) size = after.loadBytes (a + .ofNat 64 off) size := by
  apply EqualOutside.loadBytes same
  exact apart _ (List.mem_map_of_mem (f := fun cell : Nat × Nat =>
    (a + .ofNat 64 cell.1, cell.2)) member)

theorem DeviceStableFields.frame {before after : Mem 64} {writes : BitVec 64 → Prop}
    {a : BitVec 64} {d : Leanux.WG.Device}
    (same : EqualOutside writes before after)
    (apart : ∀ location ∈ deviceStableLocations a, ∀ i < location.2,
      ¬writes (location.1 + .ofNat 64 i))
    (h : DeviceStableFields before a d) : DeviceStableFields after a d := by
  refine {handshakeQueueLen := ?_, numPeers := ?_, deviceUpdateGen := ?_, fwmark := ?_, incomingPort := ?_, staticIdentity_staticPublic := ?_, staticIdentity_staticPrivate := ?_, staticIdentity_hasIdentity := ?_, cookieEncryptionKey := ?_, mac1Key := ?_, encryptLastCpu := ?_, decryptLastCpu := ?_, handshakeLastCpu := ?_}
  · exact (device_loadInt a same apart 568 4 (by decide)).symm.trans h.handshakeQueueLen
  · exact (device_loadInt a same apart 572 4 (by decide)).symm.trans h.numPeers
  · exact (device_loadInt a same apart 576 4 (by decide)).symm.trans h.deviceUpdateGen
  · exact (device_loadInt a same apart 580 4 (by decide)).symm.trans h.fwmark
  · exact (device_loadInt a same apart 584 2 (by decide)).symm.trans h.incomingPort
  · exact (device_loadBytes a same apart 176 32 (by decide)).symm.trans h.staticIdentity_staticPublic
  · exact (device_loadBytes a same apart 208 32 (by decide)).symm.trans h.staticIdentity_staticPrivate
  · exact (device_loadInt a same apart 272 1 (by decide)).symm.trans h.staticIdentity_hasIdentity
  · exact (device_loadBytes a same apart 336 32 (by decide)).symm.trans h.cookieEncryptionKey
  · exact (device_loadBytes a same apart 368 32 (by decide)).symm.trans h.mac1Key
  · obtain ⟨raw, loaded, decoded⟩ := h.encryptLastCpu
    exact ⟨raw, (device_loadInt a same apart 48 4 (by decide)).symm.trans loaded, decoded⟩
  · obtain ⟨raw, loaded, decoded⟩ := h.decryptLastCpu
    exact ⟨raw, (device_loadInt a same apart 96 4 (by decide)).symm.trans loaded, decoded⟩
  · obtain ⟨raw, loaded, decoded⟩ := h.handshakeLastCpu
    exact ⟨raw, (device_loadInt a same apart 144 4 (by decide)).symm.trans loaded, decoded⟩

#print axioms DeviceStableFields.frame
end Binary
