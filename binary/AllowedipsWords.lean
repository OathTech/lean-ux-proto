import Memory

namespace Binary.Allowedips
def swap32 (a : BitVec 32) : BitVec 32 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8

def swap64 (a : BitVec 64) : BitVec 64 :=
  a.extractLsb' 0 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.extractLsb' 56 8

/-- Exact network-order input interpretation, related through the actual
    BSWAP value rather than assuming placeholder bytes or a host address. -/
def NetworkKey (m : Mem 64) (base : BitVec 64) (bits key : Nat) : Prop :=
  if bits = 32 then ∃ word : BitVec 32,
    m.loadInt base 4 = some word.toNat ∧ (swap32 word).toNat = key
  else ∃ high low : BitVec 64,
    m.loadInt base 8 = some high.toNat ∧ m.loadInt (base+8) 8 = some low.toNat ∧
    (swap64 high).toNat*2^64+(swap64 low).toNat = key

def NetworkReads (base : BitVec 64) (bits : Nat) (a : BitVec 64) : Prop :=
  InRange base (if bits=32 then 4 else 16) a
end Binary.Allowedips
