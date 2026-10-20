import AllowedipsRootRegions

namespace Binary.Pair.Allowedips.Root

/-- The four packed bytes assembled by the compiler's shifts and partial
register moves, before the node-header store. -/
def packed (width cidr : BitVec 32) : BitVec 32 :=
  (cidr &&& 255) ||| (((((width >>> 3)-1) &&& 7) ^^^ (cidr >>> 3)) <<< 8) |||
    ((~~~cidr &&& 7) <<< 16) ||| (width <<< 24)

/-- A small finite arithmetic fact checked by Lean's kernel. It is shared by
the root, child and intermediate-node initialization sites. -/
private theorem packed_finite : ∀ family : Bool, ∀ cidr : Fin 129,
    packed (.ofNat 32 (if family then 32 else 128)) (.ofNat 32 cidr.val)=
      .ofNat 32 (headerWord (if family then 32 else 128) cidr.val) := by
  decide +kernel

theorem packed_header (width cidr : Nat) (family : width=32 ∨ width=128) (bound : cidr≤width) :
    packed (.ofNat 32 width) (.ofNat 32 cidr)=.ofNat 32 (headerWord width cidr) := by
  rcases family with rfl|rfl
  · exact packed_finite true ⟨cidr,by omega⟩
  · exact packed_finite false ⟨cidr,by omega⟩

#print axioms packed_header
end Binary.Pair.Allowedips.Root
