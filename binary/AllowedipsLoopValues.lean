import AllowedipsSourceSelect
import TrieHeap
import AllowedipsChild

namespace Binary.AllowedipsLoop
open Leanux Leanux.WG AllowedipsRelation

theorem common_value (node : AipNode) (query bits : Nat) :
    AllowedipsSource.commonValue node query bits = common bits node.bits query := by
  simp only [AllowedipsSource.commonValue,common,beq_iff_eq,bne_iff_ne]

theorem common_bound (bits stored query : Nat) (family : bits = 32 ∨ bits = 128) :
    common bits stored query ≤ bits := by
  rcases family with rfl | rfl
  · simp [common]
  · simp only [common,show ¬(128=32) by decide,↓reduceIte]
    omega

theorem pointer_some (addresses : Nat → BitVec 64) (identity : Option Nat)
    (nonnull : ∀ id, identity = some id → addresses id ≠ 0) :
    (pointer addresses identity != 0) = identity.isSome := by
  cases identity with
  | none => rfl
  | some id =>
    simp only [pointer,Option.map_some,Option.getD_some,Option.isSome_some]
    simpa only [bne_iff_ne] using nonnull id rfl

theorem byte_value (n : Nat) (small : n < 256) : (BitVec.ofNat 8 n).toNat = n :=
  Nat.mod_eq_of_lt small

theorem fields_lengths {memory nodes peers bits query id node}
    (fields : NodeFields memory nodes peers bits query id node)
    (family : bits = 32 ∨ bits = 128) :
    node.cidr < 256 ∧ common bits node.bits query < 256 := by
  have bound := common_bound bits node.bits query family
  have cidr := fields.2.1
  rcases family with rfl | rfl <;> omega

theorem query_frame {before after : Mem 64} {writes : BitVec 64 → Prop}
    {base : BitVec 64} {bits query : Nat}
    (family : bits = 32 ∨ bits = 128)
    (words : AllowedipsChild.QueryWords before base bits query)
    (frame : EqualOutside writes before after)
    (apart : ∀ a, InRange base (bits/8) a → ¬writes a) :
    AllowedipsChild.QueryWords after base bits query := by
  rcases family with rfl | rfl
  · change before.loadInt base 4 = some (query : Int) at words
    change after.loadInt base 4 = some (query : Int)
    exact (frame.loadInt base 4 (fun i hi => apart _ ⟨i,hi,rfl⟩)).symm.trans words
  · change before.loadInt base 8 = some ((query/2^64 : Nat) : Int) ∧
      before.loadInt (base+8) 8 = some ((query%2^64 : Nat) : Int) at words
    change after.loadInt base 8 = some ((query/2^64 : Nat) : Int) ∧
      after.loadInt (base+8) 8 = some ((query%2^64 : Nat) : Int)
    refine ⟨(frame.loadInt base 8 (fun i hi => apart _ ⟨i,by omega,rfl⟩)).symm.trans words.1,?_⟩
    apply Eq.trans _ words.2
    apply Eq.symm
    apply frame.loadInt
    intro i hi
    apply apart
    exact ⟨8+i,by omega,by simp only [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩

#print axioms query_frame
#print axioms common_value
#print axioms common_bound
#print axioms pointer_some
#print axioms fields_lengths
end Binary.AllowedipsLoop
