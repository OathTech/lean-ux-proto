import AllowedipsLoopInput

namespace Binary.AllowedipsLoop
open Leanux.WG

def commonSignature (rxSection bits query : Nat) (node : AipNode) : List CommonBits.EventView :=
  [(.call "common_bits",none)] ++
  (AllowedipsSource.commonChoices node query bits).map (fun (d,b) => CommonBits.decisionView rxSection d b) ++
  [CommonBits.returnedView]

theorem input_signature (s : MachineData) (bits query rxSection : Nat) (node : AipNode)
    (family : bits = 32 ∨ bits = 128) (storedBound : node.bits < 2^bits) (queryBound : query < 2^bits) :
    ((.call "common_bits",none)::(input s bits node.bits query).signature rxSection) =
      commonSignature rxSection bits query node := by
  rcases family with rfl | rfl
  · rfl
  · have highEq := input_high_eq s node.bits query storedBound queryBound
    have choices : ((input s 128 node.bits query).storedHigh != (input s 128 node.bits query).queryHigh) =
        ((node.bits ^^^ query)/2^64 != 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne,Nat.xor_div_two_pow]
      exact not_congr (highEq.trans (xor_zero_iff _ _).symm)
    simp only [CommonBits.Input.signature,CommonBits.Input.signatureOther,CommonBits.Input.signature128,
      show (input s 128 node.bits query).family = 128#8 from rfl]
    simp only [show (128#8 == 32#8)=false from rfl,show ¬(128#8=32#8) by decide,
      show (128#8 == 128#8)=true from rfl,↓reduceIte,choices]
    rfl

#print axioms input_signature
end Binary.AllowedipsLoop
