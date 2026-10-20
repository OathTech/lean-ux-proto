import AllowedipsObservation

namespace Binary.AllowedipsLoop
open LookupObservation

/-- A proof convenience for scalar regions. Soundness is checked against
`AllowedipsObservation.edge` below; this list does not drive execution. -/
def observingPCs : List Int64 :=
  let l := AllowedipsImage.Lookup.entry
  let c := AllowedipsImage.CommonBits.entry
  [l+0x41,l+0x5b,l+0x81,l+0xd3,l+0xff,l+0x9b,l+0xb2,l+0x109,l+0x11c,
   l+0xe5,l+0x114,l+0x14e,c+0x24,c+0x3c,c+0x91,c+0x4b,c+0x74,c+0xc3,
   Image.PeerGet.entry+0xaf]

def Quiet (pc : Int64) : Prop :=
  pc ∉ observingPCs ∧ (Image.fetchIn Image.PeerGet.entry Image.PeerGet.code pc).isSome = false

theorem quiet_edge (rxSection : Nat) (before after : MachineState) (quiet : Quiet before.pc) :
    AllowedipsObservation.edge rxSection before after = .ok [] := by
  rcases quiet with ⟨outside,unmapped⟩
  simp only [observingPCs,List.mem_cons,List.not_mem_nil,or_false,not_or] at outside
  rcases outside with ⟨h41,h5b,h81,hd3,hff,h9b,hb2,h109,h11c,he5,h114,h14e,
    h24,h3c,h91,h4b,h74,hc3,het⟩
  simp only [AllowedipsObservation.edge,h41,h5b,h81,hd3,hff,h9b,hb2,h109,h11c,
    he5,h114,h14e,h24,h3c,h91,h4b,h74,hc3,het,unmapped,false_or,ite_false,
    Bool.false_eq_true]
  rfl

#print axioms quiet_edge
end Binary.AllowedipsLoop
