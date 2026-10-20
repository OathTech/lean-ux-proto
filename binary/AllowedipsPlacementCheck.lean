import AllowedipsPlacementInputs
import PairAllowedipsAssert
import PairHeapProof

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG TrustBase CommonBitsCoverage AllowedipsMutationImage

/-- The concrete finite write cover used by the executable header. -/
theorem writes_cover (c : Context) (s : MachineState) : Covers (writes c s) (Writes s.data.regs.rsp c) := by
  intro a written
  rcases written with stack | coverage
  · exact (Covers.range (s.data.regs.rsp.toBitVec-48) 56).append_left a stack
  · exact (show Covers (Trie.writeSpans c) c.writes from fun _ h => Trie.writeSpans_cover h).append_right a coverage

theorem separated {c s reads} (checked : spansApart reads (writes c s)=true) :
    ∀ span ∈ reads, ∀ a, span.contains a → ¬Writes s.data.regs.rsp c a := by
  intro span member a inside written
  obtain ⟨write,member',inside'⟩ := writes_cover c s a written
  exact spansApart_sound checked member member' inside inside'

theorem heap_trie {names d m} (checked : heap names (target d) m=.ok ()) :
    Trie.heap (Trie.target d) [d.peerAllowedips.root4,d.peerAllowedips.root6]=.ok () := by
  unfold heap at checked
  obtain ⟨value,core,_⟩ := bind_ok checked
  cases value
  change Trie.heap (trieState (target d)) [d.peerAllowedips.root4,d.peerAllowedips.root6]=.ok () at core
  simpa only [trieState_target] using core

structure HeaderFields (names : Names) (o : AllowedipsProbe.Offsets) (c : Context)
    (w : World) (s : MachineState) (root : Option NodeId)
    (key cidr bits peer stack : Nat) (acc : Acc) : Prop where
  asserted : assertAt names o s.data.dmem w=.ok ()
  input : Trie.callInput names.trie o s.data.dmem root bits key=.ok ()
  locals : LocalFields names s key cidr bits peer stack acc
  pc : s.pc=Add.entry+0xf7
  cidrBound : cidr≤bits
  frame : Frame s.data c s.data
  readApart : ∀ span ∈ readSpans names o, ∀ a, span.contains a → ¬Writes s.data.regs.rsp c a
  queryApart : ∀ a, InRange s.data.regs.r13.toBitVec (bits/8) a → ¬Writes s.data.regs.rsp c a
  savedApart : ∀ a, InRange (s.data.regs.rsp.toBitVec+0x24) 4 a ∨
    InRange (s.data.regs.rsp.toBitVec+0x18) 8 a → ¬Writes s.data.regs.rsp c a

theorem header_fields {names o c w s root key cidr bits peer stack acc}
    (checked : header names o c w s root key cidr bits peer stack acc=.ok ()) :
    HeaderFields names o c w s root key cidr bits peer stack acc := by
  unfold header at checked
  obtain ⟨_,asserted,checked⟩ := bind_ok checked
  obtain ⟨_,input,checked⟩ := bind_ok checked
  obtain ⟨_,localCheck,checked⟩ := bind_ok checked
  obtain ⟨pc,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨cidrBound,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨framed,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨service,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨reads,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨query,checked⟩ := require_bind_ok _ _ _ _ checked
  have saved := require_ok checked
  have localFields := locals_fields localCheck
  refine ⟨asserted,input,localFields,eq_of_beq pc,of_decide_eq_true cidrBound,
    Frame.initial framed service,separated reads,?_,?_⟩
  · exact spansApart_disjoint query (Covers.range s.data.regs.r13.toBitVec (bits/8)) (writes_cover c s)
  · intro a inside
    have sp := Trie.u64_of_nat localFields.stackValue
    rcases inside with width | owner
    · apply separated saved (stack+0x24,4) (by simp) a
      simpa only [Span.contains,BitVec.ofNat_add,show BitVec.ofNat 64 36=(36 : BitVec 64) from rfl,sp] using width
    · apply separated saved (stack+0x18,8) (by simp) a
      simpa only [Span.contains,BitVec.ofNat_add,show BitVec.ofNat 64 24=(24 : BitVec 64) from rfl,sp] using owner

#print axioms header_fields
end Binary.Pair.Allowedips.Placement
