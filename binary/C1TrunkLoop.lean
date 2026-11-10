import C1TrunkHeld
/-! Result C1, package 2: the landed placement loop entered from
propositions. `Placement.loop_checked` takes the executable `header`; its
proof uses only the fields `header_fields` extracts and the `TrieHeap` that
`callInput` yields. `loop_from` is that proof (origin:
`AllowedipsPlacementChecked.loop_checked` and `HeaderFields.initial`, copied)
with those as hypotheses, so the header is established without evaluating
the executable check. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Pair.Allowedips.Placement AllowedipsRelation Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem loop_from (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (mutation : AllowedipsMutationDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {c : Context} {d : Device}
    {s : MachineState} {root : Option NodeId} {key cidr bits peer stack : Nat}
    (related : Corresponds names o s.data.dmem d)
    (shape : heap names (target d) s.data.dmem=.ok ())
    (trie : TrieHeap s.data.dmem (Trie.interpretation names.trie.nodes)
      (Trie.interpretation names.trie.peers) (fun id => d.nodes.get? id) root bits key)
    (locals : LocalFields names s key cidr bits peer stack (none,root,none))
    (pc : s.pc=Add.entry+0xf7) (cidrBound : cidr≤bits)
    (frame : Frame s.data c s.data)
    (readApart : ∀ span ∈ readSpans names o, ∀ a, span.contains a → ¬Writes s.data.regs.rsp c a)
    (queryApart : ∀ a, InRange s.data.regs.r13.toBitVec (bits/8) a → ¬Writes s.data.regs.rsp c a)
    (savedApart : ∀ a, InRange (s.data.regs.rsp.toBitVec+0x24) 4 a ∨
      InRange (s.data.regs.rsp.toBitVec+0x18) 8 a → ¬Writes s.data.regs.rsp c a)
    (ambient finalAmbient : Ambient) (finalStore : AipStore) (result : Option NodeId × Bool)
    (accepted : ((WG.nodePlacement root key cidr bits).run (Source.Aip.store d)).run ambient=
      .ok ((result,finalStore),finalAmbient)) :
    Eventually (instructionStep fetch) (fun t =>
      finalStore=Source.Aip.store d ∧ Frame s.data c t.data ∧
      t.pc=(if result.2 then Add.entry+0x3ca else Add.entry+0x120) ∧
      t.data.regs.rbx=ptr (Trie.interpretation names.trie.nodes) result.1 ∧
      (result.2=false → t.data.regs.rbp=.ofBitVec ((BitVec.ofNat 32 bits).setWidth 64) ∧
        t.data.regs.r14=.ofNat peer) ∧
      Corresponds names o t.data.dmem d ∧ heap names (target d) t.data.dmem=.ok ()) s := by
  have small : bits<2^32 := by rcases trie.1 with h|h <;> omega
  have saved : SavedInput s.data c (.ofNat 32 bits) (.ofNat 64 peer) := by
    refine ⟨?_,locals.peerRead,savedApart⟩
    change s.data.dmem.loadInt (s.data.regs.rsp.toBitVec+0x24) 4=some ((BitVec.ofNat 32 bits).toNat : Int)
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using locals.widthRead
  have inputs := inputs_of_heap related trie locals cidrBound readApart queryApart saved
  have initial : Invariant names o d s.data c root key cidr bits (.ofNat 64 peer)
      (none,root,none) (Source.Aip.store d) ambient s := by
    refine ⟨rfl,frame,?_,related,shape⟩
    have parent := locals.previous
    obtain ⟨id,rootAt⟩ := Option.isSome_iff_exists.mp locals.nonempty
    change root=some id at rootAt
    refine ⟨parent,?_⟩
    rw [rootAt]
    refine ⟨pc,?_,.root id rfl⟩
    apply UInt64.toBitVec_inj.mp
    simpa only [rootAt,pointer,Option.map_some,Option.getD_some,UInt64.toBitVec_ofBitVec] using locals.cursor
  exact loop fetch decoder mutation callbacks cmp inputs related shape readApart
    ambient finalAmbient finalStore result s accepted initial

#print axioms loop_from
end C1Trunk
