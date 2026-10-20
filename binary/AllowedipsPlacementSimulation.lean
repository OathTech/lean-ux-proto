import AllowedipsPlacementIteration
import PairAllowedipsHeapFrame

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG TrustBase CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem metadata_read {names o span} (member : span ∈ metadataSpans names o) : span ∈ readSpans names o := by
  simp only [metadataSpans,List.mem_append,List.mem_flatMap] at member
  rcases member with table | node | ⟨⟨id,a⟩,named,field⟩
  · exact List.mem_append_left _ table
  · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr node))
  · obtain ⟨⟨offset,size⟩,field,equal⟩ := List.mem_map.mp field
    have field' : (offset,size) ∈ peerFields o := by
      simp only [listFields,List.mem_cons,List.not_mem_nil,or_false] at field
      rcases field with h|h <;> cases h <;> simp [peerFields]
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨(id,a),named,List.mem_map.mpr ⟨(offset,size),field',equal⟩⟩))


structure Invariant (names : Names) (o : AllowedipsProbe.Offsets) (d : Device)
    (base : MachineData) (c : Context) (root : Option NodeId) (key cidr bits : Nat) (peer : BitVec 64)
    (acc : Acc) (store : AipStore) (_ : Ambient) (machine : MachineState) : Prop where
  source : store=Source.Aip.store d
  frame : Frame base c machine.data
  position : Position (Trie.interpretation names.trie.nodes) (Source.Aip.store d) root bits key peer acc machine
  related : Corresponds names o machine.data.dmem d
  heap : Allowedips.heap names (target d) machine.data.dmem=.ok ()

/-- The actual source loop is composed through its R invariant. Inputs still
name the physical entry read facts; the executable-boundary bridge is separate.
No assumed physical iteration, future correspondence or history appears here. -/
theorem loop (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (mutation : AllowedipsMutationDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {names o d base c root key cidr bits peer}
    (inputs : Inputs base c (Trie.interpretation names.trie.nodes) (Source.Aip.store d) root key cidr bits peer)
    (related : Corresponds names o base.dmem d)
    (shape : Allowedips.heap names (target d) base.dmem=.ok ())
    (apart : ∀ span ∈ readSpans names o, ∀ a, span.contains a → ¬Writes base.regs.rsp c a)
    (ambient finalAmbient : Ambient) (finalStore : AipStore) (result : Option NodeId × Bool)
    (machine : MachineState)
    (accepted : ((WG.nodePlacement root key cidr bits).run (Source.Aip.store d)).run ambient=
      .ok ((result,finalStore),finalAmbient))
    (initial : Invariant names o d base c root key cidr bits peer (none,root,none)
      (Source.Aip.store d) ambient machine) :
    Eventually (instructionStep fetch) (fun t =>
      finalStore=Source.Aip.store d ∧ Frame base c t.data ∧
      t.pc=(if result.2 then Add.entry+0x3ca else Add.entry+0x120) ∧
      t.data.regs.rbx=ptr (Trie.interpretation names.trie.nodes) result.1 ∧
      (result.2=false → t.data.regs.rbp=.ofBitVec ((BitVec.ofNat 32 bits).setWidth 64) ∧
        t.data.regs.r14=.ofBitVec peer) ∧
      Corresponds names o t.data.dmem d ∧ Allowedips.heap names (target d) t.data.dmem=.ok ()) machine := by
  have body := compose_loop fetch root key cidr bits (Invariant names o d base c root key cidr bits peer)
    (by
      intro acc store ambient next nextStore nextAmbient current accepted openLoop invariant
      rcases invariant with ⟨rfl,frame,position,_,_⟩
      obtain ⟨selected,source⟩ := iteration_accepted accepted
      have physical := inputs.step fetch decoder mutation callbacks cmp acc next current selected openLoop frame position
      apply eventually_weaken (instructionStep fetch) _ _ _ _ physical
      rintro t ⟨framed,position⟩
      have correspondence : Corresponds names o t.data.dmem d :=
        (reconstruct_frame names o framed.memory apart).symm.trans related
      have shape' := (heap_frame names o (target d) framed.memory
        (fun span member => apart span (metadata_read member))).symm.trans shape
      cases next <;> exact ⟨source,framed,position,correspondence,shape'⟩)
    (Source.Aip.store d) finalStore ambient finalAmbient result machine accepted initial
  apply eventually_weaken (instructionStep fetch) _ _ _ _ body
  rintro t ⟨acc,resultEq,invariant⟩
  have pos := invariant.position
  simp only [Position,resultEq] at pos
  exact ⟨invariant.source,invariant.frame,pos.1,pos.2.1,pos.2.2,invariant.related,invariant.heap⟩

#print axioms loop
end Binary.Pair.Allowedips.Placement
