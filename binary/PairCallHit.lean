import PairCallFinish

namespace Binary.Pair.Trie
open Leanux Leanux.WG TrustBase CommonBitsCoverage AllowedipsCaller
local instance : Labels := Image.linkedLabels
set_option maxRecDepth 4096

theorem reconstructed_node_peer {names o m d id node}
    (related : Corresponds names o m d) (present : d.nodes.get? id=some node) :
    m.loadInt (interpretation names.nodes id) 8=
      some ((AllowedipsRelation.pointer (interpretation names.peers) node.peer).toNat : Int) := by
  have fields := reconstruct_fields related
  obtain ⟨base,named,decoded⟩ := fields.node present
  obtain ⟨raw,read,pointerOk⟩ := (decodeNode_fields decoded).peer
  have pointerEq := (pointer_value fields.peerIds (by simpa using word_bound read) pointerOk).1
  change (AllowedipsRelation.pointer (interpretation names.peers) node.peer).toNat=raw at pointerEq
  rw [pointerEq,interpretation_of_mem fields.nodeIds named]
  have offset := fields.layout.2.1
  change o.peer=0 at offset
  simpa only [offset,Nat.add_zero] using word_loadInt _ _ _ _ _ read

theorem hit_segment (fetch : Int64 → Option Decoded)
    (decoder : AllowedipsDecoderAgreement fetch) (peerDecoder : AnchoredDecoderAgreement fetch)
    (pc : AllowedipsTracePcContract fetch) (cmp4 : AllowedipsTraceConstCmp4Contract fetch)
    (cmp1 : AllowedipsTraceConstCmp1Contract fetch)
    {names} {input : AllowedipsProbe.Input} {coverage initial entry state w d root bits key ra id node pid peer}
    (pre : AllowedipsEntry (callConfig names w d root bits key) coverage.coverage coverage.preempt ra initial w
      (callView (callConfig names w d root bits key) d))
    (facts : CallFacts names input.offsets coverage initial ra bits key)
    (post : AllowedipsEntry.Post (callConfig names w d root bits key) initial coverage.coverage coverage.preempt ra entry)
    (atCut : state.pc=AllowedipsImage.Lookup.entry+0x110)
    (frame : AllowedipsLoop.Frame entry.data ⟨coverage.coverage,coverage.preempt+512⟩ state.data)
    (related : Corresponds names input.offsets state.data.dmem d)
    (selected : AllowedipsSource.select (fun id => d.nodes.get? id) root bits key=some (some id))
    (nodePresent : d.nodes.get? id=some node) (word : node.peer=some pid)
    (peerPresent : d.peers.get? pid=some peer) (nonzero : peer.refcount≠0) (bound : peer.refcount+1<2^31)
    (cursor : state.data.regs.rbp.toBitVec=interpretation names.nodes id) :
    Eventually (instructionStep fetch)
      (MiddlePost names input.offsets {d with peers := d.peers.insert pid {peer with refcount := peer.refcount+1}}
        (callConfig names w d root bits key) (callView (callConfig names w d root bits key) d)
        coverage initial entry (some pid)) state := by
  let cfg := callConfig names w d root bits key
  let during : Context := ⟨coverage.coverage,coverage.preempt+512⟩
  have focus : cfg.focus.peer=some pid := by simp only [cfg,callConfig,selected,Option.join_some,Option.bind_some,nodePresent,word]
  have countView : (callView cfg d).count=some peer.refcount := by simp only [callView,focus,Option.bind_some,peerPresent,Option.map_some]
  have ready := ready_from_loop pre post frame
  obtain ⟨nonnull,countRead⟩ := count_from_loop pre post frame pid peer.refcount focus countView
  obtain ⟨countStack,countServices⟩ := count_separate pre post frame pid peer.refcount focus countView nonzero
  have nodeRead := reconstructed_node_peer related nodePresent
  rw [word] at nodeRead
  have nodePeer : state.data.dmem.loadInt state.data.regs.rbp.toBitVec 8=
      some ((interpretation names.peers pid).toNat : Int) := by rw [cursor]; exact nodeRead
  let count : UInt32 := UInt32.ofNat peer.refcount
  have countNat : count.toNat=peer.refcount := by
    change peer.refcount%2^32=peer.refcount
    exact Nat.mod_eq_of_lt (by omega)
  have positive : count≠0 := by intro zero; have equal := congrArg UInt32.toNat zero; rw [countNat] at equal; exact nonzero equal
  have run := peer_effect fetch decoder peerDecoder pc cmp4 cmp1 state.data (interpretation names.peers pid)
    during ready nonnull nodePeer count positive (by rw [countNat]; exact bound)
    (by rw [countNat]; exact countRead) countStack countServices
  have start : (⟨state.data,AllowedipsImage.Lookup.entry+0x110⟩ : MachineState)=state := by rw [←atCut]
  rw [←start]
  have fields := reconstruct_fields related
  obtain ⟨base,named,_⟩ := fields.peer peerPresent
  have countAddress : BitVec.ofNat 64 (base+input.offsets.peerRefcount)=interpretation names.peers pid+0x420 := by
    rw [interpretation_of_mem fields.peerIds named,fields.layout.2.2.2.2.2.2.2.2,BitVec.ofNat_add]
    rfl
  have scratchTotal {a : BitVec 64} (scratch : Scratch state.data a) : AllowedipsStackWrites initial a := by
    change InRange (state.data.regs.rsp.toBitVec-64) 64 a at scratch
    rw [scratch_entry post frame] at scratch
    obtain ⟨i,hi,equal⟩ := scratch
    exact ⟨i,by omega,equal⟩
  have apart := spansApart_disjoint facts.decoderApart
    (show Covers (decoderSpans names input.offsets) (ReadBytes names input.offsets) from fun _ read => decoderSpans_cover read)
    (callTotalWrites_cover initial coverage)
  have countApart := spansApart_disjoint facts.countApart (countSpans_cover names input.offsets)
    (trieSpans_cover names input.offsets).append_right
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro final ⟨position,stack,result,active,changed,memory,mapped⟩
  have reconstructed := reconstruct_peer_frame (after := final.data.dmem) (count := peer.refcount+1) related peerPresent named
    (fun a => Scratch state.data a ∨ during.writes a)
    (by intro a outside; exact memory a (by simpa only [peerWrites,←countAddress] using outside))
    (by
      intro a read written
      rcases written with scratch | buffer
      · exact apart a read (.inl (scratchTotal scratch))
      · exact apart a read (.inr (.inl ⟨.inr buffer.1,buffer.2⟩)))
    (by
      intro a read inside
      exact countApart a ⟨pid,base,named,inside⟩ read)
    (by rw [countAddress]; simpa only [countNat] using changed)
  refine ⟨position,result,reconstructed,stack.trans (frame.stack.trans post.stack),active,mapped,?_⟩
  intro a outside
  apply (frame.memory a (fun written => outside (loopWrites_middle post written))).trans
  apply memory a
  rintro (count | scratch | buffer)
  · exact outside (.inr (.inr ⟨pid,peer.refcount,focus,countView,nonzero,count⟩))
  · apply outside (.inl ?_)
    change InRange (state.data.regs.rsp.toBitVec-64) 64 a at scratch
    rw [scratch_entry post frame] at scratch
    exact scratch
  · exact outside (.inr (.inl buffer))

#print axioms hit_segment
end Binary.Pair.Trie
