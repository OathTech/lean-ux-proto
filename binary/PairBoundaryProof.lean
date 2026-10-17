import PairLocalsProof
import PairFrameProof
import PairTrieReadProof
import PairTrieLoop

namespace Binary.Pair.Trie
open Leanux Leanux.WG AllowedipsRelation
local instance : Labels := Image.linkedLabels

def loopConfig (names : Names) (w : World) (root : Option NodeId) (bits query : Nat) : Config :=
  ⟨root,bits,query,interpretation names.nodes,interpretation names.peers,⟨none,none⟩,
    w.steps.toList,w.netRxSection⟩

theorem loopWrites_cover {c : CommonBitsCoverage.Context} {s : MachineData} {a : BitVec 64}
    (write : AllowedipsLoop.writes s.regs.rsp c a) : ∃ span ∈ loopWrites c s, span.contains a := by
  rcases write with scratch | coverage
  · exact ⟨((s.regs.rsp.toBitVec-48).toNat,48),by simp [loopWrites],
      by simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using scratch⟩
  · obtain ⟨span,member,inside⟩ := writeSpans_cover coverage
    exact ⟨span,List.mem_append_right _ member,inside⟩

/-- All physical setup and initial invariant clauses are consequences of the
executable boundary assertion. Names are the sole pointer interpretation.
The only semantic inputs are the named decoder and callback contracts. -/
theorem boundary_ready (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp1 : TrustBase.AllowedipsTraceCmp1Contract fetch)
    (names : Names) (input : AllowedipsProbe.Input) (coverage : CommonBitsCoverage.Context)
    (s : MachineState) (w : World) (root : Option NodeId) (bits query : Nat)
    (checked : initialBoundary names input coverage s w root bits query = .ok ()) :
    ∃ d, w.k.wg = some d ∧
      AllowedipsLoop.Setup fetch s.data coverage (loopConfig names w root bits query) (fun id => d.nodes.get? id) ∧
      Corresponds names input.offsets s.data.dmem d ∧
      (∀ a, ReadBytes names input.offsets a → ¬AllowedipsLoop.writes s.data.regs.rsp coverage a) ∧
      Invariant names input.offsets d s.data coverage (loopConfig names w root bits query)
        (none,root,none) ⟨s,[s]⟩ := by
  unfold initialBoundary at checked
  obtain ⟨_,asserted,checked⟩ := bind_ok checked
  obtain ⟨_,inputOk,checked⟩ := bind_ok checked
  obtain ⟨_,localsOk,checked⟩ := bind_ok checked
  obtain ⟨header,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨frame,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨separation,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨querySeparation,_⟩ := check_ok _ _ _ _ checked
  obtain ⟨d,device,related,heapOk⟩ := assertAt_ok asserted
  have heap := trieHeap_of_checks related heapOk inputOk
  have locals := locals_fields heap.1 localsOk
  have apart : ∀ a, ReadBytes names input.offsets a → ¬AllowedipsLoop.writes s.data.regs.rsp coverage a := by
    intro a read write
    obtain ⟨l,hl,inside⟩ := decoderSpans_cover read
    obtain ⟨r,hr,atRight⟩ := loopWrites_cover write
    exact spansApart_sound separation hl hr inside atRight
  have queryApart : ∀ a, InRange (s.data.regs.rsp.toBitVec+16) (bits/8) a →
      ¬AllowedipsLoop.writes s.data.regs.rsp coverage a := by
    intro a read write
    obtain ⟨r,hr,atRight⟩ := loopWrites_cover write
    apply spansApart_sound querySeparation (l := ((s.data.regs.rsp.toBitVec+16).toNat,bits/8)) (by simp) hr ?_ atRight
    simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using read
  have header' : s.pc = AllowedipsImage.Lookup.entry+0xd5 ∧ root.isSome = true := by
    simpa only [Bool.and_eq_true,beq_iff_eq] using header
  refine ⟨d,device,⟨decoder,callbacks,cmp1,heap,
    fun a read => apart a (trieReads_decoded related read),locals.width,locals.family,locals.query,queryApart⟩,
    related,apart,?_,frameCheck_sound frame,related,⟨[],rfl⟩,rfl⟩
  refine ⟨locals.previous,?_⟩
  cases root with
  | none => cases header'.2
  | some id => exact ⟨header'.1,locals.cursor,.root id rfl⟩

/-- Sequential sibling over the actual mirror's findNode, starting at a
tested nonempty-loop boundary and ending before peer-get/BH-enable. Physical
setup is derived, not supplied as a second independent heap interpretation. -/
theorem findNode_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp1 : TrustBase.AllowedipsTraceCmp1Contract fetch)
    (names : Names) (input : AllowedipsProbe.Input) (coverage : CommonBitsCoverage.Context)
    (s : MachineState) (w final : World) (root : Option NodeId) (bits query : Nat) (answer : Option NodeId)
    (checked : initialBoundary names input coverage s w root bits query = .ok ())
    (accepted : (WG.findNode root bits query).run w = .ok (answer,final)) :
    Eventually (historyStep fetch) (fun t =>
      t.machine.pc = AllowedipsImage.Lookup.entry+0x101 ∧
      t.machine.data.regs.rbp.toBitVec = AllowedipsRelation.pointer (interpretation names.nodes) answer ∧
      (∃ d, final.k.wg = some d ∧ reconstruct names input.offsets t.machine.data.dmem = .ok (target d)) ∧
      AllowedipsLoop.Frame s.data coverage t.machine.data) ⟨s,[s]⟩ := by
  obtain ⟨d,device,setup,related,apart,initial⟩ :=
    boundary_ready fetch decoder callbacks cmp1 names input coverage s w root bits query checked
  have run := findNode_effect fetch names input.offsets d s.data coverage
    (loopConfig names w root bits query) setup related apart w final answer device accepted ⟨s,[s]⟩ initial
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro t ⟨pc,result,decoded,device,frame⟩
  exact ⟨pc,result,⟨d,device,decoded⟩,frame⟩

#print axioms boundary_ready
#print axioms findNode_checked
end Binary.Pair.Trie
