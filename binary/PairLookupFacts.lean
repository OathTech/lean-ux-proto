import SourceAdapter
import PairLookupFootprint
import PairLookupCoverage

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase LookupRelation CommonBitsCoverage Index
set_option maxRecDepth 2048

theorem outputNeeded_iff (v : View) : outputNeeded v=true ↔ LookupOutputNeeded v := by
  unfold outputNeeded LookupOutputNeeded
  cases count : v.count with
  | none => simp
  | some number => simp only [Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq,Option.some.injEq,exists_eq_left']

structure CallFacts (n : Names) (o : Offsets) (coverage : Context) (s : MachineState)
    (w : World) (d : Device) (query : Nat) (kinds : List IndexKind) (ra : UInt64) : Prop where
  device : w.wg.dev=some d
  related : Corresponds n o s.data.dmem d
  storage : storageCheck n o=true
  owners : Remove.ownership n o s.data.dmem=.ok (Remove.targetOwnership d)
  names : interpretationCheck n=true
  pc : s.pc=Image.Lookup.entry
  table : s.data.regs.rdi.toBitVec=(callConfig n w d query kinds).table
  queryAt : (s.data.regs.get (.low .rdx .W32)).toNat=query
  kindsAt : KindMask (s.data.regs.get (.low .rsi .W32)) kinds
  frame : Index.CallFacts n o coverage s ra (LookupStackWords (callConfig n w d query kinds))
  shapeApart : spansApart (ownerSpans n ++ countSpans n o) (shapeSpans n o)=true
  countApart : spansApart (ownerSpans n) (countSpans n o)=true
  outputMapped : LookupOutputNeeded (callView (callConfig n w d query kinds) d) →
    (s.data.dmem.loadInt s.data.regs.rcx.toBitVec 8).isSome=true
  outputApart : LookupOutputNeeded (callView (callConfig n w d query kinds) d) →
    spansApart (outputSpan s) (storageSpans n o ++
      Index.callStack s (LookupStackWords (callConfig n w d query kinds)) true ++ Trie.callServices coverage)=true

theorem pre_facts {n o coverage s w query kinds ra} (checked : Pre n o coverage s w query kinds ra) :
    ∃ d, CallFacts n o coverage s w d query kinds ra := by
  unfold Pre callBoundary at checked
  obtain ⟨_,asserted,checked⟩ := bind_ok checked
  obtain ⟨d,device,related,storage,owned⟩ := remove_assert_ok asserted
  obtain ⟨names,checked⟩ := check_ok _ _ _ _ checked
  rw [device] at checked
  obtain ⟨arguments,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,frame,checked⟩ := bind_ok checked
  obtain ⟨separated,checked⟩ := check_ok _ _ _ _ checked
  have args : s.pc=Image.Lookup.entry ∧ s.data.regs.rdi.toBitVec=(callConfig n w d query kinds).table ∧
      (s.data.regs.get (.low .rdx .W32)).toNat=query ∧
      decide (s.data.regs.get (.low .rsi .W32) &&& kindWord .handshake≠0)=kinds.contains .handshake ∧
      decide (s.data.regs.get (.low .rsi .W32) &&& kindWord .keypair≠0)=kinds.contains .keypair := by
    simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using arguments
  have apart : spansApart (ownerSpans n ++ countSpans n o) (shapeSpans n o)=true ∧
      spansApart (ownerSpans n) (countSpans n o)=true := by simpa only [Bool.and_eq_true] using separated
  refine ⟨d,device,related,storage,owned,names,args.1,args.2.1,args.2.2.1,?_,
    Index.callFrameCheck_sound frame,apart.1,apart.2,?_,?_⟩
  · intro kind
    cases kind
    · exact args.2.2.2.1
    · exact args.2.2.2.2
  all_goals intro needed
  all_goals rw [ite_eq_left ((outputNeeded_iff _).mpr needed)] at checked
  all_goals obtain ⟨mapped,checked⟩ := check_ok _ _ _ _ checked
  · exact mapped
  · exact (check_ok _ _ _ _ checked).1

#print axioms pre_facts
end Binary.Pair.IndexLookup
