import C1BelowPrefixRoot
import C1BelowPrefixRes
import C1BelowPrefixCase
import C1BelowReady

/-! Result C1, work package 3: the prefix shared by the three paths below the
placement, from the cut `add+0x156` to the comparison after `common_bits`
at `add+0x267`, from `NodeCut`, the caller's conditions, the step facts and
`CutExtra` (what `NodeCut` does not give; see `C1Cut`). -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root
local instance : Labels := Image.linkedLabels

/-- The machine part of the prefix: the state at `add+0x267`, for the node
`downId` below the placement. -/
theorem prefix_machine {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (premises : Premises fetch L A)
    {c : Context} {s : MachineState} {w w' : World} {family key cidr pid : Nat} {ra : UInt64}
    {answer : Int} {d : Device} {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool}
    {st : Step} {names : Allowedips.Names} {base : Nat} {e : MachineState}
    (ready : insertReady L A c s family key cidr pid ra=.ok ())
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .cover ∨ st.case = .split ∨ st.case = .splitNoMem)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family) :
    ∃ downId downNode m,
      below (bump d) (rootOf d family) key placed=some downId ∧
      (bump d).nodes.get? downId=some downNode ∧
      NodeInit.effect e.data=.ok (m,base) ∧
      Res names c e.data base ∧
      Eventually (instructionStep fetch) (fun t => ∃ child, child≠0 ∧ (downId,child) ∈ names.trie.nodes ∧
        Compared names c e.data (bump d) key cidr pid base child (widthOf family) downNode.bits m t) e := by
  have rfacts := ready_facts ready
  have res := resources rfacts cut extra
  have fields := NodeInit.boundary_fields cut.boundary
  obtain ⟨actual,deviceAt,related,heapOk⟩ := assertAt_ok fields.asserted
  have device : (bumped w d).wg.dev=some (bump d) := rfl
  have equal : actual=bump d := Option.some.inj (deviceAt.symm.trans device)
  subst actual
  obtain ⟨within,inexact,rootId,downId,down,rooted,lower,present⟩ := case_below facts.model case
  subst inexact
  have walked := (facts.walked (by rcases case with h|h|h <;> rw [h] <;> decide)
    (by rcases case with h|h|h <;> rw [h] <;> decide)
    (by rcases case with h|h|h <;> rw [h] <;> decide)).2
  rw [rooted] at walked
  have downWidth : down.bitlen=e.data.regs.rbp.toNat := (walk_down walked lower present).trans extra.width.symm
  have keyBound : key<2^e.data.regs.rbp.toNat := by rw [extra.width]; exact facts.keyBound
  have downOld : downId≠names.nextNode := by
    have member : (downId,down) ∈ (Allowedips.target (bump d)).nodes :=
      Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present
    have below := target_nodes_below related _ member
    have counter : (bump d).nextNode=names.nextNode := (reconstruct_fields related).nextNode
    change downId<(bump d).nextNode at below
    exact Nat.ne_of_lt (counter ▸ below)
  have selected : ∃ m, NodeInit.effect e.data=.ok (m,base) ∧
      Eventually (instructionStep fetch) (Selected names c e.data (bump d) key cidr pid base downId m) e := by
    cases placed with
    | none =>
      have same : rootId=downId := by simpa [below] using lower
      subst same
      have zero : e.data.regs.rbx=0 := by
        have at0 := cut.placedAt
        have nat : e.data.regs.rbx.toNat=0 := (Except.ok.inj at0).symm
        exact UInt64.toNat_inj.mp nat
      have full := reconstruct_fields related
      rcases facts.families with four|six
      · have slotWord := extra.slot
        simp only [four,ite_true] at slotWord
        rw [←cut.table] at slotWord
        obtain ⟨raw,rootRead,pointer⟩ := full.root4
        have root : (Allowedips.target (bump d)).table.root4=some rootId := by
          have h := rooted
          simp only [rootOf,four,beq_self_eq_true,ite_true] at h
          exact h
        rw [root] at pointer
        have bound : names.table+AllowedipsMutationLayout.root4<2^64 := by
          unfold word at rootRead
          split at rootRead
          · omega
          · cases rootRead
        exact selected_root fetch premises.insertion premises.tracePc c cut.boundary device res cut.calls zero
          slotWord bound ⟨raw,_,rootRead,pointer⟩ (by decide)
      · have slotWord := extra.slot
        simp only [six,show ¬(6=4) from by decide,ite_false] at slotWord
        rw [←cut.table] at slotWord
        obtain ⟨raw,rootRead,pointer⟩ := full.root6
        have root : (Allowedips.target (bump d)).table.root6=some rootId := by
          have h := rooted
          simp only [rootOf,six,show (6==4)=false from rfl,Bool.false_eq_true,ite_false] at h
          exact h
        rw [root] at pointer
        have bound : names.table+AllowedipsMutationLayout.root6<2^64 := by
          unfold word at rootRead
          split at rootRead
          · omega
          · cases rootRead
        exact selected_root fetch premises.insertion premises.tracePc c cut.boundary device res cut.calls zero
          slotWord bound ⟨raw,_,rootRead,pointer⟩ (by decide)
    | some p =>
      obtain ⟨pn,hasParent,width,short,occupied⟩ := walk_parent walked lower
      have parentNamed : (p,e.data.regs.rbx.toNat) ∈ names.trie.nodes := by
        have at0 := cut.placedAt
        unfold Trie.address at at0
        simp only [] at at0
        cases found : names.trie.nodes.find? (·.1 == p) with
        | none => rw [found] at at0; cases at0
        | some pair =>
          rw [found] at at0
          have member := List.mem_of_find?_eq_some found
          have matched : (pair.1 == p)=true := List.find?_some (p := fun x : Nat × Nat => x.1 == p) found
          have same : pair.1=p := eq_of_beq matched
          have address : pair.2=e.data.regs.rbx.toNat := Except.ok.inj at0
          rw [←same,←address]
          exact member
      exact selected_parent fetch premises.insertion premises.tracePc c cut.boundary device res cut.calls
        parentNamed hasParent (extra.width.trans width.symm) (by omega) occupied downOld
  obtain ⟨m,summary,run⟩ := selected
  refine ⟨downId,down,m,by rw [rooted]; exact lower,present,summary,res,?_⟩
  apply eventually_trans (instructionStep fetch) _ _ _ run
  intro t sel
  obtain ⟨child,nonzero,named,next⟩ := compared fetch premises.insertion premises.lookup premises.callbacks
    premises.tracePc premises.cmp1 c fields related res present downWidth keyBound sel
  apply eventually_weaken (instructionStep fetch) _ _ _ _ next
  intro y reached
  exact ⟨child,nonzero,named,extra.width ▸ reached⟩

#print axioms prefix_machine
end Binary.Statements.C1.Proof
