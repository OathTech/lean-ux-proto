import C1BelowWholeParent
import C1BelowWholeRoot
import C1BelowTrunk

/-! Result C1, work package 3: THE SPLIT PATH (case `split`: an intermediate
node, two allocations, at the root and below a parent), from the cut with
`CutExtra` to the common exit, and as a whole path from the strengthened
trunk. Composition: `prefix_compared` (cut to the comparison),
`split_allocated` (the second allocation, `AllocRule` and `NodeBelowTop`),
`SplitCtx.connect` (the internal node's initialization and the choice
against the node below), `SplitCtx.parent_exit` / `SplitCtx.root_exit` (the
connections, the relation and `heap` for `step`'s device, `AtExit`). -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem split_from_cut (below : NodeBelowTop) (alloc : AllocRule) {fetch : Int64 → Option Decoded}
    {L : Layout} {A : Allocator} (premises : Premises fetch L A)
    {c : Context} {s : MachineState} {w w' : World} {family key cidr pid : Nat} {ra : UInt64}
    {answer : Int} {d : Device} {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool}
    {st : Step} {names : Allowedips.Names} {base : Nat} {e : MachineState}
    (inv : Inv L A w s.data.dmem)
    (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .split)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family) :
    Eventually (instructionStep fetch) (AtExit L A c s e w' answer) e := by
  have rfacts := ready_facts ready
  obtain ⟨downId,downNode,m,hasBelow,hasDown,summary,run⟩ :=
    prefix_compared premises ready facts (.inr (.inl case)) cut extra
  obtain ⟨zero,fits,⟨first,second,rest,shape,site,success,dropped⟩,shorterAll⟩ := split_source facts case
  have shorter := shorterAll downId downNode hasBelow hasDown
  obtain ⟨_,_,_,_,inverted⟩ := step_below facts.model (.inr (.inl case))
  have inexact := inverted.inexact
  have walked := (facts.walked (by rw [case]; decide) (by rw [case]; decide) (by rw [case]; decide)).2
  rw [inexact] at walked
  have downWidth := walk_down walked hasBelow hasDown
  have wide : widthOf family = 32 ∨ widthOf family = 128 := by
    have fam := (NodeInit.boundary_fields cut.boundary).family
    rw [extra.width] at fam
    exact fam
  have cidrSmall : cidr < 256 := by rcases wide with h|h <;> omega
  have arena : ∀ node ∈ liveOf names base, InArena L node := by
    intro node member
    rcases List.mem_append.mp member with old|new
    · obtain ⟨pair,named,rfl⟩ := List.mem_map.mp old
      exact cut.arena pair named
    · cases List.mem_singleton.mp new
      exact cut.fresh
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro a ⟨child,_,named,cmp,ac⟩
  have stackA : a.data.regs.rsp.toNat = e.data.regs.rsp.toNat := by rw [cmp.held.stack]
  have high := extra.frameHigh
  have low := extra.frameLow
  apply eventually_trans (instructionStep fetch) _ _ _
    (split_allocated below alloc premises (BitVec.ofNat 8 cidr) (BitVec.ofNat 64 base) ready cut.apart arena
      cmp.pc ac.flight (by omega) (by omega) cmp.held.ready ac.cidrByte ac.baseWord
      (by rw [cmp.common,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; exact shorter)
      site success (by
        have idle := ac.idle
        rw [shape] at idle
        exact idle))
  rintro t ⟨base2,grown⟩
  have x : SplitCtx fetch L A c s ra w d family key cidr pid stream placed names base e a t m downId child
      downNode rest base2 :=
    ⟨rfacts,cut,extra,summary,named,hasDown,cmp,ac,grown,fits,shorter,facts.keyBound,downWidth⟩
  apply eventually_trans (instructionStep fetch) _ _ _ (x.connect premises)
  intro u k
  cases placed with
  | none => exact x.root_exit k premises inv facts case dropped zero hasBelow
  | some p => exact x.parent_exit k premises inv facts case dropped zero hasBelow

/-- PACKAGE 3, case `split`, from the trunk that hands over `CutExtra`
beside `NodeCut` (`TrunkToNodePlus`). `PathSplit` itself, from
`TrunkToNode`, is not provable: `NodeCut` lacks the facts of `CutExtra`. -/
theorem pathSplit_plus : NodeBelowTop → AllocRule → TrunkToNodePlus → Path .split :=
  fun below alloc trunk => path_of_segment_plus (.inr (.inl rfl)) trunk
    (fun _ _ _ premises _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv ready _ facts case cut extra =>
      split_from_cut below alloc premises inv ready facts case cut extra)

#print axioms split_from_cut
#print axioms pathSplit_plus
end Binary.Statements.C1.Proof
