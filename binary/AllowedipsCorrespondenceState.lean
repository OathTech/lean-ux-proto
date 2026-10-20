import SourceAdapter
import AllowedipsRelation
import AllowedipsSourceSelected
import LookupRelation
import PeerPhaseSchedule

namespace Binary.AllowedipsRelation
open Leanux Leanux.WG LookupObservation

theorem project_kernel (c : Config) (before after : World) (same : after.wg = before.wg) :
    project c after = project c before := by simp only [project,same]

/-- Before peer acquisition, an actually neutral raw scanner makes the
semantic helper-activity guard irrelevant. Common-bits calls do not mutate it. -/
theorem countPhase_none (raw : List MachineState) (seen : List LookupObservation.Point)
    (neutral : PeerCountPhase.scan none raw = none) :
    LookupRelation.countPhase raw seen = none := by
  simp only [LookupRelation.countPhase,neutral]
  split <;> rfl

theorem countPhase_stable {raw nextRaw : List MachineState}
    (stable : PeerCountPhase.StableExtension raw nextRaw)
    (neutral : PeerCountPhase.scan none raw = none)
    (seen nextSeen : List LookupObservation.Point) :
    LookupRelation.countPhase nextRaw nextSeen = LookupRelation.countPhase raw seen := by
  rw [countPhase_none raw seen neutral]
  exact countPhase_none nextRaw nextSeen ((stable.final none).trans neutral)

/-- Source-only framing and the actual instruction footprint transport the
minimal relation. Count phase equality is supplied by the executed history. -/
theorem R.frame_kernel (c : Config) (raw nextRaw : List MachineState)
    (seen nextSeen : List LookupObservation.Point) (s t : MachineState) (w next : World)
    (related : R c raw seen s w) (sameKernel : next.wg = w.wg)
    (last : nextRaw.getLast? = some t)
    (phase : LookupRelation.countPhase nextRaw nextSeen = LookupRelation.countPhase raw seen)
    (writes : Address → Prop) (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ v, project c w = some v → ∀ a, Reads c v a → ¬writes a)
    (steps : StepsAt c nextSeen next) : R c nextRaw nextSeen t next := by
  obtain ⟨_,⟨v,projected,physical⟩,_⟩ := related
  exact ⟨last,⟨v,(project_kernel c w next sameKernel).trans projected,
    physical.frame c raw nextRaw seen nextSeen s t v phase writes frame (apart v projected)⟩,steps⟩

/-- Physical trie fields frame independently of the focused count. This is
used at actual helper cuts, where a proved phase/count equation replaces the
single possibly changed field. No unchanged-refcount assumption is needed. -/
theorem Physical.frame_count (c : Config) (raw nextRaw : List MachineState)
    (seen nextSeen : List LookupObservation.Point) (s t : MachineState) (v next : View)
    (physical : Physical c raw seen s v) (nodes : next.nodes = v.nodes)
    (writes : Address → Prop) (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ a, TrieReads c.nodes v.nodes c.root c.bits c.key a → ¬writes a)
    (count : match c.focus.peer with
      | none => next.count = none
      | some pid => ∃ n, next.count = some n ∧ c.peers pid ≠ 0 ∧
          PeerCountPhase.At (LookupRelation.countPhase nextRaw nextSeen) t.data.dmem
            (c.peers pid + .ofNat 64 Layouts.peer_refcount) n) :
    Physical c nextRaw nextSeen t next := by
  refine ⟨?_,count⟩
  rw [nodes]
  exact physical.1.frame frame apart

/-- Combine the independently framed trie with the actual focused-count
phase equation at a semantic or stuttering cut. -/
theorem R.frame_count (c : Config) (raw nextRaw : List MachineState)
    (seen nextSeen : List LookupObservation.Point) (s t : MachineState) (w next : World)
    (related : R c raw seen s w) (last : nextRaw.getLast? = some t)
    (v nextView : View) (projected : project c w = some v)
    (nextProjected : project c next = some nextView) (nodes : nextView.nodes = v.nodes)
    (writes : Address → Prop) (frame : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ a, TrieReads c.nodes v.nodes c.root c.bits c.key a → ¬writes a)
    (count : match c.focus.peer with
      | none => nextView.count = none
      | some pid => ∃ n, nextView.count = some n ∧ c.peers pid ≠ 0 ∧
          PeerCountPhase.At (LookupRelation.countPhase nextRaw nextSeen) t.data.dmem
            (c.peers pid + .ofNat 64 Layouts.peer_refcount) n)
    (steps : StepsAt c nextSeen next) : R c nextRaw nextSeen t next := by
  obtain ⟨_,⟨old,oldProject,physical⟩,_⟩ := related
  have equal : old = v := Option.some.inj (oldProject.symm.trans projected)
  subst old
  exact ⟨last,⟨nextView,nextProjected,
    physical.frame_count c raw nextRaw seen nextSeen s t v nextView nodes writes frame apart count⟩,steps⟩

/-- The source Kernel is unchanged at every accepted search-prefix point.
This is a source theorem, not a physical prerequisite on untouched fields. -/
theorem search_prefix_project (c : Config) (world final : World) (answer : Option NodeId)
    (points : List MirrorHistory.Point)
    (accepted : ((AllowedipsSource.searchPrefix c.root c.bits c.key).run []).run world =
      .ok ((answer,points),final)) :
    project c final = project c world ∧ ∀ p ∈ points, project c p.world = project c world := by
  have frame := AllowedipsSource.frames_searchPrefix id c.root c.bits c.key world.wg [] world
    answer points final rfl (by intro p member; cases member) accepted
  exact ⟨project_kernel c world final frame.1,
    fun p member => project_kernel c world p.world (frame.2 p member)⟩

#print axioms R.frame_kernel
#print axioms Physical.frame_count
#print axioms search_prefix_project
end Binary.AllowedipsRelation
