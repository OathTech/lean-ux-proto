import AllowedipsCorrespondenceCuts
import FiniteExecution

namespace Binary.AllowedipsRelation
open Leanux Leanux.WG TrustBase LookupObservation

/-- The complete physical write footprint of this invocation: real stack
    writes, conditional KCOV writes in either BH phase, the focused live
    count, and the actual preempt-count increment/decrement. -/
def AllowedipsWrites (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (entry : MachineState) (v : View) (a : Address) : Prop :=
  AllowedipsStackWrites entry a ∨ AllowedipsCoverageWrites coverage preempt a ∨
  AllowedipsCountWrites c v a ∨ InRange preemptCountAddress 4 a

/-- Both families' anchored cuts and the old peer-helper image are retained.
    Service interiors are excluded only by their proved no-reentry contracts;
    those contracts promise memory framing at return, not at internal PCs. -/
def AllowedipsCutFrames (writes : Address → Prop) (initial : Mem 64)
    (history : List MachineState) : Prop :=
  ∀ q ∈ history, (q.pc ∈ AllowedipsImage.cutPoints ∨ q.pc ∈ Image.cutPoints) →
    EqualOutside writes initial q.data.dmem

/-- The concrete M2 result includes the ABI return, complete accepted source
    run, exact emitting-prefix and all-cut correspondence, endpoint R, the
    physical frame, and the reusable service state. This predicate alone is
    not execution: the headline must establish it under historyStep. -/
def AllowedipsPost (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (ra : UInt64) (entry : MachineState) (world : World) (answer : Option PeerId)
    (finalWorld : World) (final : Executed) : Prop :=
  Returned entry final.machine ra ∧
  final.machine.data.regs.rax.toBitVec = pointer c.peers answer ∧
  ∃ v points source,
    AllowedipsEntry c coverage preempt ra entry world v ∧
    EqualOutside (AllowedipsWrites c coverage preempt entry v) entry.data.dmem final.machine.data.dmem ∧
    ((AllowedipsSource.lookup c.root c.bits c.key).run []).run world =
      .ok ((answer,source),finalWorld) ∧
    AllowedipsObservation.observe c.rxSection final.history = .ok points ∧
    MatchesPoints (AllowedipsCorrespondence.AtPoint (R c) c.rxSection final.history) points source ∧
    AllowedipsCorrespondence.CutsAligned (R c) c.rxSection final.history source ∧
    R c final.history points final.machine finalWorld ∧
    AllowedipsCutFrames (AllowedipsWrites c coverage preempt entry v) entry.data.dmem final.history ∧
    AllowedipsCoverageAt coverage preempt final.machine.data.dmem ∧
    load32 final.machine.data.dmem preemptCountAddress = some preempt ∧
    (LookupPendingRead preempt → final.machine.data.dmem.loadInt softirqPendingAddress 2 = some 0) ∧
    EndsAtReturn (AllowedipsImage.Lookup.entry+0x14e) final.history

/-- The same accepted full source run is realized for every transported
    property, including predicates inspecting intermediate source Worlds. -/
abbrev RealizesAllowedipsRun (c : Config) (final : Executed)
    (run : MirrorHistory.Run (Option PeerId)) : Prop :=
  AllowedipsCorrespondence.MatchesRun (R c) c.rxSection final run

theorem AllowedipsPost.realizes {c coverage preempt ra initial world answer finalWorld final}
    (post : AllowedipsPost c coverage preempt ra initial world answer finalWorld final) :
    ∃ run, run.result = answer ∧ run.finalWorld = finalWorld ∧
      MirrorHistory.Accepted (AllowedipsSource.lookup c.root c.bits c.key) world run ∧
      RealizesAllowedipsRun c final run := by
  obtain ⟨_,_,v,points,source,_,_,accepted,observed,matched,aligned,related,_⟩ := post
  exact ⟨⟨answer,finalWorld,source⟩,rfl,rfl,accepted,points,observed,matched,aligned,related⟩

/-- Untouched interpretations are transported through the proved write
    footprint, without adding their bytes to R or to the entry domain. -/
theorem AllowedipsPost.frame {c coverage preempt ra initial world answer finalWorld final}
    (post : AllowedipsPost c coverage preempt ra initial world answer finalWorld final)
    (F : Mem 64 → Prop) (initialFrame : F initial.data.dmem)
    (stable : ∀ v, AllowedipsEntry c coverage preempt ra initial world v →
      ∀ before after, EqualOutside (AllowedipsWrites c coverage preempt initial v) before after →
        F before → F after) : F final.machine.data.dmem := by
  obtain ⟨_,_,v,_,_,entry,frame,_⟩ := post
  exact stable v entry _ _ frame initialFrame

#print axioms AllowedipsPost.realizes
#print axioms AllowedipsPost.frame
end Binary.AllowedipsRelation
