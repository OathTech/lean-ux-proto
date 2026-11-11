import C1BelowCoverParent
import C1BelowCoverRootExit
import C1BelowTrunk

/-! Result C1, work package 3: THE COVERING PATH from the cut to the common
exit, both sub-cases (below a parent, at the root), and `Path .cover` from
the trunk strengthened with `CutExtra`.

`cover_from_cut` composes the prefix (`prefix_compared`, cut to the
comparison at `add+0x267`) with this file's segments (`cover_parent_exit`,
`cover_root_exit`: comparison to `add+0x549`, machine and data). Nothing is
assumed beyond `NodeCut`, `CutExtra`, the caller's conditions, `Inv` at
entry and `StepFacts`. `pathCover_plus` is `PathCoverPlus` (`C1Cut`): it
takes the strengthened trunk `TrunkToNodePlus`, because `NodeCut` lacks the
facts in `CutExtra`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- The covering path from the cut to the common exit. -/
theorem cover_from_cut {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator}
    (premises : Premises fetch L A)
    {c : Context} {s : MachineState} {w w' : World} {family key cidr pid : Nat} {ra : UInt64}
    {answer : Int} {d : Device} {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool}
    {st : Step} {names : Allowedips.Names} {base : Nat} {e : MachineState}
    (inv : Inv L A w s.data.dmem)
    (ready : insertReady L A c s family key cidr pid ra=.ok ())
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .cover)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family) :
    Eventually (instructionStep fetch) (AtExit L A c s e w' answer) e := by
  obtain ⟨downId,downNode,m,lower,present,summary,run⟩ :=
    prefix_compared premises ready facts (.inl case) cut extra
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro t ⟨child,_,named,comp,compared⟩
  cases placed with
  | none =>
    exact cover_root_exit premises inv ready facts case cut extra rfl lower present summary
      named comp compared
  | some p =>
    exact cover_parent_exit premises inv ready facts case cut extra rfl lower present summary
      named comp compared

/-- `Path .cover` from the strengthened trunk. -/
theorem pathCover_plus (trunk : TrunkToNodePlus) : Path .cover :=
  path_of_segment_plus (.inl rfl) trunk
    (fun _ _ _ premises _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv ready _ facts case cut extra =>
      cover_from_cut premises inv ready facts case cut extra)

#print axioms cover_from_cut
#print axioms pathCover_plus
end Binary.Statements.C1.Proof
