import TrustBase

namespace Binary
open TrustBase

/-- Physical frames at anchored cuts. Service interiors are deliberately
    absent: their named contracts only frame returns and exclude reentry. -/
def CutFrames (writes : Address → Prop) (initial : Mem 64)
    (history : List MachineState) : Prop :=
  ∀ q ∈ history, q.pc ∈ Image.cutPoints → EqualOutside writes initial q.data.dmem

theorem CutFrames.mono {small large : Address → Prop} {initial : Mem 64}
    {history : List MachineState} (frames : CutFrames small initial history)
    (subset : ∀ a, small a → large a) : CutFrames large initial history := by
  intro q member cut a outside
  exact frames q member cut a (fun written => outside (subset a written))

theorem CutFrames.append_after {writes localWrites : Address → Prop}
    {initial base : Mem 64} {history tail : List MachineState}
    (frames : CutFrames writes initial history)
    (endpoint : EqualOutside writes initial base)
    (extension : CutFrames localWrites base tail)
    (subset : ∀ a, localWrites a → writes a) :
    CutFrames writes initial (history ++ tail) := by
  intro q member cut
  rcases List.mem_append.mp member with old | new
  · exact frames q old cut
  · intro a outside
    exact (endpoint a outside).trans
      (extension q new cut a (fun written => outside (subset a written)))

theorem CutFrames.initial (writes : Address → Prop) (s : MachineState) :
    CutFrames writes s.data.dmem [s] := by
  intro q member _
  have eq : q = s := by simpa using member
  subst q
  intro _ _
  rfl

end Binary
