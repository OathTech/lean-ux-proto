import C1BelowUndoPath
import C1BelowPrefixFinal
import C1BelowTrunk

/-! Result C1, work package 3: the rollback path (case `splitNoMem`) from
the cut, and the whole path from the strengthened trunk. `NodeCut` alone
does not suffice (see `CutExtra`); with `CutExtra` beside it the path
closes: `pathSplitNoMem_plus` has the interface's `PathSplitNoMem` with
`TrunkToNodePlus` in place of `TrunkToNode`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- The rollback path from the cut `add+0x156` to the common exit. -/
theorem rollback_from_cut (alloc : AllocRule) (free : FreeRule)
    {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} (premises : Premises fetch L A)
    {c : Context} {s : MachineState} {w w' : World} {family key cidr pid : Nat} {ra : UInt64}
    {answer : Int} {d : Device} {stream : List HiddenRecord} {placed : Option NodeId} {exact : Bool}
    {st : Step} {names : Allowedips.Names} {base : Nat} {e : MachineState}
    (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (inv : Inv L A w s.data.dmem)
    (facts : StepFacts w family key cidr pid answer w' d stream placed exact st)
    (case : st.case = .splitNoMem)
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (extra : CutExtra L s e family) :
    Eventually (instructionStep fetch) (AtExit L A c s e w' answer) e := by
  obtain ⟨downId,down,m,lower,present,summary,run⟩ :=
    prefix_compared premises ready facts (.inr (.inr case)) cut extra
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro t ⟨child,_,_,compared,reached⟩
  exact Undo.rollback_segment alloc free premises ready inv facts case cut extra.frameHigh extra.frameLow
    lower present compared.pc compared.held.stack reached.flight compared.held.ready reached.cidrByte
    reached.baseWord compared.common
    (by rw [compared.held.stack,compared.held.down]; rfl)
    reached.idle summary reached.heap reached.saved

/-- `PathSplitNoMem` with the trunk handing over `CutExtra` beside `NodeCut`. -/
theorem pathSplitNoMem_plus : AllocRule → FreeRule → TrunkToNodePlus → Path .splitNoMem :=
  fun alloc free trunk => path_of_segment_plus (.inr (.inr rfl)) trunk
    (fun _ _ _ premises _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ inv ready _ facts case cut extra =>
      rollback_from_cut alloc free premises ready inv facts case cut extra)

#print axioms rollback_from_cut
#print axioms pathSplitNoMem_plus
end Binary.Statements.C1.Proof
