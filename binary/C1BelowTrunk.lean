import C1BelowPrefixCut

/-! Result C1, work package 3: the trunk hypothesis the three paths can
actually be proved from. `TrunkToNode` hands over `NodeCut`, which does not
determine the machine's behaviour from `add+0x156` (see `CutExtra` in
`C1BelowPrefixCut` for the six missing facts and the instruction that
consumes each). `TrunkToNodePlus` is `TrunkToNode` with `CutExtra` beside
`NodeCut` (both in `C1Cut` since the integration);
`path_of_segment_plus` is `path_of_segment` for it. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- A path below the placement is its segment from the cut, with `CutExtra`
available to the segment. -/
theorem path_of_segment_plus {k : Case} (below : k = .cover ∨ k = .split ∨ k = .splitNoMem)
    (trunk : TrunkToNodePlus)
    (segment : ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
      ∀ (c : Context) (s : MachineState) (w w' : World) (family key cidr pid : Nat) (ra : UInt64)
        (answer : Int) (d : Device) (stream : List HiddenRecord) (placed : Option NodeId) (exact : Bool)
        (st : Step) (names : Allowedips.Names) (base : Nat) (e : MachineState),
        Inv L A w s.data.dmem →
        insertReady L A c s family key cidr pid ra = .ok () →
        (liftWG (WG.insert family key cidr pid)).run w = .ok (answer, w') →
        StepFacts w family key cidr pid answer w' d stream placed exact st →
        st.case = k →
        NodeCut fetch L A c s ra w d key cidr pid stream placed names base e →
        CutExtra L s e family →
        Eventually (instructionStep fetch) (AtExit L A c s e w' answer) e) : Path k := by
  intro fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
    inv ready accepted facts case
  apply eventually_trans (instructionStep fetch) _ _ _
    (trunk fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
      inv ready facts (case ▸ below))
  rintro e ⟨names,base,cut,extra⟩
  apply eventually_trans (instructionStep fetch) _ _ _
    (segment fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
      names base e inv ready accepted facts case cut extra)
  intro x reached
  exact exit_post cut reached

#print axioms path_of_segment_plus
end Binary.Statements.C1.Proof
