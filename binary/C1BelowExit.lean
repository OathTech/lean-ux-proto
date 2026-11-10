import C1Interfaces

/-! Result C1, work package 3: the two ends of a path below the placement.

A path of this package is the trunk (hypothesis `TrunkToNode`, to the cut at
`add+0x156`), a segment of its own from the cut to the common exit
`add+0x549`, and the cut's `Exits`. This file proves the composition once:
`path_of_segment` reduces `Path k` to the segment, whose target is `AtExit`.
It uses nothing of the cut but `seq` and `exits`, so it also checks that
`Exits` is enough to finish a path (it is). -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- What a segment from the cut `e` must establish at the common exit `x`:
the hypotheses of `Exits`, the answer in `ebx`, the invariant for the
mirror's final world, and the sequence word as the cut left it. -/
structure AtExit (L : Layout) (A : Allocator) (c : Context) (s e : MachineState) (w' : World)
    (answer : Int) (x : MachineState) : Prop where
  pc : x.pc = AllowedipsMutationImage.Add.entry + 0x549
  stack : x.data.regs.rsp = e.data.regs.rsp
  flight : InFlight L A c s x
  calls : CallsReady c x.data
  saved : ∀ a, InRange (e.data.regs.rsp.toBitVec + 48)
      (s.data.regs.rsp.toNat + 8 - (e.data.regs.rsp.toNat + 48)) a →
    x.data.dmem.get? a = e.data.dmem.get? a
  result : x.data.regs.get (.low .rbx .W32) = BitVec.ofInt 32 answer
  inv : Inv L A w' x.data.dmem
  seq : readNat x (L.table+AllowedipsMutationLayout.seq) 8 =
    readNat e (L.table+AllowedipsMutationLayout.seq) 8

/-- The sequence word is one of the layout's fixed words. -/
theorem seq_in_heap (L : Layout) (i : Nat) (bound : i < 8) :
    L.Heap (.ofNat 64 (L.table+AllowedipsMutationLayout.seq) + .ofNat 64 i) := by
  refine ⟨(L.table+AllowedipsMutationLayout.seq,8),?_,i,bound,rfl⟩
  apply List.mem_append_left
  apply List.mem_append_left
  simp [tableFields]

/-- A read of the sequence word sees only heap bytes. -/
theorem readNat_seq_congr (L : Layout) {x t : MachineState}
    (same : ∀ a, L.Heap a → t.data.dmem.get? a = x.data.dmem.get? a) :
    readNat t (L.table+AllowedipsMutationLayout.seq) 8 =
      readNat x (L.table+AllowedipsMutationLayout.seq) 8 := by
  have outside : EqualOutside (fun a => ¬L.Heap a) t.data.dmem x.data.dmem := by
    intro a notOutside
    exact same a (Classical.not_not.mp notOutside)
  unfold readNat
  rw [outside.loadBytes (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8
    (fun i bound h => h (seq_in_heap L i bound))]

/-- From the common exit to the caller: `Exits` and the cut's `seq` turn
`AtExit` into the conclusion of `InsertStep`. -/
theorem exit_post {fetch : Int64 → Option Decoded} {L : Layout} {A : Allocator} {c : Context}
    {s : MachineState} {ra : UInt64} {w w' : World} {d : Device} {key cidr pid : Nat}
    {stream : List HiddenRecord} {placed : Option NodeId} {names : Allowedips.Names} {base : Nat}
    {e x : MachineState} {answer : Int}
    (cut : NodeCut fetch L A c s ra w d key cidr pid stream placed names base e)
    (reached : AtExit L A c s e w' answer x) :
    Eventually (instructionStep fetch) (InsertPost L A c s w' ra answer) x := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (cut.exits x reached.pc reached.stack reached.flight reached.calls reached.saved)
  rintro t ⟨returned,eax,outside,heap,inv⟩
  refine ⟨returned,eax.trans reached.result,?_,inv w' reached.inv,?_⟩
  · obtain ⟨before,atEntry,atCut⟩ := cut.seq
    exact ⟨before,atEntry,by rw [readNat_seq_congr L heap,reached.seq]; exact atCut⟩
  · intro a unwritten
    exact (reached.flight.frame a unwritten).trans
      (outside a (fun h => unwritten (h.elim .inl (fun h => .inr (.inl h)))))

/-- A path below the placement is its segment from the cut to the common
exit: the trunk reaches the cut, the segment reaches `AtExit`, `Exits`
returns. -/
theorem path_of_segment {k : Case} (below : k = .cover ∨ k = .split ∨ k = .splitNoMem)
    (trunk : TrunkToNode)
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
        Eventually (instructionStep fetch) (AtExit L A c s e w' answer) e) : Path k := by
  intro fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
    inv ready accepted facts case
  apply eventually_trans (instructionStep fetch) _ _ _
    (trunk fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
      inv ready facts (case ▸ below))
  rintro e ⟨names,base,cut⟩
  apply eventually_trans (instructionStep fetch) _ _ _
    (segment fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st
      names base e inv ready accepted facts case cut)
  intro x reached
  exact exit_post cut reached

#print axioms path_of_segment
end Binary.Statements.C1.Proof
