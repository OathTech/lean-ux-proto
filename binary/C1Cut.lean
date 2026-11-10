import C1Interfaces

/-! Result C1, proof plan: the strengthened cut between packages 2 and 3, an
INTERNAL interface (not signed text, and no hypothesis of `Signed`).

`NodeCut` (`C1Interfaces`) does not determine the machine's behaviour from
`add+0x156`: package 3 found six facts about the cut state that the
instructions from there consume and `NodeCut` does not give. `CutExtra` is
that list and `TrunkToNodePlus` is `TrunkToNode` handing it over beside
`NodeCut`. Package 2 proves `TrunkToNodePlus`; package 3 proves its three
paths from it. The two packages each carried a verbatim copy of these
declarations on their branches; this module is their one home since the
integration. `trunk_of_plus` recovers the interface's `TrunkToNode`. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- WHAT `NodeCut` DOES NOT GIVE and the instructions from `add+0x156` to
`add+0x267` consume. None of these follows from `NodeCut`'s fields: its
`boundary` reads the stack only at `rsp+0` (8 bytes), `rsp+16` (4 bytes) and
the bytes `rsp+36/43/44`, relates `rbp` to nothing but `{32,128}`, and
separates the key bytes only from the first initialization's writes; its
`flight` bounds the stack pointer by `s.rsp - insertWindow ≤ e.rsp ≤ s.rsp`. -/
structure CutExtra (L : Layout) (s e : MachineState) (family : Nat) : Prop where
  /-- G1 (upper). `add`'s 48 bytes of locals lie below the caller's return
  word: needed for them to be mapped, to be scratch (`InsertWrites`) and to be
  apart from the heap and the coverage state. Consumed first by
  `mov %r8,0x18(%rsp)` at `add+0x1ff`. -/
  frameHigh : e.data.regs.rsp.toNat+48≤s.data.regs.rsp.toNat
  /-- G1 (lower). 48 bytes below the cut's stack pointer are still inside
  `insertWindow`: the callbacks' return words (`call` at `add+0x20d`, `+0x246`,
  `+0x262`) and `common_bits`' frame (`call` at `add+0x255`). `InFlight.low`
  allows `e.rsp = s.rsp - insertWindow`, which leaves no room when `A.depth = 0`. -/
  frameLow : s.data.regs.rsp.toNat+48≤e.data.regs.rsp.toNat+insertWindow
  /-- G4. `ebp` at the cut is the family's width (`boundary` only says 32 or
  128): the mirror's facts (`walk`, `ordered`) speak of `widthOf family`, the
  machine of `ebp`/`r15d`. Consumed by the selector (`add+0x212`) and by
  `common_bits`' third argument (`mov %r15d,%edx` at `add+0x252`). -/
  width : e.data.regs.rbp.toNat=widthOf family
  /-- G3. The key bytes at `r13` (host order, written by the wrapper into its
  own frame) lie inside the window above `add`'s locals: needed for their
  separation from the locals, the callbacks' return words, `common_bits`'
  frame and the coverage buffer. Consumed by `movzbl (%r13,%rax,1)` at
  `add+0x21f` and by `common_bits` (`mov %r13,%rsi` at `add+0x24f`). -/
  keyLow : e.data.regs.rsp.toNat+48≤e.data.regs.r13.toNat
  keyHigh : e.data.regs.r13.toNat+e.data.regs.rbp.toNat/8≤s.data.regs.rsp.toNat
  /-- G2 (root sub-case only). The stack word at `rsp+8` is the address of
  the family's root slot. Consumed by `mov 0x8(%rsp),%rax; mov (%rax),%rax`
  at `add+0x606` (and later by the root publications at `add+0x6c5`, `+0x722`). -/
  slot : e.data.dmem.loadInt (e.data.regs.rsp.toBitVec+8) 8=
    some ((L.table+(if family = 4 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6) : Nat) : Int)

/-- `TrunkToNode` with the facts about the cut state that `NodeCut` lacks. -/
def TrunkToNodePlus : Prop :=
  ∀ (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator), Premises fetch L A →
  ∀ (c : Context) (s : MachineState) (w w' : World) (family key cidr pid : Nat) (ra : UInt64)
    (answer : Int) (d : Device) (stream : List HiddenRecord) (placed : Option NodeId) (exact : Bool)
    (st : Step),
    Inv L A w s.data.dmem →
    insertReady L A c s family key cidr pid ra = .ok () →
    StepFacts w family key cidr pid answer w' d stream placed exact st →
    st.case = .cover ∨ st.case = .split ∨ st.case = .splitNoMem →
    Eventually (instructionStep fetch) (fun e => ∃ names base,
      NodeCut fetch L A c s ra w d key cidr pid stream placed names base e ∧
      CutExtra L s e family) s

/-- The strengthened trunk gives the interface's trunk. -/
theorem trunk_of_plus (trunk : TrunkToNodePlus) : TrunkToNode := by
  intro fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st inv ready facts case
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (trunk fetch L A premises c s w w' family key cidr pid ra answer d stream placed exact st inv ready facts case)
  rintro e ⟨names,base,cut,_⟩
  exact ⟨names,base,cut⟩

/-! ## What packages 2 and 3 deliver across the cut

The plus forms of `TrunkHolds`, `PathCover`, `PathSplit` and
`PathSplitNoMem` (`C1Interfaces`). `C1Assembly` consumes these four. Of the
original four, `TrunkHolds` follows by `trunk_of_plus`; the three paths from
the bare `TrunkToNode` are not proved by anyone and are not used. -/

/-- PACKAGE 2. The trunk to the cut in its strengthened form. -/
def TrunkPlusHolds : Prop := NodeBelowTop → FramedHolds → AllocRule → TrunkToNodePlus
/-- PACKAGE 3. Covering node, from the strengthened trunk. -/
def PathCoverPlus : Prop := TrunkToNodePlus → Path .cover
/-- PACKAGE 3. Intermediate node, from the strengthened trunk. -/
def PathSplitPlus : Prop := NodeBelowTop → AllocRule → TrunkToNodePlus → Path .split
/-- PACKAGE 3. The second allocation refused, from the strengthened trunk. -/
def PathSplitNoMemPlus : Prop := AllocRule → FreeRule → TrunkToNodePlus → Path .splitNoMem

end Binary.Statements.C1.Proof
