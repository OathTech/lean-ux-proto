import C1BelowPrefixParent
import C1BelowPrefixRegions

/-! Result C1, work package 3, prefix: the invariant carried from the save at
`add+0x241` to the comparison at `add+0x267`, and its preservation by a step
whose writes stay inside `Late` and off the two saved stack words. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage
open Binary.Pair.Allowedips.Root Binary.Pair.Allowedips.ChildFinish
local instance : Labels := Image.linkedLabels

/-- What holds from `add+0x246` on: the callee-saved registers of the cut
(with `rbp` and `r14` as the first initialization left them), callback
readiness, the frame since the first initialization, the pending fresh node,
and the two saved stack words (the node below at `rsp`, the fresh node at
`rsp+24`). -/
structure Held (names : Allowedips.Names) (c : Context) (e : MachineData) (d : Device)
    (key cidr pid base child : Nat) (m : DataMem) (t : MachineData) : Prop where
  stack : t.regs.rsp=e.regs.rsp
  bx : t.regs.rbx=e.regs.rbx
  r12 : t.regs.r12=e.regs.r12
  r15 : t.regs.r15=e.regs.r15
  bp : t.regs.rbp=UInt64.ofNat (e.regs.rbp.toNat/8)
  r14 : t.regs.r14=UInt64.ofNat (base+32)
  ready : CallsReady c t
  late : EqualOutside (Late e.regs.rsp c) m t.dmem
  mapped : MappedLe e.dmem t.dmem
  pending : NodeInit.Pending names e d key cidr pid base t.dmem
  query : AllowedipsChild.QueryWords t.dmem e.regs.r13.toBitVec e.regs.rbp.toNat key
  down : t.dmem.loadInt e.regs.rsp.toBitVec 8=some (child : Int)
  saved : t.dmem.loadInt (e.regs.rsp.toBitVec+24) 8=some (base : Int)

theorem writes_bytes {c : Context} {a : BitVec 64} (written : c.writes a) : c.bytes a :=
  .inr (.inr ⟨written.1,.inr written.2⟩)

/-- One step of the prefix after the save: registers kept, readiness
re-established, writes inside `W`, which lies in `Late` and off the saved
fresh-node word; the saved word of the node below is shown kept separately
(the helper's frame includes it in its footprint but does not write it). -/
theorem Held.step {names : Allowedips.Names} {c : Context} {e : MachineData} {d : Device}
    {key cidr pid base child : Nat} {m : DataMem} {t u : MachineData}
    (held : Held names c e d key cidr pid base child m t) (res : Res names c e base)
    (family : e.regs.rbp.toNat=32 ∨ e.regs.rbp.toNat=128)
    (W : BitVec 64 → Prop)
    (stack : u.regs.rsp=t.regs.rsp) (bx : u.regs.rbx=t.regs.rbx) (r12 : u.regs.r12=t.regs.r12)
    (r15 : u.regs.r15=t.regs.r15) (bp : u.regs.rbp=t.regs.rbp) (r14 : u.regs.r14=t.regs.r14)
    (ready : CallsReady c u) (mapped : MappedLe t.dmem u.dmem)
    (frame : EqualOutside W t.dmem u.dmem)
    (inside : ∀ a, W a → Late e.regs.rsp c a)
    (slot : ∀ a, InRange (e.regs.rsp.toBitVec+24) 8 a → ¬W a)
    (top : u.dmem.loadInt e.regs.rsp.toBitVec 8=t.dmem.loadInt e.regs.rsp.toBitVec 8) :
    Held names c e d key cidr pid base child m u := by
  have lateStep : EqualOutside (Late e.regs.rsp c) t.dmem u.dmem :=
    fun a outside => frame a (fun w => outside (inside a w))
  exact {
    stack := stack.trans held.stack
    bx := bx.trans held.bx
    r12 := r12.trans held.r12
    r15 := r15.trans held.r15
    bp := bp.trans held.bp
    r14 := r14.trans held.r14
    ready := ready
    late := fun a outside => (held.late a outside).trans (lateStep a outside)
    mapped := fun address size h => mapped _ _ (held.mapped _ _ h)
    pending := held.pending.frame lateStep
      (fun span member x within late => res.projection span member x within (late_after late))
      (fun x within late => res.table x within (late_after late))
    query := AllowedipsLoop.query_frame family held.query lateStep
      (fun x within late => res.query x within (late_after late))
    down := top.trans held.down
    saved := by
      rw [←frame.loadInt (e.regs.rsp.toBitVec+24) 8 (fun i bound => slot _ ⟨i,bound,rfl⟩)]
      exact held.saved }

/-- A callback's footprint (its return word and the coverage buffer) lies in
`Late` and off both saved words. -/
theorem call_late {stack : UInt64} {c : Context} {a : BitVec 64}
    (written : InRange (stack.toBitVec-8) 8 a ∨ c.writes a) : Late stack c a :=
  written.elim late_word (fun buffer => .inr (.inr buffer))

theorem call_slot {names : Allowedips.Names} {c : Context} {e : MachineData} {base : Nat}
    (res : Res names c e base) {offset : Nat} (within : offset+8≤48) {a : BitVec 64}
    (inside : InRange (e.regs.rsp.toBitVec+.ofNat 64 offset) 8 a) :
    ¬(InRange (e.regs.rsp.toBitVec-8) 8 a ∨ c.writes a) := by
  rintro (word|buffer)
  · obtain ⟨i,bound,location⟩ := inside
    obtain ⟨j,boundJ,locationJ⟩ := word
    rw [location] at locationJ
    bv_omega
  · exact res.context a (writes_bytes buffer) (zone_local within inside)

#print axioms Held.step
end Binary.Statements.C1.Proof
