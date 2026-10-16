import AllowedipsTailReturn

namespace Binary.AllowedipsTail
open TrustBase CommonBits
local instance : Labels := Image.linkedLabels

/-- The return tail executes every actual instruction and service, restores
all callee saves and the caller's stack, and exports the reusable physical
coverage/preempt/pending state. No relation or termination premise is used. -/
theorem execution (fetch : Int64 → Option Decoded) (agree : AllowedipsDecoderAgreement fetch)
    (pcContract : AllowedipsTracePcContract fetch) (bhContract : AllowedipsBhEnableContract fetch)
    {c coverage old ra initial world v}
    (pre : AllowedipsEntry c coverage old ra initial world v)
    (s : MachineData) (ready : Ready initial coverage old ra s) (rx : Nat) :
    Eventually (historyStep fetch) (fun t =>
      Post initial coverage old ra s.regs.rax t.machine ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x122⟩ rx
        [(.returned "lookup",none)] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x122⟩,[⟨s,AllowedipsImage.Lookup.entry+0x122⟩]⟩ := by
  have first := before_enable fetch agree pcContract pre s ready rx
  have second : Eventually (historyStep fetch) (fun t =>
      (t.machine.pc=AllowedipsImage.Lookup.entry+0x13c ∧ Enabled initial coverage old ra s.regs.rax t.machine.data) ∧
      Local (Writes initial coverage old) ⟨s,AllowedipsImage.Lookup.entry+0x122⟩ rx [] t)
      ⟨⟨s,AllowedipsImage.Lookup.entry+0x122⟩,[⟨s,AllowedipsImage.Lookup.entry+0x122⟩]⟩ := by
    apply chain fetch _ _ rx [] []
      (fun t => t.pc=AllowedipsImage.Lookup.entry+0x12b ∧ Stored initial coverage old ra s.regs.rax t.data)
      (fun t => t.pc=AllowedipsImage.Lookup.entry+0x13c ∧ Enabled initial coverage old ra s.regs.rax t.data) first
    rintro ⟨d,pc⟩ ⟨equal,stored⟩
    dsimp only at equal
    subst pc
    exact enable fetch agree bhContract pre d stored rx
  apply chain fetch _ _ rx [] [(.returned "lookup",none)]
    (fun t => t.pc=AllowedipsImage.Lookup.entry+0x13c ∧ Enabled initial coverage old ra s.regs.rax t.data)
    (Post initial coverage old ra s.regs.rax) second
  rintro ⟨d,pc⟩ ⟨equal,enabled⟩
  dsimp only at equal
  subst pc
  exact restore fetch agree d enabled rx

#print axioms execution
end Binary.AllowedipsTail
