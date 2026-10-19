import StackGuard

namespace Binary.Callback
open TrustBase
local instance : Labels := Image.linkedLabels

theorem change_guard {fetch} {guard guard' P : MachineState → Prop} {s}
    (implies : ∀ t, guard t → guard' t)
    (run : Eventually (guardedStep fetch guard) P s) :
    Eventually (guardedStep fetch guard') P s := by
  induction run with
  | done s hp => exact .done s hp
  | step s mid step _ ih =>
    apply step_cps
    exact ⟨implies s step.1,instruction_mono fetch s _ _ ih step.2⟩

def GuardedService (fetch : Int64 → Option Decoded) (outer : UInt64) (address : Int64)
    (ready : MachineState → Prop) (writes : MachineState → BitVec 64 → Prop)
    (effect : MachineState → MachineState → Prop) : Prop :=
  ∀ s ra, s.pc=address → ready s → EntryFrame s ra → s.data.regs.rsp≠outer+8 →
    Eventually (guardedStep fetch (StackGuard outer))
      (fun t => Returned s t ra ∧ EqualOutside (writes s) s.data.dmem t.data.dmem ∧ effect s t) s

theorem guarded_service {fetch address ready writes effect}
    (agree : ServiceDecoderAgreement fetch)
    (run : ∀ s ra, s.pc=address → ready s → EntryFrame s ra →
      Eventually (guardedStep ServiceImage.fetch (leafGuard s.data.regs.rsp))
        (fun t => Returned s t ra ∧ EqualOutside (writes s) s.data.dmem t.data.dmem ∧ effect s t) s)
    (outer : UInt64) : GuardedService fetch outer address ready writes effect := by
  intro s ra pc ready frame outside
  apply change_guard (guard := leafGuard s.data.regs.rsp)
  · intro t h
    exact fun equal => outside (h.1.symm.trans equal)
  · exact guarded_agreement agree (run s ra pc ready frame)

theorem pc_guarded (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch)
    (outer : UInt64) : GuardedService fetch outer (.ofNat 0xffffffff810f3100)
      (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc) := by
  apply guarded_service agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact pc_run s ra ready frame

theorem cmp4_guarded (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch)
    (outer : UInt64) : GuardedService fetch outer (.ofNat 0xffffffff810f3e80)
      (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4) := by
  apply guarded_service agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact cmp4_run s ra ready frame

theorem const_cmp4_guarded (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch)
    (outer : UInt64) : GuardedService fetch outer (.ofNat 0xffffffff810f3f00)
      (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4) := by
  apply guarded_service agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact const_cmp4_run s ra ready frame

theorem const_cmp1_guarded (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch)
    (outer : UInt64) : GuardedService fetch outer (.ofNat 0xffffffff810f3ec0)
      (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1) := by
  apply guarded_service agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  exact const_cmp1_run s ra ready frame

theorem bh_guarded (fetch : Int64 → Option Decoded) (agree : ServiceDecoderAgreement fetch)
    (outer : UInt64) : GuardedService fetch outer (.ofNat 0xffffffff810732c0) BhEnableReady
      (fun _ => InRange preemptCountAddress 4)
      (fun before after => ∀ old : BitVec 32,
        before.data.dmem.loadInt preemptCountAddress 4=some (old.toNat : Int) →
        after.data.dmem.loadInt preemptCountAddress 4=
          some ((old-before.data.regs.get (.low .rsi .W32)).toNat : Int)) := by
  apply guarded_service agree
  rintro ⟨s,p⟩ ra pc ready frame
  change p=_ at pc
  subst p
  rcases ready with ⟨count,read,hardirq,pending,apart⟩
  apply eventually_weaken (guardedStep ServiceImage.fetch (leafGuard s.regs.rsp))
    _ _ _ _ (bh_run s ra count read hardirq pending apart frame)
  rintro t ⟨returned,framed,changed⟩
  refine ⟨returned,framed,?_⟩
  intro old oldRead
  have equal : old=count := by
    apply BitVec.eq_of_toNat_eq
    exact_mod_cast Option.some.inj (oldRead.symm.trans read)
  subst old
  exact changed

#print axioms pc_guarded
#print axioms cmp4_guarded
#print axioms const_cmp4_guarded
#print axioms const_cmp1_guarded
#print axioms bh_guarded
end Binary.Callback
