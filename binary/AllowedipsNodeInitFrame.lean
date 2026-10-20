import PairAllowedipsNodeInit
import AllowedipsRootInitFrame

namespace Binary.Pair.Allowedips.NodeInit
open Root

def StackWrites (stack : Nat) (a : BitVec 64) : Prop :=
  ∃ offset ∈ [36,43,44], InRange (.ofNat 64 (stack+offset)) 1 a

def EntryWrites (names : Names) (s : MachineData) (base : Nat) (a : BitVec 64) : Prop :=
  InRange (.ofNat 64 base) 72 a ∨ ListWrites (names.allocated base) a ∨ StackWrites s.regs.rsp.toNat a

def InitWrites (base stack : Nat) (a : BitVec 64) : Prop :=
  InRange (.ofNat 64 base) 56 a ∨ StackWrites stack a

/-- Separate the three real stack stores from the packed record-header store.
The frame is derived from the executed summary without alias assumptions. -/
theorem header_parts {stack width base cidr : Nat} {before after : DataMem}
    (checked : header stack width base cidr before=.ok after) :
    ∃ saved, EqualOutside (StackWrites stack) before saved ∧
      Root.store saved (base+24) 4 (headerWord width cidr)=.ok after := by
  unfold header at checked
  obtain ⟨m1,first,checked⟩ := bind_ok checked
  obtain ⟨m2,second,checked⟩ := bind_ok checked
  obtain ⟨m3,third,last⟩ := bind_ok checked
  refine ⟨m3,?_,last⟩
  intro a outside
  have keep {memory next : DataMem} {offset value : Nat}
      (member : offset ∈ [36,43,44])
      (run : store memory (stack+offset) 1 value=.ok next) : memory.get? a=next.get? a := by
    rw [(store_facts run).2]
    exact storeInt_frame _ _ _ _ a (fun inside => outside ⟨offset,member,inside⟩)
  exact (keep (by simp) first).trans ((keep (by simp) second).trans (keep (by simp) third))

theorem header_frame {names : Names} {s : MachineData} {base cidr : Nat} {before after : DataMem}
    (checked : header s.regs.rsp.toNat s.regs.rbp.toNat base cidr before=.ok after) :
    EqualOutside (EntryWrites names s base) before after := by
  obtain ⟨saved,frame,stored⟩ := header_parts checked
  intro a outside
  have first := frame a (fun inside => outside (.inr (.inr inside)))
  have last := store_record_frame (by decide) stored a (fun inside => by
    obtain ⟨i,bound,equal⟩ := inside
    exact outside (.inl ⟨i,by omega,equal⟩))
  exact first.trans last

theorem attach_cidr {s : MachineData} {memory : DataMem} {base cidr : Nat}
    (checked : attach s=.ok (memory,base,cidr)) : s.regs.r12.toNat=cidr := by
  unfold attach at checked
  obtain ⟨allocation,_,checked⟩ := bind_ok checked
  obtain ⟨requested,_,checked⟩ := bind_ok checked
  obtain ⟨last,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,locals,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have values : (cidr≤s.regs.rbp.toNat ∧ s.regs.r12.toNat=cidr) ∧
      s.regs.r15.toNat=s.regs.rbp.toNat := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] using require_ok locals
  exact values.1.2

theorem effect_parts {s : MachineData} {memory : DataMem} {base cidr : Nat}
    (original : s.regs.r12.toNat=cidr) (checked : effect s=.ok (memory,base)) :
    ∃ attached initialized, attach s=.ok (attached,base,cidr) ∧
      header s.regs.rsp.toNat s.regs.rbp.toNat base cidr attached=.ok initialized ∧
      Root.copy {s with regs:={s.regs with rbx:=.ofNat base}} initialized=.ok memory := by
  unfold effect at checked
  obtain ⟨⟨attached,allocation,requested⟩,attachment,checked⟩ := bind_ok checked
  obtain ⟨initialized,headerCheck,checked⟩ := bind_ok checked
  obtain ⟨copied,copyCheck,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have requestedEq : requested=cidr := (attach_cidr attachment).symm.trans original
  subst requested
  exact ⟨attached,initialized,attachment,headerCheck,copyCheck⟩

theorem header_copy_frame {s : MachineData} {attached initialized memory : DataMem} {base cidr : Nat}
    (small : base<2^64)
    (headerCheck : header s.regs.rsp.toNat s.regs.rbp.toNat base cidr attached=.ok initialized)
    (copyCheck : Root.copy {s with regs:={s.regs with rbx:=.ofNat base}} initialized=.ok memory) :
    EqualOutside (InitWrites base s.regs.rsp.toNat) attached memory := by
  obtain ⟨saved,stackFrame,stored⟩ := header_parts headerCheck
  have copiedFrame := copy_frame copyCheck
  have baseNat : (UInt64.ofNat base).toNat=base := Nat.mod_eq_of_lt small
  simp only [baseNat] at copiedFrame
  intro a outside
  have first := stackFrame a (fun inside => outside (.inr inside))
  have middle := store_record_frame (by decide) stored a (fun inside => outside (.inl inside))
  have last := copiedFrame a (fun inside => outside (.inl inside))
  exact first.trans (middle.trans last)


end Binary.Pair.Allowedips.NodeInit
