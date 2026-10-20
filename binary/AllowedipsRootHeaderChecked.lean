import AllowedipsRootAttach

namespace Binary.Pair.Allowedips.Root
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem header_bound {width cidr : Nat} (family : width=32 ∨ width=128) (bound : cidr≤width) :
    headerWord width cidr<2^32 := by
  have widthBound : width≤128 := by omega
  have xorBound := Nat.xor_lt_two_pow (n:=5) (x:=cidr/8) (y:=(width/8-1)%8)
    (by omega) (by omega)
  unfold headerWord
  omega

private theorem pack_layout : LaidOut Add.fetch (Add.entry+0x494) (Add.r494.take 5) :=
  AllowedipsLoop.layout_take Add_r494_layout 5

private theorem layout_tail {fetch pc i size code}
    (layout : LaidOut fetch pc (⟨i,size⟩::code)) : LaidOut fetch (pc+.ofNat size) code := by
  cases layout with
  | cons _ _ _ _ _ _ _ rest => exact rest

private theorem finish_layout : LaidOut Add.fetch (Add.entry+0x4a1) (Add.r494.drop 5) := by
  have remaining := layout_tail (layout_tail (layout_tail (layout_tail (layout_tail Add_r494_layout))))
  simpa [Add.entry,Add.r494] using remaining

def headerRegs (s : MachineData) (width cidr : Nat) : Reg64s :=
  {s.regs with
    rax:=.ofNat (width/8),rdx:=.ofNat (headerWord width cidr),
    rsi:=.ofBitVec (s.regs.rbx.toBitVec+32),rcx:=.ofNat ((7-cidr%8)*65536)}

theorem header_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s : MachineData} {memory : DataMem} {width cidr : Nat} (family : width=32 ∨ width=128) (bound : cidr≤width)
    (bits : s.regs.rbp=.ofNat width) (requested : s.regs.rdi=.ofNat cidr)
    (shifted : s.regs.rsi=.ofNat (cidr/8)) (index : s.regs.rcx=.ofNat (width/8-1))
    (original : s.regs.rdx=.ofNat cidr) (bytes : s.regs.rax=.ofNat (width/8))
    (checked : store s.dmem (s.regs.rbx.toNat+24) 4 (headerWord width cidr)=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x4ab ∧ t.data.dmem=memory ∧ t.data.regs=headerRegs s width cidr ∧
      t.data.status.cf=(width==32)) ⟨s,Add.entry+0x481⟩ := by
  have small := header_bound family bound
  let word := BitVec.ofNat 32 (headerWord width cidr)
  -- Use the representation lemma: definitional reduction through Fin
  -- expanded this tiny conversion to gigabytes during calibration.
  have wordNat : word.toNat=headerWord width cidr := by
    simp only [word,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
  have wordReg : UInt64.ofBitVec (word.setWidth 64)=UInt64.ofNat (headerWord width cidr) := by
    dsimp only [word]
    rw [BitVec.setWidth_ofNat_of_le_of_lt (by decide) small]
    rfl
  obtain ⟨mapped,memoryEq⟩ := store_facts checked
  have stored : memory=s.dmem.storeInt (s.regs.rbx.toBitVec+24) 4 word.toInt := by
    rw [←wordNat,store_unsigned] at memoryEq
    simpa [BitVec.ofNat_add,ofNat_uint64] using memoryEq
  have first := header_prepare s width cidr family bound bits requested shifted index original bytes
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r481_layout.agreement decoder.add) s _ first)
  rintro a ⟨pc1,mem1,regs1⟩
  rw [Placement.at_pc a _ pc1]
  have second := header_pack a.data width cidr family bound
    (by simp only [regs1]) (by simp only [regs1]) (by simp only [regs1])
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (pack_layout.agreement decoder.add) a.data _ second)
  rintro b ⟨pc2,mem2,regs2⟩
  rw [Placement.at_pc b _ pc2]
  have third := header_finish b.data word width family
    (by simp only [regs2,regs1]) (by simp only [regs2,wordReg])
    (by simpa [mem2,mem1,regs2,regs1,BitVec.ofNat_add,ofNat_uint64] using mapped)
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (finish_layout.agreement decoder.add) b.data _ third)
  rintro t ⟨pc3,mem3,regs3,carry⟩
  refine ⟨pc3,?_,?_,carry⟩
  · simpa only [mem2,mem1,regs2,regs1,stored] using mem3
  · simpa only [regs2,regs1,headerRegs] using regs3

#print axioms header_checked
end Binary.Pair.Allowedips.Root
