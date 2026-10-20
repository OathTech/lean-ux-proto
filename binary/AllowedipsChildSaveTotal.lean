import AllowedipsChildSaved
import AllowedipsRootTotalMemory

namespace Binary.Pair.Allowedips.ChildSetup
open Root

private theorem ok_bind (value : α) (f : α → Except ε β) :
    ((Except.ok value : Except ε α) >>= f)=f value := rfl

/-- Readability of the current stack slots derives the save effect used by
both the runner and the executed branch theorem. -/
theorem save_total {s : MachineData}
    (baseMapped : (s.dmem.loadInt (.ofNat 64 s.regs.rsp.toNat) 8).isSome=true)
    (directionMapped : (s.dmem.loadInt (.ofNat 64 (s.regs.rsp.toNat+8)) 1).isSome=true)
    (indexMapped : (s.dmem.loadInt (.ofNat 64 (s.regs.rsp.toNat+16)) 8).isSome=true) :
    ∃ memory, saveEffect s=.ok memory := by
  let first := s.dmem.storeInt (.ofNat 64 (s.regs.rsp.toNat+16)) 8 s.regs.rax.toNat
  have firstStore : store s.dmem (s.regs.rsp.toNat+16) 8 s.regs.rax.toNat=.ok first := store_total indexMapped
  let second := first.storeInt (.ofNat 64 (s.regs.rsp.toNat+8)) 1 (s.regs.rdx.toNat%256 : Nat)
  have secondStore : store first (s.regs.rsp.toNat+8) 1 (s.regs.rdx.toNat%256)=.ok second :=
    store_total ((store_mapped firstStore) _ _ directionMapped)
  let memory := second.storeInt (.ofNat 64 s.regs.rsp.toNat) 8 s.regs.r8.toNat
  have lastStore : store second s.regs.rsp.toNat 8 s.regs.r8.toNat=.ok memory :=
    store_total (((store_mapped firstStore).trans (store_mapped secondStore)) _ _ baseMapped)
  exact ⟨memory,by simp only [saveEffect,firstStore,secondStore,lastStore,ok_bind]⟩

end Binary.Pair.Allowedips.ChildSetup
