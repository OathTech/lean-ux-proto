import PairAllowedipsNodeBoundary
import AllowedipsAllocatedFacts

namespace Binary.Pair.Allowedips.NodeInit
open Leanux

structure BoundaryFields (names : Names) (o : AllowedipsProbe.Offsets) (world : World)
    (machine : MachineState) (key cidr pid base : Nat) : Prop where
  asserted : assertAt names o machine.data.dmem world=.ok ()
  baseRead : readNat machine machine.data.regs.rsp.toNat 8=.ok base
  pc : machine.pc=AllowedipsMutationImage.Add.entry+0x156
  family : machine.data.regs.rbp.toNat=32 ∨ machine.data.regs.rbp.toNat=128
  owner : Trie.address names.trie.peers (some pid)=.ok machine.data.regs.r14.toNat
  cidrRead : readNat machine (machine.data.regs.rsp.toNat+16) 4=.ok cidr
  cidrBound : cidr≤machine.data.regs.rbp.toNat
  original : machine.data.regs.r12.toNat=cidr
  bits : machine.data.regs.r15.toNat=machine.data.regs.rbp.toNat
  allocated : validate (names.allocated base) o=.ok ()
  zero : readNat machine base 72=.ok 0
  query : Placement.queryLocals machine key machine.data.regs.rbp.toNat=.ok ()
  stackMapped : ∀ offset ∈ [36,43,44],
    (machine.data.dmem.loadInt (.ofNat 64 (machine.data.regs.rsp.toNat+offset)) 1).isSome=true
  queryApart : spansApart [(machine.data.regs.r13.toNat,machine.data.regs.rbp.toNat/8)]
    (writeSpans (names.allocated base) machine.data base)=true
  stackApart : spansApart [(machine.data.regs.rsp.toNat+36,1),
      (machine.data.regs.rsp.toNat+43,1),(machine.data.regs.rsp.toNat+44,1)]
    ([(base,72),(names.table,24)]++allocations names o)=true

theorem boundary_fields {names o world machine key cidr pid base}
    (checked : boundary names o world machine key cidr pid=.ok base) :
    BoundaryFields names o world machine key cidr pid base := by
  unfold boundary at checked
  obtain ⟨_,asserted,checked⟩ := bind_ok checked
  obtain ⟨allocation,baseRead,checked⟩ := bind_ok checked
  obtain ⟨pc,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨family,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨owner,ownerAt,checked⟩ := bind_ok checked
  obtain ⟨peer,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨requested,cidrRead,checked⟩ := bind_ok checked
  obtain ⟨cidrChecked,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨locals,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨_,allocated,checked⟩ := bind_ok checked
  obtain ⟨raw,zero,checked⟩ := bind_ok checked
  obtain ⟨zeroValue,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨_,query,checked⟩ := bind_ok checked
  obtain ⟨_,mapped,checked⟩ := bind_ok checked
  obtain ⟨queryApart,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨stackApart,checked⟩ := require_bind_ok _ _ _ _ checked
  cases Except.ok.inj checked
  have readable := forIn_ok (P:=fun offset : Nat =>
      (machine.data.dmem.loadInt (.ofNat 64 (machine.data.regs.rsp.toNat+offset)) 1).isSome=true)
    (fun _ _ _ _ run => by
      obtain ⟨_,mapped,run⟩ := bind_ok run
      exact ⟨(),(Except.ok.inj run).symm,require_ok mapped⟩) mapped
  have cidrChecked : requested=cidr ∧ cidr≤machine.data.regs.rbp.toNat := by
    simpa only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using cidrChecked
  have locals : machine.data.regs.r12.toNat=cidr ∧ machine.data.regs.r15.toNat=machine.data.regs.rbp.toNat := by
    simpa only [Bool.and_eq_true,beq_iff_eq] using locals
  have peer := eq_of_beq peer
  have zeroValue := eq_of_beq zeroValue
  exact ⟨asserted,baseRead,eq_of_beq pc,by simpa only [Bool.or_eq_true,beq_iff_eq] using family,
    peer ▸ ownerAt,cidrChecked.1 ▸ cidrRead,cidrChecked.2,locals.1,locals.2,
    mapError_ok allocated,zeroValue ▸ zero,query,readable,queryApart,stackApart⟩

#print axioms boundary_fields
end Binary.Pair.Allowedips.NodeInit
