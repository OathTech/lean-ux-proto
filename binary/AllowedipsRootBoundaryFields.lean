import PairAllowedipsRootBoundary
import PairAllowedipsAssert
import AllowedipsAllocatedFacts
import AllowedipsPlacementLocals

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG

structure BoundaryFields (names : Names) (o : AllowedipsProbe.Offsets) (world : World)
    (machine : MachineState) (key cidr pid : Nat) : Prop where
  asserted : assertAt names o machine.data.dmem world=.ok ()
  device : ∃ d, world.wg.dev=some d ∧
    (if machine.data.regs.rbp.toNat=32 then d.peerAllowedips.root4 else d.peerAllowedips.root6)=none
  pc : machine.pc=AllowedipsMutationImage.Add.entry+0x443
  family : machine.data.regs.rbp.toNat=32 ∨ machine.data.regs.rbp.toNat=128
  owner : Trie.address names.trie.peers (some pid)=.ok machine.data.regs.r14.toNat
  cidrRead : readNat machine (machine.data.regs.rsp.toNat+16) 4=.ok cidr
  cidrBound : cidr≤machine.data.regs.rbp.toNat
  allocated : validate (names.allocated machine.data.regs.rbx.toNat) o=.ok ()
  zero : readNat machine machine.data.regs.rbx.toNat 72=.ok 0
  query : Placement.queryLocals machine key machine.data.regs.rbp.toNat=.ok ()
  saved : readNat machine (machine.data.regs.rsp.toNat+8) 8=
    .ok (names.table+(if machine.data.regs.rbp.toNat=32 then 0 else 8))
  apart : spansApart [(machine.data.regs.r13.toNat,machine.data.regs.rbp.toNat/8),
      (machine.data.regs.rsp.toNat+8,8),(machine.data.regs.rsp.toNat+16,4)]
    (writeSpans (names.allocated machine.data.regs.rbx.toNat) machine.data)=true

theorem boundary_fields {names o world machine key cidr pid}
    (checked : boundary names o world machine key cidr pid=.ok ()) :
    BoundaryFields names o world machine key cidr pid := by
  unfold boundary at checked
  obtain ⟨_,asserted,checked⟩ := bind_ok checked
  cases device : world.wg.dev with
  | none => simp only [device] at checked; cases checked
  | some d =>
    simp only [device] at checked
    obtain ⟨pc,checked⟩ := require_bind_ok _ _ _ _ checked
    obtain ⟨family,checked⟩ := require_bind_ok _ _ _ _ checked
    obtain ⟨empty,checked⟩ := require_bind_ok _ _ _ _ checked
    obtain ⟨owner,ownerAt,checked⟩ := bind_ok checked
    obtain ⟨peer,checked⟩ := require_bind_ok _ _ _ _ checked
    obtain ⟨requested,cidrRead,checked⟩ := bind_ok checked
    obtain ⟨cidrChecked,checked⟩ := require_bind_ok _ _ _ _ checked
    obtain ⟨_,allocated,checked⟩ := bind_ok checked
    obtain ⟨raw,zero,checked⟩ := bind_ok checked
    obtain ⟨zeroValue,checked⟩ := require_bind_ok _ _ _ _ checked
    obtain ⟨_,query,checked⟩ := bind_ok checked
    obtain ⟨slot,saved,checked⟩ := bind_ok checked
    obtain ⟨savedSlot,checked⟩ := require_bind_ok _ _ _ _ checked
    have cidrChecked : requested=cidr ∧ cidr≤machine.data.regs.rbp.toNat := by
      simpa only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using cidrChecked
    have peer := eq_of_beq peer
    have zeroValue := eq_of_beq zeroValue
    have savedSlot : slot=names.table+(if machine.data.regs.rbp.toNat=32 then 0 else 8) := by
      simpa only [beq_iff_eq] using eq_of_beq savedSlot
    exact ⟨asserted,⟨d,device,by simpa only [beq_iff_eq,Option.isNone_iff_eq_none] using empty⟩,
      eq_of_beq pc,by simpa only [Bool.or_eq_true,beq_iff_eq] using family,
      peer ▸ ownerAt,cidrChecked.1 ▸ cidrRead,cidrChecked.2,mapError_ok allocated,zeroValue ▸ zero,
      query,savedSlot ▸ saved,require_ok checked⟩

#print axioms boundary_fields
end Binary.Pair.Allowedips.Root
