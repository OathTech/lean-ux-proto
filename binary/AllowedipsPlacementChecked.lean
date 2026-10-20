import AllowedipsPlacementCheck

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG TrustBase CommonBitsCoverage AllowedipsMutationImage AllowedipsRelation
local instance : Labels := Image.linkedLabels

theorem HeaderFields.initial {names o c w s root key cidr bits peer stack d}
    (fields : HeaderFields names o c w s root key cidr bits peer stack (none,root,none))
    (related : Corresponds names o s.data.dmem d)
    (shape : heap names (target d) s.data.dmem=.ok ()) (ambient : Ambient) :
    Invariant names o d s.data c root key cidr bits (.ofNat 64 peer)
      (none,root,none) (Source.Aip.store d) ambient s := by
  refine ⟨rfl,fields.frame,?_,related,shape⟩
  have parent := fields.locals.previous
  obtain ⟨id,rootAt⟩ := Option.isSome_iff_exists.mp fields.locals.nonempty
  change root=some id at rootAt
  refine ⟨parent,?_⟩
  rw [rootAt]
  refine ⟨fields.pc,?_,.root id rfl⟩
  apply UInt64.toBitVec_inj.mp
  simpa only [rootAt,pointer,Option.map_some,Option.getD_some,UInt64.toBitVec_ofBitVec] using fields.locals.cursor

/-- The complete placement loop from the exact executable header assertion.
The source operation is the landed mirror's nodePlacement. All memory inputs
and the loop invariant are consequences of the checked entry state. -/
theorem loop_checked (fetch : Int64 → Option Decoded) (decoder : AllowedipsDecoderAgreement fetch)
    (mutation : AllowedipsMutationDecoderAgreement fetch)
    (callbacks : CommonBits.Callbacks fetch) (cmp : AllowedipsTraceCmp1Contract fetch)
    {names o c w d s root key cidr bits peer stack}
    (device : w.wg.dev=some d)
    (checked : header names o c w s root key cidr bits peer stack (none,root,none)=.ok ())
    (ambient finalAmbient : Ambient) (finalStore : AipStore) (result : Option NodeId × Bool)
    (accepted : ((WG.nodePlacement root key cidr bits).run (Source.Aip.store d)).run ambient=
      .ok ((result,finalStore),finalAmbient)) :
    Eventually (instructionStep fetch) (fun t =>
      finalStore=Source.Aip.store d ∧ Frame s.data c t.data ∧
      t.pc=(if result.2 then Add.entry+0x3ca else Add.entry+0x120) ∧
      t.data.regs.rbx=ptr (Trie.interpretation names.trie.nodes) result.1 ∧
      (result.2=false → t.data.regs.rbp=.ofBitVec ((BitVec.ofNat 32 bits).setWidth 64) ∧
        t.data.regs.r14=.ofNat peer) ∧
      Corresponds names o t.data.dmem d ∧ heap names (target d) t.data.dmem=.ok ()) s := by
  have fields := header_fields checked
  obtain ⟨actual,present,related,shape⟩ := assertAt_ok fields.asserted
  have same : actual=d := Option.some.inj (present.symm.trans device)
  subst actual
  have trie := Trie.trieHeap_of_checks related.trie (heap_trie shape) fields.input
  have small : bits<2^32 := by rcases trie.1 with h|h <;> omega
  have saved : SavedInput s.data c (.ofNat 32 bits) (.ofNat 64 peer) := by
    refine ⟨?_,fields.locals.peerRead,fields.savedApart⟩
    change s.data.dmem.loadInt (s.data.regs.rsp.toBitVec+0x24) 4=some ((BitVec.ofNat 32 bits).toNat : Int)
    simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] using fields.locals.widthRead
  have inputs := inputs_of_heap related trie fields.locals fields.cidrBound fields.readApart fields.queryApart saved
  exact loop fetch decoder mutation callbacks cmp inputs related shape fields.readApart
    ambient finalAmbient finalStore result s accepted (fields.initial related shape ambient)

#print axioms loop_checked
end Binary.Pair.Allowedips.Placement
