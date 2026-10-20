import SourceAdapter
import PairSequenceCaller

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
set_option maxRecDepth 2048

theorem CallFacts.checked {n o c s w d query kinds ra}
    (facts : CallFacts n o c s w d query kinds ra) : Pre n o c s w query kinds ra := by
  have asserted := remove_assert_of_parts facts.device facts.storage facts.related facts.owners
  unfold Pre callBoundary
  rw [asserted]
  apply check_of _ _ _ _ facts.names
  rw [facts.device]
  apply check_of
  · simpa only [Bool.and_eq_true,beq_iff_eq,and_assoc] using
      And.intro facts.pc (And.intro facts.table (And.intro facts.queryAt
        (And.intro (facts.kindsAt .handshake) (facts.kindsAt .keypair))))
  · rw [facts.frame.checked]
    apply check_of
    · simpa only [Bool.and_eq_true] using And.intro facts.shapeApart facts.countApart
    · split
      next needed =>
        have active := (outputNeeded_iff _).mp needed
        apply check_of _ _ _ _ (facts.outputMapped active)
        apply check_of _ _ _ _ (facts.outputApart active)
        rfl
      next absent => rfl
end Binary.Pair.IndexLookup

namespace Binary.Pair.Sequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
set_option maxRecDepth 2048

theorem remove_pre {n o c base initialWorld ra current w owner address}
    (facts : InitialFacts n o c base initialWorld ra)
    (ready : Ready n o c base current.data.dmem w) (named : addressOf n owner=.ok address) :
    Remove.Pre n o c (install n base ra (.ofNat Remove.entry) address 0 current) w owner ra := by
  have next := install_ready facts ready (.ofNat Remove.entry) address 0
  have member := Remove.addressOf_ok named
  have bound := entry_bound facts.storage member
  apply Remove.pre_of_parts (next.asserted facts.storage) named _
    (install_frame facts ready _ _ _ 4 (by simp [stackSizes])).checked
  have positive : 0<o.entrySize := (storage_bounds facts.storage (entry_storage member)).1
  simp only [install,Bool.and_eq_true,beq_iff_eq]
  exact ⟨rfl,Nat.mod_eq_of_lt (by omega)⟩

theorem replace_pre {n o c base initialWorld ra current w pid kid old new}
    (facts : InitialFacts n o c base initialWorld ra)
    (ready : Ready n o c base current.data.dmem w)
    (oldAddress : addressOf n (.handshake pid)=.ok old)
    (newAddress : addressOf n (.keypair kid)=.ok new)
    (fresh : ∀ d, w.wg.dev=some d → d.indexTable.any (·.owner==.handshake pid)=true →
      d.indexTable.any (·.owner==.keypair kid)=false) :
    Replace.Pre n o c (install n base ra (.ofNat Replace.entry) old new current) w pid kid ra := by
  have next := install_ready facts ready (.ofNat Replace.entry) old new
  obtain ⟨d,device,_,_⟩ := next.state
  have oldNamed := Remove.addressOf_ok oldAddress
  have newNamed := Remove.addressOf_ok newAddress
  apply Replace.pre_of_parts (next.asserted facts.storage) oldAddress newAddress _ device
    (fun linked => next.newReady facts newNamed (fresh d device linked))
    (install_frame facts ready _ _ _ 5 (by simp [stackSizes])).checked
  have oldBound := entry_bound facts.storage oldNamed
  have newBound := entry_bound facts.storage newNamed
  have positive : 0<o.entrySize := (storage_bounds facts.storage (entry_storage oldNamed)).1
  simp only [install,Bool.and_eq_true,beq_iff_eq]
  exact ⟨⟨rfl,Nat.mod_eq_of_lt (by omega)⟩,Nat.mod_eq_of_lt (by omega)⟩

theorem mask_correct (kinds : List IndexKind) :
    KindMask (.ofNat 32 (kindMask kinds)) kinds := by
  intro kind
  unfold kindMask
  cases hs : kinds.contains .handshake <;> cases hk : kinds.contains .keypair <;>
    cases kind <;> simp only [hs,hk,↓reduceIte,kindWord] <;> decide

theorem lookup_pre {n o c base initialWorld ra current w query kinds}
    (facts : InitialFacts n o c base initialWorld ra)
    (ready : Ready n o c base current.data.dmem w) (queryBound : query<2^32) :
    IndexLookup.Pre n o c (install n base ra Image.Lookup.entry (kindMask kinds) query current) w query kinds ra := by
  have next := install_ready facts ready Image.Lookup.entry (kindMask kinds) query
  obtain ⟨d,device,related,owned⟩ := next.state
  let size := LookupStackWords (IndexLookup.callConfig n w d query kinds)
  have sizeAt : size ∈ stackSizes := by unfold size LookupStackWords; split <;> simp [stackSizes]
  apply IndexLookup.CallFacts.checked (d := d)
  refine ⟨device,related,facts.storage,owned,facts.names,rfl,?_,?_,?_,
    install_frame facts ready _ _ _ size sizeAt,facts.shapeApart,facts.countApart,
    (fun _ => next.mapped _ _ facts.outputMapped),(fun _ => facts.outputApart size sizeAt)⟩
  · rfl
  · simp [install,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Width.bits,
      BitVec.drop,BitVec.take,UInt64.toBitVec_ofNat',Nat.mod_eq_of_lt queryBound]
  · have bits : (BitVec.ofNat 64 (kindMask kinds)).extractLsb' 0 32=BitVec.ofNat 32 (kindMask kinds) := by
      apply BitVec.eq_of_toNat_eq
      simp
    simpa [install,Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,Width.bits,
      BitVec.drop,BitVec.take,UInt64.toBitVec_ofNat',bits] using mask_correct kinds

#print axioms remove_pre
#print axioms replace_pre
#print axioms lookup_pre
end Binary.Pair.Sequence
