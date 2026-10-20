import PairAllowedipsPlacement
import PairLocalsProof

namespace Binary.Pair.Allowedips.Placement
open Leanux Leanux.WG

structure LocalFields (names : Names) (s : MachineState) (key cidr bits peer stack : Nat) (acc : Acc) : Prop where
  openLoop : acc.1=none
  nonempty : acc.2.1.isSome=true
  cursor : s.data.regs.rbx.toBitVec=AllowedipsRelation.pointer (Trie.interpretation names.trie.nodes) acc.2.1
  previous : s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8=
    some ((AllowedipsRelation.pointer (Trie.interpretation names.trie.nodes) acc.2.2).toNat : Int)
  stackValue : s.data.regs.rsp.toNat=stack
  cidrValue : s.data.regs.r12=.ofNat cidr
  bitsValue : s.data.regs.r15=.ofNat bits
  widthRead : s.data.dmem.loadInt (s.data.regs.rsp.toBitVec+0x24) 4=some (bits : Int)
  peerRead : s.data.dmem.loadInt (s.data.regs.rsp.toBitVec+0x18) 8=some ((BitVec.ofNat 64 peer).toNat : Int)
  query : AllowedipsChild.QueryWords s.data.dmem s.data.regs.r13.toBitVec bits key

theorem register_value {r : UInt64} {n : Nat} (value : r.toNat=n) : r=.ofNat n :=
  UInt64.toBitVec_inj.mp (Trie.u64_of_nat value)

private theorem word_bound_nat (n : Nat) (bound : (n : Int)<18446744073709551616) : n<2^64 := by omega

private theorem combined_words (hi lo key : Nat) (value : hi*2^64+lo=key) (bound : lo<2^64) :
    key/2^64=hi ∧ key%2^64=lo := by omega

theorem cursorLocals_fields {names s acc}
    (checked : cursorLocals names s acc=.ok ()) :
    acc.1=none ∧ acc.2.1.isSome=true ∧
    s.data.regs.rbx.toBitVec=AllowedipsRelation.pointer (Trie.interpretation names.trie.nodes) acc.2.1 ∧
    s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8=
      some ((AllowedipsRelation.pointer (Trie.interpretation names.trie.nodes) acc.2.2).toNat : Int) := by
  unfold cursorLocals at checked
  obtain ⟨active,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨current,currentAt,checked⟩ := bind_ok checked
  obtain ⟨previous,previousRead,checked⟩ := bind_ok checked
  obtain ⟨parent,parentAt,checked⟩ := bind_ok checked
  have cursor := require_ok checked
  have active' : acc.1=none ∧ acc.2.1.isSome=true := by
    simpa only [Bool.and_eq_true,Option.isNone_iff_eq_none] using active
  have cursor' : s.data.regs.rbx.toNat=current ∧ previous=parent := by
    simpa only [Bool.and_eq_true,beq_iff_eq] using cursor
  have loaded := Trie.readNat_loadInt previousRead
  have previousBound : previous<2^64 := by
    have bound := (loadInt_range _ _ _ _ loaded).2
    change (previous : Int)<18446744073709551616 at bound
    exact word_bound_nat previous bound
  refine ⟨active'.1,active'.2,(Trie.u64_of_nat cursor'.1).trans (Trie.address_value currentAt).symm,?_⟩
  rw [Trie.address_value parentAt,←cursor'.2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt previousBound]
  simpa only [(Trie.u64_of_nat (rfl : s.data.regs.rsp.toNat=s.data.regs.rsp.toNat)).symm] using loaded

structure SavedFields (s : MachineState) (cidr bits peer stack : Nat) : Prop where
  stackValue : s.data.regs.rsp.toNat=stack
  cidrValue : s.data.regs.r12=.ofNat cidr
  bitsValue : s.data.regs.r15=.ofNat bits
  widthRead : s.data.dmem.loadInt (s.data.regs.rsp.toBitVec+0x24) 4=some (bits : Int)
  peerRead : s.data.dmem.loadInt (s.data.regs.rsp.toBitVec+0x18) 8=some ((BitVec.ofNat 64 peer).toNat : Int)

theorem savedLocals_fields {names s root cidr bits peer stack}
    (checked : savedLocals names s root cidr bits peer stack=.ok ()) :
    SavedFields s cidr bits peer stack := by
  unfold savedLocals at checked
  obtain ⟨registers,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨slot,_,checked⟩ := bind_ok checked
  obtain ⟨rootWord,_,checked⟩ := bind_ok checked
  obtain ⟨rootAddress,_,checked⟩ := bind_ok checked
  obtain ⟨owner,ownerRead,checked⟩ := bind_ok checked
  obtain ⟨width,widthRead,checked⟩ := bind_ok checked
  obtain ⟨requested,_,checked⟩ := bind_ok checked
  have saved := require_ok checked
  have registers' : (s.data.regs.rsp.toNat=stack ∧ s.data.regs.r12.toNat=cidr) ∧ s.data.regs.r15.toNat=bits := by
    simpa only [Bool.and_eq_true,beq_iff_eq] using registers
  have saved' : (((slot=names.table+(if bits==32 then AllowedipsMutationLayout.root4 else AllowedipsMutationLayout.root6) ∧
      rootWord=rootAddress) ∧ owner=peer) ∧ width=bits) ∧ requested=cidr := by
    simpa only [Bool.and_eq_true,beq_iff_eq] using saved
  have stackWord := Trie.u64_of_nat registers'.1.1
  have ownerLoaded := Trie.readNat_loadInt ownerRead
  have ownerBound : peer<2^64 := by
    have bound := (loadInt_range _ _ _ _ ownerLoaded).2
    rw [saved'.1.1.2] at bound
    change (peer : Int)<18446744073709551616 at bound
    exact word_bound_nat peer bound
  refine ⟨registers'.1.1,register_value registers'.1.2,register_value registers'.2,?_,?_⟩
  · have read := Trie.readNat_loadInt widthRead
    simpa only [stackWord,BitVec.ofNat_add,show BitVec.ofNat 64 36=(36 : BitVec 64) from rfl,saved'.1.2] using read
  · simpa only [stackWord,BitVec.ofNat_add,show BitVec.ofNat 64 24=(24 : BitVec 64) from rfl,saved'.1.1.2,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ownerBound] using ownerLoaded

theorem query4_fields {s key} (checked : query4 s key=.ok ()) :
    s.data.dmem.loadInt s.data.regs.r13.toBitVec 4=some (key : Int) := by
  unfold query4 at checked
  obtain ⟨actual,read,checked⟩ := bind_ok checked
  have equal : actual=key := eq_of_beq (require_ok checked)
  have queryAddress : BitVec.ofNat 64 s.data.regs.r13.toNat=s.data.regs.r13.toBitVec := (Trie.u64_of_nat rfl).symm
  simpa only [equal,queryAddress] using Trie.readNat_loadInt read

theorem query6_fields {s key} (checked : query6 s key=.ok ()) :
    s.data.dmem.loadInt s.data.regs.r13.toBitVec 8=some ((key/2^64 : Nat) : Int) ∧
    s.data.dmem.loadInt (s.data.regs.r13.toBitVec+8) 8=some ((key%2^64 : Nat) : Int) := by
  unfold query6 at checked
  obtain ⟨hi,hiRead,checked⟩ := bind_ok checked
  obtain ⟨lo,loRead,checked⟩ := bind_ok checked
  have value : hi*2^64+lo=key := eq_of_beq (require_ok checked)
  have lowBound : lo<2^64 := by
    have bound := (loadInt_range _ _ _ _ (Trie.readNat_loadInt loRead)).2
    change (lo : Int)<18446744073709551616 at bound
    exact word_bound_nat lo bound
  obtain ⟨high,low⟩ := combined_words hi lo key value lowBound
  have queryAddress : BitVec.ofNat 64 s.data.regs.r13.toNat=s.data.regs.r13.toBitVec := (Trie.u64_of_nat rfl).symm
  constructor
  · simpa only [high,queryAddress] using Trie.readNat_loadInt hiRead
  · simpa only [low,BitVec.ofNat_add,queryAddress,show BitVec.ofNat 64 8=(8 : BitVec 64) from rfl] using Trie.readNat_loadInt loRead

theorem queryLocals_fields {s key bits} (checked : queryLocals s key bits=.ok ()) :
    AllowedipsChild.QueryWords s.data.dmem s.data.regs.r13.toBitVec bits key := by
  by_cases width : bits=32
  · have run : query4 s key=.ok () := by simpa only [queryLocals,width,beq_self_eq_true,ite_true] using checked
    simpa only [AllowedipsChild.QueryWords,width,ite_true] using query4_fields run
  · have run : query6 s key=.ok () := by simpa only [queryLocals,show (bits==32)=false from by simp [width],Bool.false_eq_true,ite_false] using checked
    simpa only [AllowedipsChild.QueryWords,ite_eq_right width] using query6_fields run

theorem locals_fields {names s root key cidr bits peer stack acc}
    (checked : locals names s root key cidr bits peer stack acc=.ok ()) :
    LocalFields names s key cidr bits peer stack acc := by
  unfold locals at checked
  obtain ⟨_,cursor,checked⟩ := bind_ok checked
  obtain ⟨_,saved,query⟩ := bind_ok checked
  obtain ⟨active,nonempty,bx,parent⟩ := cursorLocals_fields cursor
  obtain ⟨sp,r12,r15,width,peer⟩ := savedLocals_fields saved
  exact ⟨active,nonempty,bx,parent,sp,r12,r15,width,peer,queryLocals_fields query⟩

#print axioms locals_fields
end Binary.Pair.Allowedips.Placement
