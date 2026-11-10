import C1BelowInternalRecord
import AllowedipsRootTotalMemory

/-! Result C1, work package 3: the internal node's initialization on the
split path of `add`, from the second allocation's return (`add+0x292`, a
non-NULL object in `rax`) to `add+0x31d`, where `choose(node, down->bits)`
begins: the reload and save of the first node, the coverage call, the empty
list head, the packed header for `min(cidr, common)`, and the copy of the
leaf's key out of the first node. Hypotheses are facts about the state at
`add+0x292` only (`Entry`); the conclusion (`Exit`) carries the registers
the connections read, the byte frame, and the internal node's record. -/
namespace Binary.Pair.Allowedips.C1Internal
open Leanux Leanux.WG AllowedipsMutationImage Root CommonBitsCoverage
local instance : Labels := Image.linkedLabels

/-- The state at `add+0x292` on the split path. `base` is the first node
(the leaf, initialized, in the stack word at `rsp+0x18`), `base2` the object
the second allocation returned, `common` the result of `common_bits` (only
the low byte of `r13` is known), `key` the leaf's key as the first node
stores it. -/
structure Entry (c : Context) (a : MachineData) (base base2 width cidr common key : Nat) : Prop where
  family : width=32 ∨ width=128
  cidrBound : cidr≤width
  commonBound : common≤width
  object : a.regs.rax=.ofNat base2
  nonzero : base2≠0
  extent : base2+72≤2^64
  zero : readNat ⟨a,0⟩ base2 72=.ok 0
  stackLow : 8≤a.regs.rsp.toNat
  stackHigh : a.regs.rsp.toNat+48≤2^64
  firstRead : word a.dmem "saved.node" (a.regs.rsp.toNat+24) 8=.ok base
  firstExtent : base+72≤2^64
  cidrRead : word a.dmem "saved.cidr" (a.regs.rsp.toNat+16) 1=.ok cidr
  maskRead : word a.dmem "saved.mask" (a.regs.rsp.toNat+36) 1=.ok ((width/8-1)%8)
  commonLow : BitVec.extractLsb' 0 8 a.regs.r13.toBitVec=BitVec.ofNat 8 common
  bits : a.regs.r15=.ofNat width
  bytes : a.regs.rbp=.ofNat (width/8)
  source : a.regs.r14=.ofNat (base+32)
  firstKey : if width=32 then word a.dmem "node.key32" (base+32) 4=.ok key else
    ∃ hi lo, word a.dmem "node.key128.high" (base+32) 8=.ok hi ∧
      word a.dmem "node.key128.low" (base+40) 8=.ok lo ∧ key=hi*2^64+lo
  ready : CallsReady c a
  nodeStack : ∀ x, InRange (.ofNat 64 base2) 72 x → ¬InRange (.ofNat 64 (a.regs.rsp.toNat-8)) 56 x
  nodeContext : ∀ x, c.bytes x → ¬InRange (.ofNat 64 base2) 72 x
  nodeCoverage : ∀ x, c.writes x → ¬InRange (.ofNat 64 base2) 72 x
  nodeFirst : ∀ x, InRange (.ofNat 64 base2) 72 x → ¬InRange (.ofNat 64 base) 72 x
  stackContext : ∀ x, c.bytes x → ¬InRange (.ofNat 64 (a.regs.rsp.toNat+24)) 8 x
  stackCoverage : ∀ x, c.writes x → ¬InRange (.ofNat 64 a.regs.rsp.toNat) 48 x
  firstStack : ∀ x, InRange (.ofNat 64 (base+32)) 16 x → ¬InRange (.ofNat 64 (a.regs.rsp.toNat-8)) 56 x
  firstCoverage : ∀ x, c.writes x → ¬InRange (.ofNat 64 (base+32)) 16 x

/-- The bytes the segment may write: the internal node, the stack word of
the first node, the coverage call's return word and the coverage buffer. -/
def Writes (c : Context) (stack : UInt64) (base2 : Nat) (x : BitVec 64) : Prop :=
  InRange (.ofNat 64 base2) 72 x ∨ InRange (.ofNat 64 (stack.toNat+24)) 8 x ∨
    InRange (stack.toBitVec-8) 8 x ∨ c.writes x

/-- The state at `add+0x31d`. -/
structure Exit (c : Context) (a : MachineData) (base base2 width least key : Nat) (t : MachineData) : Prop where
  stack : t.regs.rsp=a.regs.rsp
  parent : t.regs.rbx=a.regs.rbx
  bytes : t.regs.rbp=a.regs.rbp
  common : t.regs.r13=a.regs.r13
  source : t.regs.r14=a.regs.r14
  bits : t.regs.r15=a.regs.r15
  node : t.regs.r12=.ofNat base2
  first : t.regs.r8=.ofNat base
  shift : t.regs.rcx=.ofNat (7-least%8)
  index : BitVec.extractLsb' 0 8 t.regs.rdx.toBitVec=BitVec.ofNat 8 (NodeInit.selector width least)
  ready : CallsReady c t
  frame : EqualOutside (Writes c a.regs.rsp base2) a.dmem t.dmem
  record : ∀ names : Names, Trie.decodeNode names.trie nodeOffsets t.dmem base2=
    .ok (Trie.targetNode (newNode key least width none))
  next : word t.dmem "node.list.next" (base2+56) 8=.ok (base2+56)
  prev : word t.dmem "node.list.prev" (base2+64) 8=.ok (base2+56)
  saved : word t.dmem "saved.node" (a.regs.rsp.toNat+24) 8=.ok base
  locals : ∀ offset size, offset+size≤48 → offset+size≤24 ∨ 32≤offset → ∀ path,
    word t.dmem path (a.regs.rsp.toNat+offset) size=word a.dmem path (a.regs.rsp.toNat+offset) size

theorem sub_range {p offset size total : Nat} {x : BitVec 64} (within : offset+size≤total)
    (inside : InRange (.ofNat 64 (p+offset)) size x) : InRange (.ofNat 64 p) total x := by
  obtain ⟨i,bound,equal⟩ := inside
  refine ⟨offset+i,by omega,?_⟩
  rw [equal]
  simp only [BitVec.ofNat_add,BitVec.add_assoc]

theorem internal_initialized (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch) (c : Context)
    {a : MachineData} {base base2 width cidr common key : Nat}
    (entry : Entry c a base base2 width cidr common key) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x31d ∧ Exit c a base base2 width (min cidr common) key t.data)
      ⟨a,Add.entry+0x292⟩ := by
  have stackWord (offset : Nat) : BitVec.ofNat 64 (a.regs.rsp.toNat+offset)=a.regs.rsp.toBitVec+.ofNat 64 offset := by
    rw [BitVec.ofNat_add,ofNat_uint64]
  have baseSmall : base<2^64 := by have := entry.firstExtent; omega
  have base2Small : base2<2^64 := by have := entry.extent; omega
  have baseNat : (BitVec.ofNat 64 base).toNat=base := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt baseSmall
  -- +0x292: reload the first node, keep the allocation
  have nonzero : a.regs.rax≠0 := by
    rw [entry.object]
    intro zero
    have := congrArg UInt64.toNat zero
    simp [Nat.mod_eq_of_lt base2Small] at this
    exact entry.nonzero this
  have firstLoad : a.dmem.loadInt (a.regs.rsp.toBitVec+24) 8=some ((BitVec.ofNat 64 base).toNat : Int) := by
    have read := word_loadInt _ _ _ _ _ entry.firstRead
    rw [stackWord] at read
    rw [baseNat]
    exact read
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r292_layout.agreement decoder.add) a _
      (entry_region a (.ofNat 64 base) nonzero firstLoad))
  rintro b1 ⟨pc1,mem1,regs1⟩
  rw [Placement.at_pc b1 _ pc1]
  -- +0x2a3: save it again, then the coverage call
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually ((AllowedipsLoop.layout_take Add_r2a3_layout 1).agreement decoder.add) b1.data _
      (save_region b1.data (by rw [mem1,regs1,firstLoad]; rfl)))
  rintro b2 ⟨pc2,mem2,regs2⟩
  let m2 := a.dmem.storeInt (.ofNat 64 (a.regs.rsp.toNat+24)) 8 (base : Nat)
  have memory2 : b2.data.dmem=m2 := by
    rw [mem2,mem1,regs1]
    simp only [m2]
    rw [store_nat64,stackWord]
    rfl
  have stack2 : b2.data.regs.rsp=a.regs.rsp := by rw [regs2,regs1]
  have frame2 : EqualOutside (InRange (.ofNat 64 (a.regs.rsp.toNat+24)) 8) a.dmem b2.data.dmem :=
    memory2 ▸ storeInt_frame _ _ _ _
  have ready2 : CallsReady c b2.data :=
    entry.ready.frame stack2 frame2 (memory2 ▸ MappedLe.store _ _ _ _) entry.stackContext
  have here := decoder.add _ _ (show Add.fetch (Add.entry+0x2a8)=some _ from rfl)
  rw [Placement.at_pc b2 _ pc2]
  apply eventually_trans (instructionStep fetch) _ _ _
    (Services.call fetch (Add.entry+0x2a8) "L_ffffffff810f31f0" .pc tracePc here c b2.data ready2)
  rintro b3 ⟨pc3,stack3,bx3,bp3,node3,common3,source3,bits3,ready3,frame3⟩
  rw [stack2] at stack3 frame3
  rw [regs2,regs1] at bx3 bp3 node3 common3 source3 bits3
  simp only at bx3 bp3 node3 common3 source3 bits3
  -- what the stack word's store and the call left alone
  have stackLow := entry.stackLow
  have stackHigh := entry.stackHigh
  have returnWord : a.regs.rsp.toBitVec-8=.ofNat 64 (a.regs.rsp.toNat-8) := by
    symm
    rw [BitVec.eq_sub_iff_add_eq,←ofNat_uint64,show (8 : BitVec 64)=BitVec.ofNat 64 8 from rfl,
      ←BitVec.ofNat_add]
    congr 1
    omega
  have frame13 := frame2.trans frame3
  have keep (address size : Nat)
      (apartStack : ∀ x, InRange (.ofNat 64 address) size x → ¬InRange (.ofNat 64 (a.regs.rsp.toNat-8)) 56 x)
      (apartCoverage : ∀ x, c.writes x → ¬InRange (.ofNat 64 address) size x) (path : String) :
      word b3.data.dmem path address size=word a.dmem path address size := by
    apply (Trie.word_frame frame13 path address size _).symm
    intro x inside written
    rcases written with saved|ret|coverage
    · apply apartStack x inside
      apply sub_range (offset:=32) (size:=8) (by decide)
      rw [show a.regs.rsp.toNat-8+32=a.regs.rsp.toNat+24 from by omega]
      exact saved
    · apply apartStack x inside
      apply sub_range (offset:=0) (size:=8) (by decide)
      rw [returnWord] at ret
      exact ret
    · exact apartCoverage x coverage inside
  have localCall (offset size : Nat) (within : offset+size≤48) :
      ∀ x, InRange (.ofNat 64 (a.regs.rsp.toNat+offset)) size x →
        ¬(InRange (a.regs.rsp.toBitVec-8) 8 x ∨ c.writes x) := by
    intro x inside written
    rcases written with ret|coverage
    · rw [returnWord] at ret
      rw [show a.regs.rsp.toNat+offset=a.regs.rsp.toNat-8+(8+offset) from by omega,BitVec.ofNat_add] at inside
      exact InRange.offset_disjoint (.ofNat 64 (a.regs.rsp.toNat-8)) (8+offset) size 0 8 (by omega) (by decide)
        (.inr (by omega)) x inside (by simpa using ret)
    · exact entry.stackCoverage x coverage (sub_range within inside)
  have keepLocal (offset size : Nat) (within : offset+size≤48) (apart : offset+size≤24 ∨ 32≤offset)
      (path : String) :
      word b3.data.dmem path (a.regs.rsp.toNat+offset) size=word a.dmem path (a.regs.rsp.toNat+offset) size := by
    apply (Trie.word_frame frame13 path _ size _).symm
    intro x inside written
    rcases written with saved|call
    · rw [BitVec.ofNat_add] at inside saved
      exact InRange.offset_disjoint (.ofNat 64 a.regs.rsp.toNat) offset size 24 8 (by omega) (by decide)
        (by omega) x inside saved
    · exact localCall offset size within x inside call
  have first3 : word b3.data.dmem "saved.node" (a.regs.rsp.toNat+24) 8=.ok base := by
    rw [←Trie.word_frame frame3 "saved.node" _ 8 (localCall 24 8 (by decide)),memory2]
    exact word_store_same _ _ _ _ _ (by omega) (by simpa using baseSmall)
  have cidr3 := (keepLocal 16 1 (by decide) (by decide) "saved.cidr").trans entry.cidrRead
  have mask3 := (keepLocal 36 1 (by decide) (by decide) "saved.mask").trans entry.maskRead
  have nodeKeep (offset size : Nat) (within : offset+size≤72) (path : String) :
      word b3.data.dmem path (base2+offset) size=word a.dmem path (base2+offset) size :=
    keep _ _ (fun x inside => entry.nodeStack x (sub_range within inside))
      (fun x coverage inside => entry.nodeCoverage x coverage (sub_range within inside)) path
  have zero3 (offset size : Nat) (within : offset+size≤72) (path : String) :
      word b3.data.dmem path (base2+offset) size=.ok 0 := by
    rw [nodeKeep offset size within]
    have full := Trie.readNat_loadInt entry.zero
    have part := MemoryBytes.loadInt_subword _ _ _ _ full offset size within
    apply Trie.word_of_loadInt _ (by have := entry.extent; omega)
    simpa [BitVec.ofNat_add] using part
  have keyKeep (offset size : Nat) (within : offset+size≤16) (path : String) :
      word b3.data.dmem path (base+32+offset) size=word a.dmem path (base+32+offset) size :=
    keep _ _ (fun x inside => entry.firstStack x (sub_range within inside))
      (fun x coverage inside => entry.firstCoverage x coverage (sub_range within inside)) path
  -- +0x2ad: the empty list head and min(cidr, common)
  have least : min cidr common≤width := Nat.le_trans (Nat.min_le_left _ _) entry.cidrBound
  have widthBound : width≤128 := by rcases entry.family with h|h <;> omega
  have r12Word : b3.data.regs.r12.toBitVec=.ofNat 64 base2 := by rw [node3,entry.object]; rfl
  have stackAt (offset : Nat) : b3.data.regs.rsp.toBitVec+.ofNat 64 offset=
      .ofNat 64 (a.regs.rsp.toNat+offset) := by rw [stack3,stackWord]
  have nodeAt (offset : Nat) : b3.data.regs.r12.toBitVec+.ofNat 64 offset=.ofNat 64 (base2+offset) := by
    rw [r12Word,BitVec.ofNat_add]
  have nodeMapped3 (offset size : Nat) (within : offset+size≤72) :
      (b3.data.dmem.loadInt (.ofNat 64 (base2+offset)) size).isSome=true := by
    rw [word_loadInt _ _ _ _ _ (zero3 offset size within "")]; rfl
  have s16 : b3.data.regs.rsp.toBitVec+16=.ofNat 64 (a.regs.rsp.toNat+16) := stackAt 16
  have s24 : b3.data.regs.rsp.toBitVec+24=.ofNat 64 (a.regs.rsp.toNat+24) := stackAt 24
  have n24 : b3.data.regs.r12.toBitVec+24=.ofNat 64 (base2+24) := nodeAt 24
  have n32 : b3.data.regs.r12.toBitVec+32=.ofNat 64 (base2+32) := nodeAt 32
  have n56 : b3.data.regs.r12.toBitVec+56=.ofNat 64 (base2+56) := nodeAt 56
  have n64 : b3.data.regs.r12.toBitVec+64=.ofNat 64 (base2+64) := nodeAt 64
  have listRun := list_region b3.data cidr common (.ofNat 64 base) (Nat.le_trans entry.cidrBound widthBound)
    (Nat.le_trans entry.commonBound widthBound) (by rw [common3]; exact entry.commonLow)
    (by rw [s16]; exact word_loadInt _ _ _ _ _ cidr3)
    (by rw [s24,baseNat]; exact word_loadInt _ _ _ _ _ first3)
    (by rw [n56]; exact nodeMapped3 56 8 (by decide))
    (by rw [n64]; exact storeInt_defined _ _ _ _ _ _ (nodeMapped3 64 8 (by decide)))
  rw [Placement.at_pc b3 _ pc3]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r2ad_layout.agreement decoder.add) b3.data _ listRun)
  rintro b4 ⟨pc4,mem4,x,lowX,regs4⟩
  let m4 := (b3.data.dmem.storeInt (.ofNat 64 (base2+56)) 8 (base2+56 : Nat)).storeInt
    (.ofNat 64 (base2+64)) 8 (base2+56 : Nat)
  have memory4 : b4.data.dmem=m4 := by
    rw [mem4]
    simp only [m4,listMemory]
    rw [store_nat64,store_nat64,n56,n64]
  have frame34 : EqualOutside (InRange (.ofNat 64 base2) 72) b3.data.dmem b4.data.dmem := by
    intro y outside
    rw [memory4]
    exact (storeInt_frame _ _ _ _ y (fun h => outside (sub_range (offset:=56) (by decide) h))).trans
      (storeInt_frame _ _ _ _ y (fun h => outside (sub_range (offset:=64) (by decide) h)))
  have mapped34 : MappedLe b3.data.dmem b4.data.dmem :=
    memory4 ▸ (MappedLe.store _ _ _ _).trans (MappedLe.store _ _ _ _)
  have localIn (offset size : Nat) (within : offset+size≤48) {y : BitVec 64}
      (inside : InRange (.ofNat 64 (a.regs.rsp.toNat+offset)) size y) :
      InRange (.ofNat 64 (a.regs.rsp.toNat-8)) 56 y := by
    rw [show a.regs.rsp.toNat+offset=a.regs.rsp.toNat-8+(8+offset) from by omega] at inside
    exact sub_range (by omega) inside
  have stack4 : b4.data.regs.rsp=a.regs.rsp := by rw [regs4]; exact stack3
  have mask4 : word b4.data.dmem "saved.mask" (a.regs.rsp.toNat+36) 1=.ok ((width/8-1)%8) := by
    rw [←Trie.word_frame frame34 _ _ 1
      (fun y inside node => entry.nodeStack y node (localIn 36 1 (by decide) inside))]
    exact mask3
  -- +0x2cf, +0x2e6: the packed header word
  have firstRun := pack_first b4.data x width (min cidr common) entry.family least lowX
    (by rw [regs4]) (by rw [regs4]) (by rw [regs4]; exact bits3.trans entry.bits)
    (by
      have read := word_loadInt _ _ _ _ _ mask4
      rw [stackWord] at read
      rw [stack4]
      exact read)
  rw [Placement.at_pc b4 _ pc4]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r2cf_layout.agreement decoder.add) b4.data _ firstRun)
  rintro b5 ⟨pc5,mem5,regs5⟩
  have secondRun := pack_second b5.data x (x.setWidth 64) width (min cidr common) entry.family least lowX
    (by rw [regs5]) (by rw [regs5]) (by rw [regs5]) (by rw [regs5]) (by rw [regs5])
    (by rw [regs5,regs4]; exact bp3.trans entry.bytes)
  rw [Placement.at_pc b5 _ pc5]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r2e6_layout.agreement decoder.add) b5.data _ secondRun)
  rintro b6 ⟨pc6,mem6,carry6,regs6⟩
  -- +0x2fb: the header store
  have wordReg : UInt64.ofNat (headerWord width (min cidr common))=
      UInt64.ofBitVec ((BitVec.ofNat 32 (headerWord width (min cidr common))).setWidth 64) := by
    rw [BitVec.setWidth_ofNat_of_le_of_lt (by decide) (header_bound entry.family least)]
    rfl
  have node6 : b6.data.regs.r12=b3.data.regs.r12 := by rw [regs6,regs5,regs4]
  have memory6 : b6.data.dmem=m4 := by rw [mem6,mem5,memory4]
  have storeRun := store_region b6.data (.ofNat 32 (headerWord width (min cidr common))) width entry.family
    carry6 (by rw [regs6]; exact wordReg)
    (by rw [node6,n24,memory6,←memory4]; exact mapped34 _ _ (nodeMapped3 24 4 (by decide)))
  rw [Placement.at_pc b6 _ pc6]
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r2fb_layout.agreement decoder.add) b6.data _ storeRun)
  rintro b7 ⟨pc7,mem7,regs7⟩
  let m7 := m4.storeInt (.ofNat 64 (base2+24)) 4 (headerWord width (min cidr common) : Nat)
  have memory7 : b7.data.dmem=m7 := by
    rw [mem7,node6,n24,memory6]
    simp only [m7]
    rw [store_nat32]
  -- the key copy, against the landed summary
  have r12_7 : b7.data.regs.r12=.ofNat base2 := by
    rw [regs7]; exact node6.trans (node3.trans entry.object)
  have r14_7 : b7.data.regs.r14=.ofNat (base+32) := by
    rw [regs7,regs6,regs5,regs4]; exact source3.trans entry.source
  have r8_7 : b7.data.regs.r8=.ofBitVec (.ofNat 64 base) := by rw [regs7,regs6,regs5,regs4]
  have rbp_7 : b7.data.regs.rbp=.ofNat (width/8) := by
    rw [regs7,regs6,regs5,regs4]; exact bp3.trans entry.bytes
  have rdi_7 : b7.data.regs.rdi.toBitVec=b7.data.regs.r12.toBitVec+32 := by rw [regs7]
  have source7 : b7.data.regs.r14.toBitVec=b7.data.regs.r8.toBitVec+32 := by
    rw [r14_7,r8_7]
    show BitVec.ofNat 64 (base+32)=BitVec.ofNat 64 base+BitVec.ofNat 64 32
    rw [BitVec.ofNat_add]
  let view := copyView b7.data width
  have viewBase : view.regs.rbx.toNat=base2 := by
    show b7.data.regs.r12.toNat=base2
    rw [r12_7]; exact Nat.mod_eq_of_lt base2Small
  have viewQuery : view.regs.r13.toNat=base+32 := by
    show b7.data.regs.r14.toNat=base+32
    rw [r14_7]; exact Nat.mod_eq_of_lt (by have := entry.firstExtent; omega)
  have viewBits : view.regs.rbp.toNat=width := Nat.mod_eq_of_lt (by omega)
  have frame37 : EqualOutside (InRange (.ofNat 64 base2) 72) b3.data.dmem b7.data.dmem := by
    intro y outside
    rw [memory7]
    exact (frame34 y outside).trans (by
      rw [memory4]
      exact storeInt_frame _ _ _ _ y (fun h => outside (sub_range (offset:=24) (by decide) h)))
  have mapped37 : MappedLe b3.data.dmem b7.data.dmem := by
    rw [memory7]
    exact (memory4 ▸ mapped34).trans (MappedLe.store _ _ _ _)
  have keyKeep7 (offset size : Nat) (within : offset+size≤16) (path : String) :
      word b7.data.dmem path (base+32+offset) size=word a.dmem path (base+32+offset) size := by
    rw [←Trie.word_frame frame37 path _ size (fun y inside node =>
      entry.nodeFirst y node (sub_range (p:=base) (offset:=32+offset) (size:=size) (total:=72) (by omega)
        (by rw [←Nat.add_assoc]; exact inside)))]
    exact keyKeep offset size within path
  have query7 : if width=32 then word b7.data.dmem "query" (base+32) 4=.ok key else
      ∃ hi lo, word b7.data.dmem "query.high" (base+32) 8=.ok hi ∧
        word b7.data.dmem "query.low" (base+32+8) 8=.ok lo ∧ key=hi*2^64+lo := by
    have firstKey := entry.firstKey
    by_cases four : width=32
    · rw [ite_eq_left four] at firstKey ⊢
      exact (keyKeep7 0 4 (by decide) "query").trans (word_path "query" firstKey)
    · rw [ite_eq_right four] at firstKey ⊢
      obtain ⟨hi,lo,high,low,keyEq⟩ := firstKey
      exact ⟨hi,lo,(keyKeep7 0 8 (by decide) "query.high").trans (word_path "query.high" high),
        (keyKeep7 8 8 (by decide) "query.low").trans (word_path "query.low" low),keyEq⟩
  obtain ⟨final,checked,mappedFinal⟩ := copy_total (s:=view) (memory:=b7.data.dmem)
    (by
      rw [viewBits,viewQuery]
      by_cases four : width=32
      · rw [ite_eq_left four] at query7 ⊢
        rw [word_loadInt _ _ _ _ _ query7]; rfl
      · rw [ite_eq_right four] at query7 ⊢
        obtain ⟨hi,lo,high,low,_⟩ := query7
        exact ⟨by rw [word_loadInt _ _ _ _ _ high]; rfl,by rw [word_loadInt _ _ _ _ _ low]; rfl⟩)
    (by
      intro offset size within
      rw [viewBase,Nat.add_assoc]
      exact mapped37 _ _ (nodeMapped3 (32+offset) size (by omega)))
  have copyRun := copy_checked fetch decoder entry.family rbp_7 rdi_7 source7 checked
  rw [Placement.at_pc b7 _ pc7]
  apply eventually_weaken (instructionStep fetch) _ _ _ _ copyRun
  rintro t ⟨pcT,memT,frameT⟩
  refine ⟨pcT,?_⟩
  -- the record
  have nodeWord4 (offset size : Nat) (within : offset+size≤56) (path : String) :
      word m4 path (base2+offset) size=.ok 0 := by
    simp only [m4]
    rw [word_store_frame _ path base2 offset size 64 8 _ (by have := entry.extent; omega) (by decide)
        (.inl (by omega)),
      word_store_frame _ path base2 offset size 56 8 _ (by have := entry.extent; omega) (by decide)
        (.inl within)]
    exact zero3 offset size (by omega) path
  have core (names : Names) := header_copy_peerless (names:=names) (s:=view) (before:=m4) (after:=final)
    (cidr:=min cidr common) (key:=key)
    (by rw [viewBits]; exact entry.family) (by rw [viewBits]; exact least)
    (by rw [viewBase]; exact entry.extent)
    (by rw [viewBase]; exact nodeWord4 0 8 (by decide) _)
    (by rw [viewBase]; exact nodeWord4 8 8 (by decide) _)
    (by rw [viewBase]; exact nodeWord4 16 8 (by decide) _)
    (by
      rw [viewBits,viewBase,viewQuery]
      show if width=32 then word m7 "query" (base+32) 4=.ok key else
        ∃ hi lo, word m7 "query.high" (base+32) 8=.ok hi ∧
          word m7 "query.low" (base+32+8) 8=.ok lo ∧ key=hi*2^64+lo
      rw [←memory7]
      exact query7)
    (by
      rw [viewBits,viewBase]
      have query : view.regs.r13.toBitVec=.ofNat 64 (base+32) := by
        show b7.data.regs.r14.toBitVec=_
        rw [r14_7]; rfl
      rw [query]
      intro y read written
      exact entry.nodeFirst y (sub_range (offset:=32) (by decide) written)
        (sub_range (p:=base) (offset:=32) (total:=72) (by split <;> decide) read))
    (by
      rw [viewBase,viewBits]
      show copy view m7=.ok final
      rw [←memory7]
      exact checked)
  have copyFrame : EqualOutside (InRange (.ofNat 64 (base2+32)) 16) b7.data.dmem final := by
    have frame := (core ⟨0,⟨[],[]⟩,0⟩).2
    rw [viewBase,viewBits] at frame
    rw [memory7]
    exact frame
  have frame3f : EqualOutside (InRange (.ofNat 64 base2) 72) b3.data.dmem final := by
    intro y outside
    exact (frame37 y outside).trans
      (copyFrame y (fun h => outside (sub_range (offset:=32) (by decide) h)))
  have stackT : t.data.regs.rsp=a.regs.rsp := by
    rw [frameT.stack,regs7,regs6,regs5]; exact stack4
  have extent := entry.extent
  have listApart (offset : Nat) (high : 48≤offset) (within : offset+8≤72) :
      ∀ y, InRange (.ofNat 64 (base2+offset)) 8 y → ¬InRange (.ofNat 64 (base2+32)) 16 y :=
    fun y inside written => InRange.offset_disjoint (.ofNat 64 base2) offset 8 32 16 (by omega) (by decide)
      (.inr (by omega)) y (by rw [←BitVec.ofNat_add]; exact inside) (by rw [←BitVec.ofNat_add]; exact written)
  exact {
    stack := stackT
    parent := by rw [frameT.parent,regs7,regs6,regs5,regs4]; exact bx3
    bytes := by rw [frameT.bytes,regs7,regs6,regs5,regs4]; exact bp3
    common := by rw [frameT.common,regs7,regs6,regs5,regs4]; exact common3
    source := by rw [frameT.source,regs7,regs6,regs5,regs4]; exact source3
    bits := by rw [frameT.bits,regs7,regs6,regs5,regs4]; exact bits3
    node := frameT.node.trans r12_7
    first := frameT.first.trans r8_7
    shift := by rw [frameT.shift,regs7,regs6]
    index := by rw [frameT.index,regs7,regs6,regs5]; exact low_byte_replace _ _
    ready := ready3.frame (stackT.trans stack3.symm) (memT ▸ frame3f)
      (memT ▸ mapped37.trans mappedFinal) entry.nodeContext
    frame := by
      intro y outside
      rw [memT]
      exact (frame13 y (fun h => outside (.inr h))).trans (frame3f y (fun h => outside (.inl h)))
    record := fun names => by
      have decoded := (core names).1
      rw [viewBase,viewBits] at decoded
      rw [memT]
      exact decoded
    next := by
      rw [memT,←Trie.word_frame copyFrame _ (base2+56) 8 (listApart 56 (by decide) (by decide)),memory7]
      simp only [m7,m4]
      rw [word_store_frame _ _ base2 56 8 24 4 _ (by omega) (by decide) (.inr (by decide)),
        word_store_frame _ _ base2 56 8 64 8 _ (by omega) (by decide) (.inl (by decide))]
      exact word_store_same _ _ _ _ _ (by omega) (by omega)
    prev := by
      rw [memT,←Trie.word_frame copyFrame _ (base2+64) 8 (listApart 64 (by decide) (by decide)),memory7]
      simp only [m7,m4]
      rw [word_store_frame _ _ base2 64 8 24 4 _ (by omega) (by decide) (.inr (by decide))]
      exact word_store_same _ _ _ _ _ (by omega) (by omega)
    saved := by
      rw [memT,←Trie.word_frame frame3f _ _ 8
        (fun y inside node => entry.nodeStack y node (localIn 24 8 (by decide) inside))]
      exact first3
    locals := by
      intro offset size within apart path
      rw [memT,←Trie.word_frame frame3f path _ size
        (fun y inside node => entry.nodeStack y node (localIn offset size within inside))]
      exact keepLocal offset size within apart path }

#print axioms internal_initialized

/-- `choose(node, down->bits)`: from `add+0x31d` to `add+0x338`, where the
connections begin. `down` is the node below, saved at `rsp`; `byte` is the
byte of its key at the internal node's byte selector. The memory is the one
`internal_initialized` left. -/
theorem internal_chosen (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    (tracePc : TrustBase.TracePcContract fetch) (c : Context)
    {a : MachineData} {base base2 width cidr common key down byte : Nat}
    (entry : Entry c a base base2 width cidr common key)
    (strict : min cidr common<width) (downExtent : down+72≤2^64)
    (downRead : word a.dmem "saved.down" a.regs.rsp.toNat 8=.ok down)
    (byteRead : word a.dmem "down.key" (down+32+NodeInit.selector width (min cidr common)) 1=.ok byte)
    (downApart : ∀ x, InRange (.ofNat 64 (down+32)) 16 x → ¬Writes c a.regs.rsp base2 x) :
    Eventually (instructionStep fetch) (fun u =>
      u.pc=Add.entry+0x338 ∧ ∃ t : MachineData,
        Exit c a base base2 width (min cidr common) key t ∧ u.data.dmem=t.dmem ∧
        u.data.regs={t.regs with
          rdi:=.ofNat down,
          rax:=.ofNat (AllowedipsChild.selected byte (7-min cidr common%8)),
          rdx:=.ofNat (AllowedipsChild.selected byte (7-min cidr common%8)),
          rcx:=.ofNat (AllowedipsChild.selected byte (7-min cidr common%8)+1)})
      ⟨a,Add.entry+0x292⟩ := by
  apply eventually_trans (instructionStep fetch) _ _ _ (internal_initialized fetch decoder tracePc c entry)
  rintro t ⟨pcT,exit⟩
  have widthBound : width≤128 := by rcases entry.family with h|h <;> omega
  have indexBound : NodeInit.selector width (min cidr common)<16 :=
    Nat.xor_lt_two_pow (n:=4) (by omega) (by omega)
  have downWord : word t.data.dmem "saved.down" a.regs.rsp.toNat 8=.ok down :=
    (exit.locals 0 8 (by decide) (.inl (by decide)) "saved.down").trans downRead
  have downLoad : t.data.dmem.loadInt t.data.regs.rsp.toBitVec 8=some ((BitVec.ofNat 64 down).toNat : Int) := by
    have read := word_loadInt _ _ _ _ _ downWord
    rw [ofNat_uint64] at read
    rw [exit.stack,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    exact read
  have byteWord : word t.data.dmem "down.key" (down+32+NodeInit.selector width (min cidr common)) 1=.ok byte := by
    rw [←Trie.word_frame exit.frame "down.key" _ 1
      (fun y inside => downApart y (sub_range (p:=down+32) (size:=1) (total:=16) (by omega) inside))]
    exact byteRead
  have byteLoad : t.data.dmem.loadInt
      (BitVec.ofNat 64 down+32+.ofNat 64 (NodeInit.selector width (min cidr common))) 1=some (byte : Int) := by
    have read := word_loadInt _ _ _ _ _ byteWord
    rw [BitVec.ofNat_add,BitVec.ofNat_add] at read
    exact read
  have run := choose_region t.data (.ofNat 64 down) _ (7-min cidr common%8) byte indexBound (by omega)
    (by simpa using word_bound byteWord) downLoad exit.index exit.shift byteLoad
  rw [Placement.at_pc t _ pcT]
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r31d_layout.agreement decoder.add) t.data _ run)
  rintro u ⟨pcU,memU,regsU⟩
  exact ⟨pcU,t.data,exit,memU,regsU⟩

#print axioms internal_chosen

end Binary.Pair.Allowedips.C1Internal
