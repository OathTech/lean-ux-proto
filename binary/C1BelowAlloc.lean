import C1BelowRollback
import AllowedipsPlacementRegions

/-! Result C1, work package 3: the second allocation (cases `split` and
`splitNoMem`), from the comparison after `common_bits` (`add+0x267`, the
new prefix strictly longer than the common prefix) through the saved node,
the coverage callback and the load of `node_cache` to the allocation
service, taken from the hypothesis `AllocRule`, and back at `add+0x292`. -/
namespace Binary.Statements.C1.Proof.Second
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage Binary.Instrumentation
open Binary.Statements.C1.Proof.Rollback
local instance : Labels := Image.linkedLabels

/-- `+0x267`: `cmp 0x10(%rsp),%r13b; mov 0x18(%rsp),%r8; jae +0x56d`. -/
theorem compare_step (s : MachineData) (cidr : BitVec 8) (base : BitVec 64)
    (cidrRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x10) 1=some cidr.toNat)
    (baseRead : s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some base.toNat) :
    (Placement.physical Add.r267 0x267 s).All (fun t =>
      t.data.regs={s.regs with r8 := .ofBitVec base} ∧ t.data.dmem=s.dmem ∧
      t.pc=if cidr.toNat ≤ (s.regs.get (.low .r13 .W8)).toNat
        then Add.entry+0x56d else Add.entry+0x277) := by
  simp [Placement.physical,Add.r267,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get64,Reg64s.set,Reg64s.set64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,
    StatusFlags.from_result,CondCode.interp,Allowedips.carry8] at cidrRead baseRead ⊢
  rw [cidrRead]
  simp only [Effects.All]
  rw [baseRead]
  simp only [Effects.All]
  have target : (label "L_ffffffff813a112d" : Int64)=Add.entry+0x56d := by decide +kernel
  have small : (cidr.toNat : Int) % 256=cidr.toNat := by have := cidr.isLt; omega
  simp only [small,Int.ofNat_le,target]
  split <;> simp_all [Effects.All,Add.entry,BitVec.ofInt_natCast]

/-- `+0x277`: `mov %r8,0x18(%rsp)`, up to the coverage call at `+0x27c`. -/
theorem save_step (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8).isSome=true) :
    (Placement.physical (Add.r277.take 1) 0x277 s).All (fun t =>
      t.pc=Add.entry+0x27c ∧ t.data.regs=s.regs ∧
      t.data.dmem=s.dmem.storeInt (s.regs.rsp.toBitVec+0x18) 8 s.regs.r8.toBitVec.toInt) := by
  obtain ⟨old,read⟩ := Option.isSome_iff_exists.mp mapped
  simp [Placement.physical,Add.r277,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get,Reg64s.get64,
    Reg.base,Reg.offset,BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at read ⊢
  rw [read]
  simp [Effects.All,Add.entry]

/-- `+0x281`: `mov node_cache(%rip),%rdi; mov $0xdc0,%esi`, up to the call at `+0x28d`. -/
theorem arguments_step (s : MachineData) (cache : Nat)
    (cacheRead : s.dmem.loadInt (.ofNat 64 cacheWord) 8 = some (cache : Int)) :
    (Placement.physical (Add.r281.take 2) 0x281 s).All (fun t =>
      t.pc=Add.entry+0x28d ∧ t.data.dmem=s.dmem ∧
      t.data.regs={s.regs with rdi := .ofNat cache, rsi := 0xdc0}) := by
  simp [Placement.physical,Add.r281,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.set,Reg64s.set64,
    BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at cacheRead ⊢
  have cacheAddress : BitVec.ofInt 64 ((Add.entry.toInt + 641 + 7).bmod 18446744073709551616) + 12824600#64 =
      BitVec.ofNat 64 cacheWord := by rfl
  rw [cacheAddress,cacheRead]
  simp only [Effects.All,BitVec.ofInt_natCast]
  constructor <;> first | trivial | rfl

#print axioms compare_step
#print axioms save_step
#print axioms arguments_step

variable {L : Layout} {A : Allocator} {c : Context} {s : MachineState} {family : Nat} {ra : UInt64}

/-- The local at `rsp+0x18` (the saved first node) is scratch. -/
theorem saved_scratch {a : MachineState} (facts : ReadyFacts L A c s family ra)
    (high : a.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toNat)
    (low : s.data.regs.rsp.toNat + 48 ≤ a.data.regs.rsp.toNat + insertWindow)
    {x : BitVec 64} (inside : InRange (a.data.regs.rsp.toBitVec + 0x18) 8 x) :
    Scratch s (insertWindow + A.depth) x := by
  obtain ⟨i,bound,at_⟩ := inside
  have window := window_bounds facts
  have size := a.data.regs.rsp.toBitVec.isLt
  have rsp : a.data.regs.rsp.toBitVec.toNat = a.data.regs.rsp.toNat := rfl
  have value := congrArg BitVec.toNat at_
  have offset : (0x18 : BitVec 64).toNat = 24 := rfl
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,rsp,offset] at value
  unfold insertWindow at low window ⊢
  apply scratch_nat <;> omega

/-- The saved node's local is apart from the return word below the stack pointer. -/
theorem saved_push_apart {rsp : UInt64} (room : rsp.toNat + 32 ≤ 2^64) (positive : 8 ≤ rsp.toNat)
    {x : BitVec 64} (inside : InRange (rsp.toBitVec + 0x18) 8 x) : ¬InRange (rsp.toBitVec - 8) 8 x := by
  obtain ⟨i,bound,at_⟩ := inside
  rintro ⟨j,other,equal⟩
  have raw := congrArg BitVec.toNat (at_.symm.trans equal)
  have value : rsp.toBitVec.toNat = rsp.toNat := rfl
  have eight : (8 : BitVec 64).toNat = 8 := rfl
  have offset : (0x18 : BitVec 64).toNat = 24 := rfl
  simp only [BitVec.toNat_add,BitVec.toNat_sub,BitVec.toNat_ofNat,eight,value,offset] at raw
  omega

/-- `add+0x267` (the new prefix longer than the common prefix) to the first
instruction of the allocation service. -/
theorem to_alloc (fetch : Int64 → Option Decoded)
    (mutation : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (c : Context) (a : MachineData) (cidr : BitVec 8) (base : BitVec 64) (cache : Nat)
    (ready : CallsReady c a)
    (cidrRead : a.dmem.loadInt (a.regs.rsp.toBitVec+0x10) 1 = some cidr.toNat)
    (baseRead : a.dmem.loadInt (a.regs.rsp.toBitVec+0x18) 8 = some base.toNat)
    (shorter : (a.regs.get (.low .r13 .W8)).toNat < cidr.toNat)
    (cacheRead : a.dmem.loadInt (.ofNat 64 cacheWord) 8 = some (cache : Int))
    (localContext : ∀ x, c.bytes x → ¬InRange (a.regs.rsp.toBitVec+0x18) 8 x)
    (cacheApart : ∀ x, InRange (.ofNat 64 cacheWord) 8 x →
      ¬(InRange (a.regs.rsp.toBitVec+0x18) 8 x ∨ InRange (a.regs.rsp.toBitVec-8) 8 x ∨ c.writes x)) :
    Eventually (instructionStep fetch) (fun e => ∃ v,
      EqualOutside (fun x => InRange (a.regs.rsp.toBitVec - 8) 8 x ∨ c.writes x)
        (a.dmem.storeInt (a.regs.rsp.toBitVec+0x18) 8 base.toInt) v.dmem ∧
      CallsReady c v ∧ v.regs.rsp = a.regs.rsp ∧ v.regs.rbx = a.regs.rbx ∧ v.regs.rbp = a.regs.rbp ∧
      v.regs.r12 = a.regs.r12 ∧ v.regs.r13 = a.regs.r13 ∧ v.regs.r14 = a.regs.r14 ∧ v.regs.r15 = a.regs.r15 ∧
      v.regs.rdi = .ofNat cache ∧ v.regs.rsi = 0xdc0 ∧
      e = calledState v (Add.entry + 0x292) (label "L_ffffffff81196d20")) ⟨a, Add.entry + 0x267⟩ := by
  -- the comparison: not taken
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r267_layout.agreement mutation.add) a _ (compare_step a cidr base cidrRead baseRead))
  rintro ⟨b0,pc0⟩ ⟨regs0,mem0,pcEq⟩
  simp only at pcEq mem0 regs0
  simp only [Nat.not_le.mpr shorter,↓reduceIte] at pcEq
  subst pcEq
  -- save the first node
  have layout277 : LaidOut Add.fetch (Add.entry + 0x277) (Add.r277.take 1) := by binary_layout
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (layout277.agreement mutation.add) b0 _
      (save_step b0 (by rw [mem0,regs0]; exact Option.isSome_of_eq_some baseRead)))
  rintro ⟨b,pcB⟩ ⟨pcEq,regsB,memB⟩
  simp only at pcEq memB regsB
  subst pcEq
  rw [mem0,regs0] at memB
  rw [regs0] at regsB
  simp only at memB
  have stackB : b.regs.rsp = a.regs.rsp := by rw [regsB]
  have readyB : CallsReady c b := ready.frame stackB (memB ▸ storeInt_frame a.dmem _ 8 _)
    (memB ▸ MappedLe.store a.dmem _ 8 _) localContext
  -- the coverage callback
  have here := mutation.add _ _ (show Add.fetch (Add.entry + 0x27c) = some _ from rfl)
  apply eventually_trans (instructionStep fetch) _ _ _
    (Services.call fetch (Add.entry + 0x27c) "L_ffffffff810f31f0" .pc tracePc here c b readyB)
  rintro ⟨t,pcT⟩ ⟨pcEq,stackT,bxT,bpT,r12T,r13T,r14T,r15T,readyT,frameT⟩
  simp only at pcEq stackT bxT bpT r12T r13T r14T r15T readyT frameT
  subst pcEq
  rw [stackB] at stackT frameT
  rw [memB] at frameT
  have cacheT : t.dmem.loadInt (.ofNat 64 cacheWord) 8 = some (cache : Int) := by
    rw [←frameT.loadInt (.ofNat 64 cacheWord) 8 (fun i bound written =>
      cacheApart _ ⟨i,bound,rfl⟩ (.inr written))]
    rw [←(storeInt_frame a.dmem (a.regs.rsp.toBitVec+0x18) 8 _).loadInt (.ofNat 64 cacheWord) 8
      (fun i bound written => cacheApart _ ⟨i,bound,rfl⟩ (.inl written))]
    exact cacheRead
  -- the arguments
  have layout281 : LaidOut Add.fetch (Add.entry + 0x281) (Add.r281.take 2) := by binary_layout
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (layout281.agreement mutation.add) t _ (arguments_step t cache cacheT))
  rintro ⟨v,pcV⟩ ⟨pcEq,memV,regsV⟩
  simp only at pcEq memV regsV
  subst pcEq
  have stackV : v.regs.rsp = t.regs.rsp := by rw [regsV]
  have readyV : CallsReady c v := readyT.congr memV stackV
  -- the call
  have call := mutation.add _ _ (show Add.fetch (Add.entry + 0x28d) = some _ from rfl)
  apply Sequential.forget
    (historySteps_eventually fetch _ _ _
      (call_instruction fetch (Add.entry + 0x28d) "L_ffffffff81196d20" call v [] readyV.mapped))
  rintro e ⟨machine,_⟩
  refine ⟨v,memV ▸ frameT,readyV,stackV.trans stackT,?_,?_,?_,?_,?_,?_,by rw [regsV],by rw [regsV],?_⟩
  · rw [regsV]; exact bxT.trans (by rw [regsB])
  · rw [regsV]; exact bpT.trans (by rw [regsB])
  · rw [regsV]; exact r12T.trans (by rw [regsB])
  · rw [regsV]; exact r13T.trans (by rw [regsB])
  · rw [regsV]; exact r14T.trans (by rw [regsB])
  · rw [regsV]; exact r15T.trans (by rw [regsB])
  · rw [machine]
    rfl

#print axioms to_alloc

/-- THE SECOND ALLOCATION. From `add+0x267` with the common prefix strictly
shorter than the new prefix: the first node is saved, the allocation
service is called with `node_cache` and `GFP_KERNEL | __GFP_ZERO`, and the
machine is back at `add+0x292` with the service's result (`AllocResult` for
the pending record of site 79), still in flight, the callee-saved registers
and every guarded byte as the coverage callback left them (`covered`). -/
theorem second_allocation (alloc : AllocRule) (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator)
    (premises : Premises fetch L A) (c : Context) (s a : MachineState)
    (family key cidr pid : Nat) (ra : UInt64) (live : List Nat)
    (record : HiddenRecord) (stream : List HiddenRecord) (bound : BitVec 8) (base : BitVec 64)
    (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (apart : spansApart (objectsOf L) L.arena = true) (arena : ∀ node ∈ live, InArena L node)
    (pc : a.pc = Add.entry + 0x267)
    (flight : InFlight L A c s a)
    (high : a.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toNat)
    (low : s.data.regs.rsp.toNat + 48 ≤ a.data.regs.rsp.toNat + insertWindow)
    (calls : CallsReady c a.data)
    (boundRead : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec+0x10) 1 = some bound.toNat)
    (baseRead : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec+0x18) 8 = some base.toNat)
    (shorter : (a.data.regs.get (.low .r13 .W8)).toNat < bound.toNat)
    (site : record.site = 79)
    (idle : A.Idle a.data.dmem live (record :: stream)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc = Add.entry + 0x292 ∧ t.data.regs.rsp = a.data.regs.rsp ∧
      t.data.regs.rbx = a.data.regs.rbx ∧ t.data.regs.rbp = a.data.regs.rbp ∧
      t.data.regs.r12 = a.data.regs.r12 ∧ t.data.regs.r13 = a.data.regs.r13 ∧
      t.data.regs.r14 = a.data.regs.r14 ∧ t.data.regs.r15 = a.data.regs.r15 ∧
      AllocResult L A live record stream t ∧ InFlight L A c s t ∧ CallsReady c t.data ∧
      ∃ covered,
        EqualOutside (fun y => InRange (a.data.regs.rsp.toBitVec - 8) 8 y ∨ c.writes y)
          (a.data.dmem.storeInt (a.data.regs.rsp.toBitVec+0x18) 8 base.toInt) covered ∧
        ∀ y, Guarded L s a live y → t.data.dmem.get? y = covered.get? y) a := by
  have facts := ready_facts ready
  have window := window_bounds facts
  have pushed := pushed_rsp facts low
  have savedWindow {x : BitVec 64} (inside : InRange (a.data.regs.rsp.toBitVec+0x18) 8 x) : Window A s x :=
    scratch_window (saved_scratch facts high low inside)
  have pushWindow {x : BitVec 64} (inside : InRange (a.data.regs.rsp.toBitVec-8) 8 x) : Window A s x :=
    scratch_window (words_scratch facts high low (words_push inside))
  have cacheRead := Trie.readNat_loadInt (facts.cache_read flight)
  have cacheSmall : L.cache < 2^64 := by
    have bound := (loadInt_range _ _ _ _ cacheRead).2
    omega
  have entry := eventually_flight (to_alloc fetch premises.insertion premises.tracePc c a.data bound base L.cache
    calls boundRead baseRead shorter cacheRead
    (fun x read inside => facts.bytes_window read (savedWindow inside))
    (fun x cache touched => by
      rcases touched with saved | push | covered
      · exact facts.scratch_cache (saved_scratch facts high low saved) cache
      · exact facts.scratch_cache (words_scratch facts high low (words_push push)) cache
      · exact facts.writes_cache covered cache))
  apply start_at pc
  apply eventually_trans (instructionStep fetch) _ _ _ entry
  rintro e ⟨⟨v,frameC,readyV,stackV,bxV,bpV,r12V,r13V,r14V,r15V,rdiV,rsiV,rfl⟩,mappedE,flagE⟩
  generalize site' : calledState v (Add.entry + 0x292) (label "L_ffffffff81196d20") = e at mappedE flagE ⊢
  have rspE : e.data.regs.rsp = a.data.regs.rsp - 8 := by rw [←site',←stackV]; rfl
  have memE : e.data.dmem = v.dmem.storeInt (a.data.regs.rsp.toBitVec - 8) 8 (Add.entry + 0x292).toBitVec.toInt := by
    rw [←site',←stackV]; rfl
  have frameE : EqualOutside (fun x => InRange (a.data.regs.rsp.toBitVec+0x18) 8 x ∨
      InRange (a.data.regs.rsp.toBitVec-8) 8 x ∨ c.writes x) a.data.dmem e.data.dmem := by
    intro x outside
    rw [memE]
    exact ((storeInt_frame _ _ 8 _ x (fun h => outside (.inl h))).trans
      (frameC x (fun h => outside (.inr h)))).trans
      (storeInt_frame _ _ 8 _ x (fun h => outside (.inr (.inl h))))
  have ready' := called_ready c v (Add.entry + 0x292) (label "L_ffffffff81196d20") readyV
  rw [site'] at ready'
  have flightE : InFlight L A c s e := flight.later _ (by rw [rspE]; omega) (by rw [rspE]; omega) frameE
    (fun x written => by
      rcases written with saved | push | covered
      · exact .inl (saved_scratch facts high low saved)
      · exact .inl (words_scratch facts high low (words_push push))
      · exact .inr (.inl covered))
    mappedE flagE ready'.2
  have idleE : A.Idle e.data.dmem live (record :: stream) :=
    premises.allocator.frame _ _ live _ idle (fun x inArena _ => frameE x (fun written => by
      rcases written with saved | push | covered
      · exact facts.heap_window (arena_heap inArena) (savedWindow saved)
      · exact facts.heap_window (arena_heap inArena) (pushWindow push)
      · exact facts.heap_writes (arena_heap inArena) covered))
  have rdiE : e.data.regs.rdi.toNat = L.cache := by
    rw [←site']
    change v.regs.rdi.toNat = L.cache
    rw [rdiV,UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt cacheSmall
  have rsiE : e.data.regs.get (.low .rsi .W32) = 0xdc0#32 := by
    rw [←site']
    change v.regs.get (.low .rsi .W32) = 0xdc0#32
    simp only [Reg64s.get,Reg64s.get64,rsiV]
    rfl
  have pcE : e.pc = allocEntry := by rw [←site']; rfl
  have served := eventually_flight (alloc fetch L A premises c s e family key cidr pid ra
    (Add.entry + 0x292).toUInt64 live record stream ready apart arena flightE (by rw [rspE]; omega) pcE ready'.1
    rdiE rsiE (by rw [site]; exact List.mem_cons_of_mem _ List.mem_cons_self) idleE)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ served
  rintro t ⟨⟨returned,result,flightT,kept⟩,mappedT,flagT⟩
  obtain ⟨pcT,stackT,bxT,bpT,r12T,r13T,r14T,r15T⟩ := returned
  have stackT : t.data.regs.rsp = a.data.regs.rsp := by
    rw [stackT,rspE]; exact UInt64.sub_add_cancel _ _
  have regE (f : Reg64s → UInt64) (same : f (calledState v (Add.entry + 0x292) (label "L_ffffffff81196d20")).data.regs = f v.regs) :
      f e.data.regs = f v.regs := by rw [←site']; exact same
  refine ⟨pcT,stackT,?_,?_,?_,?_,?_,?_,result,flightT,?_,v.dmem,frameC,?_⟩
  · exact bxT.trans ((regE (·.rbx) rfl).trans bxV)
  · exact bpT.trans ((regE (·.rbp) rfl).trans bpV)
  · exact r12T.trans ((regE (·.r12) rfl).trans r12V)
  · exact r13T.trans ((regE (·.r13) rfl).trans r13V)
  · exact r14T.trans ((regE (·.r14) rfl).trans r14V)
  · exact r15T.trans ((regE (·.r15) rfl).trans r15V)
  · exact {
      state := flightT.coverage
      aligned := by rw [stackT]; exact calls.aligned
      mapped := by rw [stackT]; exact mappedT _ _ (mappedE _ _ calls.mapped)
      pushSeparate := by rw [stackT]; exact calls.pushSeparate
      returnSeparate := by rw [stackT]; exact calls.returnSeparate
      metadataSeparate := calls.metadataSeparate
      preemptSeparate := calls.preemptSeparate }
  · intro y guarded
    have notPush : ¬InRange (a.data.regs.rsp.toBitVec - 8) 8 y := by
      rcases guarded with stack | ⟨span,fixed,inside⟩ | keptNode | cache
      · exact above_push (by omega) (by omega) stack
      · exact fun push => facts.heap_window ⟨span,List.mem_append_left _ fixed,inside⟩ (pushWindow push)
      · exact fun push => facts.heap_window (arena_heap (kept_arena arena keptNode)) (pushWindow push)
      · exact fun push => facts.scratch_cache (words_scratch facts high low (words_push push)) cache
    have covers : Protected L s e live y := by
      rcases guarded with stack | fixed | keptNode | cache
      · left
        have size : s.data.regs.rsp.toNat + 8 - e.data.regs.rsp.toNat =
            s.data.regs.rsp.toNat + 8 - a.data.regs.rsp.toNat + 8 := by rw [rspE]; omega
        rw [size,rspE]
        exact range_below stack
      · exact .inr (.inl fixed)
      · exact .inr (.inr (.inl keptNode))
      · exact .inr (.inr (.inr cache))
    rw [kept y covers,memE]
    exact (storeInt_frame _ _ 8 _ y notPush).symm

#print axioms second_allocation
end Binary.Statements.C1.Proof.Second
