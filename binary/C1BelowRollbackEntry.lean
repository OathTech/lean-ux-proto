import C1BelowRollbackRegions
import C1BelowRollbackStack
import PairServiceCall
import AllowedipsStackReady

/-! Result C1, work package 3, rollback path: from the second allocation's
NULL return (`add+0x292`) to the entry of the release service, by executed
instructions: the reload and branch, the saved node, the coverage callback,
`list_del` on the node's list words, and the call. Hypotheses are facts
about the starting state. -/
namespace Binary.Statements.C1.Proof.Rollback
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage Binary.Instrumentation
local instance : Labels := Image.linkedLabels

/-- The memory after the two poison stores of `list_del`. -/
def poisoned (m : DataMem) (base : Nat) : DataMem :=
  (m.storeInt (.ofNat 64 base + 56) 8 (0xdead000000000100#64).toInt).storeInt
    (.ofNat 64 base + 64) 8 (0xdead000000000122#64).toInt

/-- The bytes `list_del(&node->peer_list)` writes: the neighbours' links and the node's two list words. -/
def ListWrites (base next prev : Nat) (x : BitVec 64) : Prop :=
  (InRange (.ofNat 64 next + 8) 8 x ∨ InRange (.ofNat 64 prev) 8 x) ∨
  (InRange (.ofNat 64 base + 56) 8 x ∨ InRange (.ofNat 64 base + 64) 8 x)

theorem released_frame (m : DataMem) (base next prev : Nat) :
    EqualOutside (ListWrites base next prev) m (poisoned (unlinked m next prev) base) :=
  ((storeInt_frame m _ 8 _).trans (storeInt_frame _ _ 8 _)).trans
    ((storeInt_frame _ _ 8 _).trans (storeInt_frame _ _ 8 _))

theorem released_mapped (m : DataMem) (base next prev : Nat) :
    MappedLe m (poisoned (unlinked m next prev) base) :=
  ((MappedLe.store m _ 8 _).trans (MappedLe.store _ _ 8 _)).trans
    ((MappedLe.store _ _ 8 _).trans (MappedLe.store _ _ 8 _))

/-- The bytes the rollback reads after the coverage callback, other than its own stack local. -/
def Reads (base next prev : Nat) (x : BitVec 64) : Prop :=
  InRange (.ofNat 64 cacheWord) 8 x ∨ ListWrites base next prev x

/-- `add+0x292` to the first instruction of the release service. -/
theorem to_free (fetch : Int64 → Option Decoded)
    (mutation : AllowedipsMutationDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (c : Context) (a : MachineData) (base cache next prev : Nat)
    (ready : CallsReady c a)
    (rax : a.regs.rax = 0)
    (baseRead : a.dmem.loadInt (a.regs.rsp.toBitVec + 24) 8 = some (base : Int))
    (localMapped : (a.dmem.loadInt a.regs.rsp.toBitVec 8).isSome = true)
    (cacheRead : a.dmem.loadInt (.ofNat 64 cacheWord) 8 = some (cache : Int))
    (nextRead : a.dmem.loadInt (.ofNat 64 base + 56) 8 = some (next : Int))
    (prevRead : a.dmem.loadInt (.ofNat 64 base + 64) 8 = some (prev : Int))
    (nextMapped : (a.dmem.loadInt (.ofNat 64 next + 8) 8).isSome = true)
    (prevMapped : (a.dmem.loadInt (.ofNat 64 prev) 8).isSome = true)
    (localContext : ∀ x, c.bytes x → ¬InRange a.regs.rsp.toBitVec 8 x)
    (localWrites : ∀ x, InRange a.regs.rsp.toBitVec 8 x → ¬c.writes x)
    (readsApart : ∀ x, Reads base next prev x → ¬(Words a.regs.rsp x ∨ c.writes x))
    (listContext : ∀ x, c.bytes x → ¬ListWrites base next prev x) :
    Eventually (instructionStep fetch) (fun e => ∃ covered v,
      EqualOutside (fun x => InRange (a.regs.rsp.toBitVec - 8) 8 x ∨ c.writes x)
        (a.dmem.storeInt a.regs.rsp.toBitVec 8 (UInt64.ofNat base).toBitVec.toInt) covered ∧
      CallsReady c v ∧ v.regs.rsp = a.regs.rsp ∧
      v.dmem = poisoned (unlinked covered next prev) base ∧
      v.regs.rdi = .ofNat cache ∧ v.regs.rsi = .ofNat base ∧
      e = calledState v (Add.entry + 0x692) (label "L_ffffffff81199b10")) ⟨a, Add.entry + 0x292⟩ := by
  -- reload, branch, save
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r292_layout.agreement mutation.add) a _ (region292 a base rax baseRead))
  rintro ⟨b0,pc0⟩ ⟨pcEq,mem0,regs0⟩
  simp only at pcEq mem0 regs0
  subst pcEq
  have layout651 : LaidOut Add.fetch (Add.entry + 0x651) (Add.r651.take 1) := by binary_layout
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (layout651.agreement mutation.add) b0 _
      (region651 b0 (by rw [mem0,regs0]; exact localMapped)))
  rintro ⟨b,pcB⟩ ⟨pcEq,memB,regsB⟩
  simp only at pcEq memB regsB
  subst pcEq
  rw [mem0,regs0] at memB
  rw [regs0] at regsB
  simp only at memB
  have stackB : b.regs.rsp = a.regs.rsp := by rw [regsB]
  have readyB : CallsReady c b := ready.frame stackB (memB ▸ storeInt_frame a.dmem _ 8 _)
    (memB ▸ MappedLe.store a.dmem _ 8 _) localContext
  -- the coverage callback
  have here := mutation.add _ _ (show Add.fetch (Add.entry + 0x655) = some _ from rfl)
  apply eventually_trans (instructionStep fetch) _ _ _
    (Services.call fetch (Add.entry + 0x655) "L_ffffffff810f31f0" .pc tracePc here c b readyB)
  rintro ⟨t,pcT⟩ ⟨pcEq,stackT,_,_,_,_,_,_,readyT,frameT⟩
  simp only at pcEq stackT readyT frameT
  subst pcEq
  rw [stackB] at stackT frameT
  rw [memB] at frameT
  -- reads after the callback
  have baseBound : base < 2^64 := by
    have bound := (loadInt_range _ _ _ _ baseRead).2
    omega
  have far (address : BitVec 64) (size : Nat)
      (inside : ∀ i < size, Reads base next prev (address + .ofNat 64 i)) :
      t.dmem.loadInt address size = a.dmem.loadInt address size := by
    rw [←frameT.loadInt address size (fun i bound written =>
      readsApart _ (inside i bound) (written.elim (fun h => .inl (words_push h)) .inr))]
    exact ((storeInt_frame a.dmem a.regs.rsp.toBitVec 8 _).loadInt address size (fun i bound written =>
      readsApart _ (inside i bound) (.inl (words_local written)))).symm
  have baseT : t.dmem.loadInt t.regs.rsp.toBitVec 8 = some (base : Int) := by
    rw [stackT,←frameT.loadInt a.regs.rsp.toBitVec 8 (fun i bound written =>
      written.elim (local_push_apart ⟨i,bound,rfl⟩) (localWrites _ ⟨i,bound,rfl⟩)),load64_store]
    simp only [UInt64.toBitVec_ofNat',BitVec.toNat_ofNat,Nat.mod_eq_of_lt baseBound]
  have cacheT : t.dmem.loadInt (.ofNat 64 cacheWord) 8 = some (cache : Int) := by
    rw [far _ 8 (fun i bound => .inl ⟨i,bound,rfl⟩)]; exact cacheRead
  have prevT : t.dmem.loadInt (.ofNat 64 base + 64) 8 = some (prev : Int) := by
    rw [far _ 8 (fun i bound => .inr (.inr (.inr ⟨i,bound,rfl⟩)))]; exact prevRead
  have nextT : t.dmem.loadInt (.ofNat 64 base + 56) 8 = some (next : Int) := by
    rw [far _ 8 (fun i bound => .inr (.inr (.inl ⟨i,bound,rfl⟩)))]; exact nextRead
  have firstT : (t.dmem.loadInt (.ofNat 64 next + 8) 8).isSome = true := by
    rw [far _ 8 (fun i bound => .inr (.inl (.inl ⟨i,bound,rfl⟩)))]; exact nextMapped
  have secondT : (t.dmem.loadInt (.ofNat 64 prev) 8).isSome = true := by
    rw [far _ 8 (fun i bound => .inr (.inl (.inr ⟨i,bound,rfl⟩)))]; exact prevMapped
  -- unlink
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (Add_r65a_layout.agreement mutation.add) t _
      (region65a t base cache next prev baseT cacheT prevT nextT firstT (storeInt_defined _ _ _ _ _ _ secondT)))
  rintro ⟨u,pcU⟩ ⟨pcEq,memU,regsU⟩
  simp only at pcEq memU regsU
  subst pcEq
  -- poison
  have baseWord : u.regs.r8.toBitVec = BitVec.ofNat 64 base := by
    rw [regsU]; exact UInt64.toBitVec_ofNat' ..
  have layout681 : LaidOut Add.fetch (Add.entry + 0x681) (Add.r681.take 3) := by binary_layout
  have nodeNext : (u.dmem.loadInt (u.regs.r8.toBitVec + 56) 8).isSome = true := by
    rw [baseWord,memU]
    exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ (nextT ▸ rfl))
  have nodePrev : (u.dmem.loadInt (u.regs.r8.toBitVec + 64) 8).isSome = true := by
    rw [baseWord,memU]
    exact storeInt_defined _ _ _ _ _ _ (storeInt_defined _ _ _ _ _ _ (prevT ▸ rfl))
  apply eventually_trans (instructionStep fetch) _ _ _
    (region_eventually (layout681.agreement mutation.add) u _
      (region681 u (by rw [regsU]) nodeNext (storeInt_defined _ _ _ _ _ _ nodePrev)))
  rintro ⟨v,pcV⟩ ⟨pcEq,memV,regsV⟩
  simp only at pcEq memV regsV
  subst pcEq
  rw [baseWord,memU] at memV
  have memV : v.dmem = poisoned (unlinked t.dmem next prev) base := memV
  have stackV : v.regs.rsp = t.regs.rsp := by rw [regsV,regsU]
  have readyV : CallsReady c v := readyT.frame stackV (memV ▸ released_frame t.dmem base next prev)
    (memV ▸ released_mapped t.dmem base next prev) listContext
  -- the call
  have call := mutation.add _ _ (show Add.fetch (Add.entry + 0x68d) = some _ from rfl)
  apply Sequential.forget
    (historySteps_eventually fetch _ _ _
      (call_instruction fetch (Add.entry + 0x68d) "L_ffffffff81199b10" call v [] readyV.mapped))
  rintro e ⟨machine,_⟩
  refine ⟨t.dmem,v,frameT,readyV,stackV.trans stackT,memV,by rw [regsV,regsU],by rw [regsV,regsU],?_⟩
  rw [machine]
  rfl

#print axioms to_free
end Binary.Statements.C1.Proof.Rollback
