import C1ServiceStubRun
import MemoryBytes

/-! Result C1, work package 4: the stub meets `AllocatorContract` as stated.

The one byte the stub changes has unmapped neighbours, so no read of two or
more bytes (every read of a coverage context, the return word) can contain
it: that is all the `alloc` clause's `c.At` needs. -/
namespace Binary.Statements.C1.Stub
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Statements.C1.Proof
local instance : Labels := Image.linkedLabels

/-! ## A byte with unmapped neighbours -/

/-- A mapped read of at least two bytes does not contain a byte whose two
neighbours are unmapped. -/
theorem read_apart {m : Mem 64} {a b : BitVec 64} {n : Nat}
    (before : m.get? (a - 1#64) = none) (after : m.get? (a + 1#64) = none) (wide : 2 ≤ n)
    (mapped : (m.loadInt b n).isSome = true) : ∀ i < n, ¬InRange a 1 (b + .ofNat 64 i) := by
  rintro i bound ⟨j,small,equal⟩
  have zero : j = 0 := by omega
  subst zero
  have here : b + .ofNat 64 i = a := by simpa using equal
  have bytes := (loadInt_defined m b n).mp mapped
  by_cases last : i + 1 < n
  · have next := bytes (i+1) last
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, here] at next
    rw [show BitVec.ofNat 64 1 = 1#64 from rfl, after] at next
    cases next
  · have previous := bytes (i-1) (by omega)
    have back : b + .ofNat 64 (i-1) = a - 1#64 := by
      rw [← here]
      have split : BitVec.ofNat 64 i = BitVec.ofNat 64 (i-1) + 1#64 := by
        rw [show (1#64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
        congr 1
        omega
      rw [split, ← BitVec.add_assoc, BitVec.add_sub_cancel]
    rw [back, before] at previous
    cases previous

/-- Such a read is unchanged by a store to that byte. -/
theorem read_kept {m : Mem 64} {a b : BitVec 64} {n : Nat} (v : Int)
    (before : m.get? (a - 1#64) = none) (after : m.get? (a + 1#64) = none) (wide : 2 ≤ n)
    (mapped : (m.loadInt b n).isSome = true) :
    (m.storeInt a 1 v).loadInt b n = m.loadInt b n :=
  ((storeInt_frame m a 1 v).loadInt b n (read_apart before after wide mapped)).symm

private theorem load32_kept {m : Mem 64} {a b : BitVec 64} (v : Int) {value : BitVec 32}
    (before : m.get? (a - 1#64) = none) (after : m.get? (a + 1#64) = none)
    (read : load32 m b = some value) : load32 (m.storeInt a 1 v) b = some value := by
  unfold load32 at read ⊢
  rw [read_kept v before after (by decide) (by
    cases loaded : m.loadInt b 4 with
    | none => simp [loaded] at read
    | some _ => rfl)]
  exact read

private theorem load64_kept {m : Mem 64} {a b : BitVec 64} (v : Int) {value : BitVec 64}
    (before : m.get? (a - 1#64) = none) (after : m.get? (a + 1#64) = none)
    (read : load64 m b = some value) : load64 (m.storeInt a 1 v) b = some value := by
  unfold load64 at read ⊢
  rw [read_kept v before after (by decide) (by
    cases loaded : m.loadInt b 8 with
    | none => simp [loaded] at read
    | some _ => rfl)]
  exact read

/-- Every coverage context valid before a store to such a byte is valid after it. -/
theorem coverage_kept {c : Context} {m : Mem 64} {a : BitVec 64} (v : Int)
    (before : m.get? (a - 1#64) = none) (after : m.get? (a + 1#64) = none) (valid : c.At m) :
    c.At (m.storeInt a 1 v) := by
  obtain ⟨⟨task,soft,mode,buffer⟩,count⟩ := valid
  refine ⟨⟨load64_kept v before after task,fun read => load32_kept v before after (soft read),
    fun read => load32_kept v before after (mode read),fun needed => ?_⟩,load32_kept v before after count⟩
  obtain ⟨capacity,area,words,fill,bound,header⟩ := buffer needed
  exact ⟨load32_kept v before after capacity,load64_kept v before after area,
    fun word small => storeInt_defined _ _ _ _ _ _ (words word small),
    fill,bound,load64_kept v before after header⟩

/-! ## The state byte -/

theorem state_before : BitVec.ofNat 64 state - 1#64 = BitVec.ofNat 64 (state-1) := by decide
theorem state_after : BitVec.ofNat 64 state + 1#64 = BitVec.ofNat 64 (state+1) := by decide

/-- A byte of the arena other than the state byte is unchanged by a store to it. -/
theorem away (m : Mem 64) (v : Int) (x size : Nat)
    (apart : x + size ≤ state ∨ state < x) (small : x + size < 2^64) :
    (m.storeInt (.ofNat 64 state) 1 v).loadBytes (.ofNat 64 x) size = m.loadBytes (.ofNat 64 x) size := by
  refine ((storeInt_frame m (.ofNat 64 state) 1 v).loadBytes (.ofNat 64 x) size ?_).symm
  rintro i bound ⟨j,one,equal⟩
  have zero : j = 0 := by omega
  subst zero
  have numbers := congrArg BitVec.toNat equal
  simp only [← BitVec.ofNat_add, BitVec.toNat_ofNat, state] at numbers apart
  omega

theorem state_stored (m : Mem 64) (value : Nat) (small : value < 256) :
    (m.storeInt (.ofNat 64 state) 1 (value : Int)).loadInt (.ofNat 64 state) 1 = some (value : Int) := by
  have read := MemoryBytes.loadInt_store_subword m (.ofNat 64 state) 1 (value : Int) (by decide) 0 1
    (by decide)
  simp at read
  rw [read]
  congr 1
  omega

theorem not_state (x : Nat) (other : x ≠ state) (small : x < 2^64) :
    ¬InRange (.ofNat 64 state) 1 (.ofNat 64 x) := by
  rintro ⟨j,one,equal⟩
  have zero : j = 0 := by omega
  subst zero
  have numbers := congrArg BitVec.toNat equal
  simp only [← BitVec.ofNat_add, BitVec.toNat_ofNat, state] at numbers other
  omega

/-- After one more answer: the allocator's state for the remaining stream,
whatever objects (among the first `count+1`) are handed out. -/
theorem idle_advance {m : Mem 64} {live : List Nat} {record : HiddenRecord}
    {stream : List HiddenRecord} {count : Nat}
    (room : count + (record :: stream).length ≤ slots)
    (before : m.get? (.ofNat 64 (state-1)) = none) (after : m.get? (.ofNat 64 (state+1)) = none)
    (outcomes : ∀ i (bound : i < (record :: stream).length),
      m.loadInt (.ofNat 64 (table+(count+i))) 1 = some (outcome (record :: stream)[i]))
    (zeroed : ∀ i (bound : i < (record :: stream).length), (record :: stream)[i].bytes.head? = some 1 →
      readNat ⟨{dmem := m},0⟩ (slot (count+i)) nodeSize = .ok 0)
    (lives : ∀ object ∈ live, ∃ index < count+1, object = slot index) :
    Idle (m.storeInt (.ofNat 64 state) 1 ((count : Int)+1)) live stream := by
  simp only [List.length_cons, slots] at room
  refine ⟨count+1,?_,by simp only [slots]; omega,?_,?_,?_,?_,lives⟩
  · exact_mod_cast state_stored m (count+1) (by omega)
  · rw [← (storeInt_frame m (.ofNat 64 state) 1 _) _ (not_state _ (by decide) (by decide))]
    exact before
  · rw [← (storeInt_frame m (.ofNat 64 state) 1 _) _ (not_state _ (by decide) (by decide))]
    exact after
  · intro i bound
    have old := outcomes (i+1) (by simp only [List.length_cons]; omega)
    have place : table + (count + 1 + i) = table + (count + (i + 1)) := by omega
    unfold Mem.loadInt at old ⊢
    rw [place, away m _ _ 1 (by simp only [table, state]; omega) (by simp only [table]; omega)]
    simpa using old
  · intro i bound success
    have old := zeroed (i+1) (by simp only [List.length_cons]; omega) (by simpa using success)
    have place : slot (count + 1 + i) = slot (count + (i + 1)) := by
      congr 1
      omega
    simp only [readNat] at old ⊢
    rw [place, away m _ _ nodeSize (by simp only [slot, objects, state]; omega)
      (by simp only [slot, objects, nodeSize]; omega)]
    exact old

/-! ## The contract -/

variable {fetch : Int64 → Option Decoded}

/-- The `alloc` clause. -/
theorem alloc_clause (agree : ∀ pc i, Stub.fetch pc = some i → fetch pc = some i)
    (tableAt : Nat) (peers : List (PeerId × Nat)) (c : Context) (s : MachineState) (ra : UInt64)
    (live : List Nat) (record : HiddenRecord) (stream : List HiddenRecord)
    (entry : s.pc = allocEntry) (frame : EntryFrame s ra) (ready : ServiceReady (layout tableAt peers) allocator c s)
    (cache : s.data.regs.rdi.toNat = (layout tableAt peers).cache)
    (idle : Idle s.data.dmem live (record :: stream)) :
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧
      EqualOutside (ServiceWrites (layout tableAt peers) allocator c s live) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ AllocResult (layout tableAt peers) allocator live record stream t) s := by
  obtain ⟨d,pc⟩ := s
  change pc = _ at entry
  subst entry
  obtain ⟨count,stateRead,room,before,after,outcomes,zeroed,lives⟩ := idle
  have small : count < slots := by
    simp only [List.length_cons] at room
    omega
  have before' : d.dmem.get? (BitVec.ofNat 64 state - 1#64) = none := by
    rw [state_before]
    exact before
  have after' : d.dmem.get? (BitVec.ofNat 64 state + 1#64) = none := by
    rw [state_after]
    exact after
  have rdi : d.regs.rdi = UInt64.ofNat state := by
    have value : d.regs.rdi.toNat = state := cache
    rw [← value, UInt64.ofNat_toNat]
  have code : outcome record = 0 ∨ outcome record = 1 := by
    unfold outcome
    split
    · exact .inr rfl
    · exact .inl rfl
  apply alloc_run fetch agree d ra count small (outcome record) code rdi stateRead
  · have old := outcomes 0 (by simp)
    unfold Mem.loadInt at old ⊢
    rw [away d.dmem _ _ 1 (by simp only [table, state]; omega) (by simp only [table, slots] at *; omega)]
    simpa using old
  · rw [read_kept _ before' after' (by decide) (by rw [frame.2]; rfl)]
    exact frame.2
  intro t returned memory result system
  have earlier : ∀ object ∈ live, ∃ index < count+1, object = slot index := fun object member =>
    let ⟨index,bound,equal⟩ := lives object member
    ⟨index,by omega,equal⟩
  refine ⟨returned,?_,?_,fun failure => ?_,fun success => ?_⟩
  · rw [memory]
    intro a outside
    refine storeInt_frame d.dmem _ 1 _ a (fun inside => outside (.inr (.inl ?_)))
    obtain ⟨j,one,rfl⟩ := inside
    have zero : j = 0 := by omega
    subst zero
    rw [← BitVec.ofNat_add]
    exact ⟨arena_contains (by decide) (by decide),not_kept lives (by omega) (.inl (by decide))⟩
  · rw [memory]
    exact coverage_kept _ before' after' ready.coverage
  · have zero : outcome record = 0 := by simp [outcome, failure]
    rw [zero] at result
    refine ⟨by simpa using result,?_⟩
    rw [memory]
    exact idle_advance room before after outcomes zeroed earlier
  · have one : outcome record = 1 := by simp [outcome, success]
    rw [one] at result
    have address : t.data.regs.rax.toNat = slot count := by simpa using result
    show t.data.regs.rax.toNat ≠ 0 ∧ _
    rw [address]
    simp only [slots] at small
    refine ⟨by simp only [slot, objects]; omega,by simp only [slot, objects]; omega,
      by simp only [slot, objects, nodeSize]; omega,
      ⟨(arenaBase,arenaSize),List.mem_singleton.mpr rfl,
        by simp only [slot, objects, arenaBase]; omega,
        by simp only [slot, objects, arenaBase, arenaSize, nodeSize]; omega⟩,?_,?_,?_⟩
    · intro other member
      obtain ⟨index,bound,rfl⟩ := lives other member
      show disjointRanges (slot count) nodeSize (slot index) nodeSize = true
      have apart : slot index + nodeSize ≤ slot count := by
        simp only [slot, objects, nodeSize]
        omega
      simp [disjointRanges, apart]
    · have old := zeroed 0 (by simp) (by simpa using success)
      simp only [readNat, memory] at old ⊢
      rw [away d.dmem _ _ nodeSize (by simp only [slot, objects, state]; omega)
        (by simp only [slot, objects, nodeSize]; omega)]
      simpa using old
    · rw [memory]
      refine idle_advance room before after outcomes zeroed (fun object member => ?_)
      rcases List.mem_append.mp member with old | new
      · exact earlier object old
      · exact ⟨count,by omega,List.mem_singleton.mp new⟩

/-- The `free` clause. -/
theorem free_clause (agree : ∀ pc i, Stub.fetch pc = some i → fetch pc = some i)
    (tableAt : Nat) (peers : List (PeerId × Nat)) (c : Context) (s : MachineState) (ra : UInt64)
    (live : List Nat) (stream : List HiddenRecord)
    (entry : s.pc = freeEntry) (frame : EntryFrame s ra) (ready : ServiceReady (layout tableAt peers) allocator c s)
    (idle : Idle s.data.dmem live stream) :
    Eventually (instructionStep fetch) (fun t =>
      Returned s t ra ∧
      EqualOutside (ServiceWrites (layout tableAt peers) allocator c s
        (live.erase s.data.regs.rsi.toNat)) s.data.dmem t.data.dmem ∧
      c.At t.data.dmem ∧ Idle t.data.dmem (live.erase s.data.regs.rsi.toNat) stream) s := by
  obtain ⟨d,pc⟩ := s
  change pc = _ at entry
  subst entry
  apply free_run fetch agree d ra frame.2
  intro t returned memory
  obtain ⟨count,stateRead,room,before,after,outcomes,zeroed,lives⟩ := idle
  refine ⟨returned,?_,?_,?_⟩
  · rw [memory]
    exact fun _ _ => rfl
  · rw [memory]
    exact ready.coverage
  · rw [memory]
    exact ⟨count,stateRead,room,before,after,outcomes,zeroed,
      fun object member => lives object (List.mem_of_mem_erase member)⟩

/-- THE STUB MEETS THE CONTRACT AS STATED, at any decoder that holds its code. -/
theorem contract (agree : ∀ pc i, Stub.fetch pc = some i → fetch pc = some i)
    (tableAt : Nat) (peers : List (PeerId × Nat)) :
    AllocatorContract fetch (layout tableAt peers) allocator :=
  ⟨fun _ _ _ _ idle same => idle_frame idle same,
   fun c s ra live record stream entry frame ready cache _ _ idle =>
     alloc_clause agree tableAt peers c s ra live record stream entry frame ready cache idle,
   fun c s ra live stream entry frame ready _ _ _ idle =>
     free_clause agree tableAt peers c s ra live stream entry frame ready idle⟩

#print axioms contract
#print axioms coverage_kept
end Binary.Statements.C1.Stub
