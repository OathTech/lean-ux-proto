import C1BelowRollbackEntry

/-! Result C1, work package 3, rollback path (case `splitNoMem`): the machine
segment from the second allocation's NULL return (`add+0x292`) to the common
exit `add+0x549`, with the release service taken from the hypothesis
`FreeRule`. The hypotheses are facts about the state at `add+0x292` and the
caller's conditions; no execution is assumed. -/
namespace Binary.Statements.C1.Proof.Rollback
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.AllowedipsMutationImage Binary.Instrumentation
local instance : Labels := Image.linkedLabels

/-- Bytes the rollback's release leaves as they were at its entry: the live
frames from the stack pointer of `a` up to and including the wrapper's return
word, the layout's fixed words, the nodes that stay handed out, and the
`node_cache` word (`Protected` without the release's own return word). -/
def Guarded (L : Layout) (s a : MachineState) (kept : List Nat) (y : BitVec 64) : Prop :=
  InRange a.data.regs.rsp.toBitVec (s.data.regs.rsp.toNat + 8 - a.data.regs.rsp.toNat) y ∨
  (∃ span ∈ L.fixed, span.contains y) ∨ Kept kept y ∨ InRange (.ofNat 64 cacheWord) 8 y

theorem range_below {p : UInt64} {n : Nat} {y : BitVec 64} (inside : InRange p.toBitVec n y) :
    InRange (p.toBitVec - 8) (n + 8) y := by
  obtain ⟨i,bound,at_⟩ := inside
  refine ⟨i+8,by omega,?_⟩
  rw [at_,BitVec.ofNat_add,BitVec.add_comm (BitVec.ofNat 64 i),←BitVec.add_assoc]
  congr 1
  exact (BitVec.sub_add_cancel _ _).symm

theorem above_push {p : UInt64} {n : Nat} {y : BitVec 64} (positive : 8 ≤ p.toNat)
    (fits : p.toNat + n ≤ 2^64) (inside : InRange p.toBitVec n y) : ¬InRange (p.toBitVec - 8) 8 y := by
  obtain ⟨i,bound,at_⟩ := inside
  rintro ⟨j,other,equal⟩
  have raw := congrArg BitVec.toNat (at_.symm.trans equal)
  have size := p.toBitVec.isLt
  have eight : (8 : BitVec 64).toNat = 8 := rfl
  have value : p.toBitVec.toNat = p.toNat := rfl
  simp only [BitVec.toNat_add,BitVec.toNat_sub,BitVec.toNat_ofNat,eight,value] at raw size
  omega

/-- Run from a state by naming its program counter, leaving the postcondition as stated. -/
theorem start_at {fetch : Int64 → Option Decoded} {P : MachineState → Prop} {a : MachineState} {pc : Int64}
    (here : a.pc = pc) (run : Eventually (instructionStep fetch) P ⟨a.data,pc⟩) :
    Eventually (instructionStep fetch) P a := by
  cases a
  cases here
  exact run

/-- THE ROLLBACK SEGMENT. From `add+0x292` with NULL in `rax`: the node saved
in the local at `rsp+0x18` is unlinked from its peer's list and released, and
the machine is at the common exit with `-ENOMEM` in `ebx`, still in flight,
the allocator idle without the node. `covered` is the memory after the
coverage callback; every guarded byte at the exit is the byte of `covered`
after `list_del`'s four stores. -/
theorem rollback (free : FreeRule) (fetch : Int64 → Option Decoded) (L : Layout) (A : Allocator)
    (premises : Premises fetch L A) (c : Context) (s a : MachineState)
    (family key cidr pid : Nat) (ra : UInt64) (live : List Nat) (stream : List HiddenRecord)
    (base next prev : Nat)
    (ready : insertReady L A c s family key cidr pid ra = .ok ())
    (apart : spansApart (objectsOf L) L.arena = true) (arena : ∀ node ∈ live, InArena L node)
    (pc : a.pc = Add.entry + 0x292) (rax : a.data.regs.rax = 0)
    (flight : InFlight L A c s a)
    (high : a.data.regs.rsp.toNat + 48 ≤ s.data.regs.rsp.toNat)
    (low : s.data.regs.rsp.toNat + 48 ≤ a.data.regs.rsp.toNat + insertWindow)
    (calls : CallsReady c a.data)
    (localMapped : (a.data.dmem.loadInt a.data.regs.rsp.toBitVec 8).isSome = true)
    (baseRead : a.data.dmem.loadInt (a.data.regs.rsp.toBitVec + 24) 8 = some (base : Int))
    (member : base ∈ live)
    (nextRead : a.data.dmem.loadInt (.ofNat 64 base + 56) 8 = some (next : Int))
    (prevRead : a.data.dmem.loadInt (.ofNat 64 base + 64) 8 = some (prev : Int))
    (nextMapped : (a.data.dmem.loadInt (.ofNat 64 next + 8) 8).isSome = true)
    (prevMapped : (a.data.dmem.loadInt (.ofNat 64 prev) 8).isSome = true)
    (links : ∀ x, InRange (.ofNat 64 next + 8) 8 x ∨ InRange (.ofNat 64 prev) 8 x →
      L.Heap x ∧ (L.Arena x → Kept live x))
    (idle : A.Idle a.data.dmem live stream) :
    Eventually (instructionStep fetch) (fun x =>
      x.pc = Add.entry + 0x549 ∧ x.data.regs.rsp = a.data.regs.rsp ∧
      x.data.regs.get (.low .rbx .W32) = BitVec.ofInt 32 (-ENOMEM) ∧
      InFlight L A c s x ∧ CallsReady c x.data ∧
      A.Idle x.data.dmem (live.erase base) stream ∧
      ∃ covered,
        EqualOutside (fun y => InRange (a.data.regs.rsp.toBitVec - 8) 8 y ∨ c.writes y)
          (a.data.dmem.storeInt a.data.regs.rsp.toBitVec 8 (UInt64.ofNat base).toBitVec.toInt) covered ∧
        ∀ y, Guarded L s a (live.erase base) y →
          x.data.dmem.get? y = (poisoned (unlinked covered next prev) base).get? y) a := by
  have facts := ready_facts ready
  have window := window_bounds facts
  have pushed := pushed_rsp facts low
  have scratch {x : BitVec 64} (inside : Words a.data.regs.rsp x) : Window A s x :=
    scratch_window (words_scratch facts high low inside)
  have listHeap (x : BitVec 64) (written : ListWrites base next prev x) :
      L.Heap x ∧ (L.Arena x → Kept live x) := by
    rcases written with link | node
    · exact links x link
    · have kept : Kept live x := ⟨base,member,node.elim
        (node_bytes (offset := 56) (by decide)) (node_bytes (offset := 64) (by decide))⟩
      exact ⟨arena_heap (kept_arena arena kept),fun _ => kept⟩
  have cacheRead := Trie.readNat_loadInt (facts.cache_read flight)
  have cacheSmall : L.cache < 2^64 := by
    have bound := (loadInt_range _ _ _ _ cacheRead).2
    omega
  have baseSmall := live_bound apart arena member
  -- to the release's entry
  have entry := eventually_flight (to_free fetch premises.insertion premises.tracePc c a.data base L.cache
    next prev calls rax baseRead localMapped cacheRead nextRead prevRead nextMapped prevMapped
    (fun x read inside => facts.bytes_window read (scratch (words_local inside)))
    (fun x inside written => facts.writes_window written (scratch (words_local inside)))
    (fun x read touched => by
      rcases read with cache | written
      · rcases touched with stack | covered
        · exact facts.scratch_cache (words_scratch facts high low stack) cache
        · exact facts.writes_cache covered cache
      · rcases touched with stack | covered
        · exact facts.heap_window (listHeap x written).1 (scratch stack)
        · exact facts.heap_writes (listHeap x written).1 covered)
    (fun x read written => facts.heap_bytes (listHeap x written).1 read))
  apply start_at pc
  apply eventually_trans (instructionStep fetch) _ _ _ entry
  rintro e ⟨⟨covered,v,frameC,readyV,stackV,memV,rdiV,rsiV,rfl⟩,mappedE,flagE⟩
  generalize site : calledState v (Add.entry + 0x692) (label "L_ffffffff81199b10") = e at mappedE flagE ⊢
  have rspE : e.data.regs.rsp = a.data.regs.rsp - 8 := by rw [←site,←stackV]; rfl
  have memE : e.data.dmem = (poisoned (unlinked covered next prev) base).storeInt
      (a.data.regs.rsp.toBitVec - 8) 8 (Add.entry + 0x692).toBitVec.toInt := by
    rw [←site,←stackV,←memV]; rfl
  have frameE : EqualOutside (fun x => Words a.data.regs.rsp x ∨ c.writes x ∨ ListWrites base next prev x)
      a.data.dmem e.data.dmem := by
    intro x outside
    rw [memE]
    exact ((storeInt_frame _ _ 8 _ x (fun h => outside (.inl (words_local h)))).trans
      (frameC x (fun h => outside (h.elim (fun h => .inl (words_push h)) (fun h => .inr (.inl h)))))).trans
      ((released_frame covered base next prev x (fun h => outside (.inr (.inr h)))).trans
        (storeInt_frame _ _ 8 _ x (fun h => outside (.inl (words_push h)))))
  have ready' := called_ready c v (Add.entry + 0x692) (label "L_ffffffff81199b10") readyV
  rw [site] at ready'
  have flightE : InFlight L A c s e := flight.later _ (by rw [rspE]; omega) (by rw [rspE]; omega) frameE
    (fun x written => by
      rcases written with stack | covered | list
      · exact .inl (words_scratch facts high low stack)
      · exact .inr (.inl covered)
      · exact .inr (.inr (listHeap x list).1))
    mappedE flagE ready'.2
  have idleE : A.Idle e.data.dmem live stream :=
    premises.allocator.frame _ _ live stream idle (fun x inArena notKept => frameE x (fun written => by
      rcases written with stack | covered | list
      · exact facts.heap_window (arena_heap inArena) (scratch stack)
      · exact facts.heap_writes (arena_heap inArena) covered
      · exact notKept ((listHeap x list).2 inArena)))
  have rsiE : e.data.regs.rsi.toNat = base := by
    rw [←site]
    change v.regs.rsi.toNat = base
    rw [rsiV,UInt64.toNat_ofNat']
    unfold nodeSize at baseSmall
    exact Nat.mod_eq_of_lt (by omega)
  have rdiE : e.data.regs.rdi.toNat = L.cache := by
    rw [←site]
    change v.regs.rdi.toNat = L.cache
    rw [rdiV,UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt cacheSmall
  have pcE : e.pc = freeEntry := by rw [←site]; rfl
  have freed := eventually_flight (free fetch L A premises c s e family key cidr pid ra
    (Add.entry + 0x692).toUInt64 live stream ready apart arena flightE (by rw [rspE]; omega) pcE ready'.1
    (by rfl) rdiE (rsiE ▸ member) idleE)
  apply eventually_trans (instructionStep fetch) _ _ _ freed
  rintro t ⟨⟨returned,idleT,flightT,kept⟩,mappedT,flagT⟩
  obtain ⟨pcT,stackT,_⟩ := returned
  have pcT : t.pc = Add.entry + 0x692 := pcT
  have stackT : t.data.regs.rsp = a.data.regs.rsp := by
    rw [stackT,rspE]; exact UInt64.sub_add_cancel _ _
  apply start_at pcT
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (eventually_flight (region_eventually (Add_r692_layout.agreement premises.insertion.add) t.data _
      (region692 t.data)))
  rintro x ⟨⟨pcX,memX,regsX⟩,mappedX,flagX⟩
  have stackX : x.data.regs.rsp = a.data.regs.rsp := by rw [regsX]; exact stackT
  have flightX : InFlight L A c s x := flightT.later (fun _ => False) (by rw [stackX]; omega)
    (by rw [stackX]; omega) (fun y _ => by rw [memX]) (fun _ h => h.elim) mappedX flagX
    (memX ▸ flightT.coverage)
  refine ⟨pcX,stackX,by rw [regsX]; rfl,flightX,?_,?_,covered,frameC,?_⟩
  · exact {
      state := flightX.coverage
      aligned := by rw [stackX]; exact calls.aligned
      mapped := by rw [stackX]; exact mappedX _ _ (mappedT _ _ (mappedE _ _ calls.mapped))
      pushSeparate := by rw [stackX]; exact calls.pushSeparate
      returnSeparate := by rw [stackX]; exact calls.returnSeparate
      metadataSeparate := calls.metadataSeparate
      preemptSeparate := calls.preemptSeparate }
  · rw [memX,←rsiE]; exact idleT
  · intro y guarded
    have notPush : ¬InRange (a.data.regs.rsp.toBitVec - 8) 8 y := by
      rcases guarded with stack | ⟨span,fixed,inside⟩ | keptNode | cache
      · exact above_push (by omega) (by omega) stack
      · exact fun push => facts.heap_window ⟨span,List.mem_append_left _ fixed,inside⟩ (scratch (words_push push))
      · obtain ⟨object,named,inside⟩ := keptNode
        exact fun push => facts.heap_window
          (arena_heap (kept_arena arena ⟨object,List.mem_of_mem_erase named,inside⟩)) (scratch (words_push push))
      · exact fun push => facts.scratch_cache (words_scratch facts high low (words_push push)) cache
    have covers : Protected L s e (live.erase e.data.regs.rsi.toNat) y := by
      rw [rsiE]
      rcases guarded with stack | fixed | keptNode | cache
      · left
        have size : s.data.regs.rsp.toNat + 8 - e.data.regs.rsp.toNat =
            s.data.regs.rsp.toNat + 8 - a.data.regs.rsp.toNat + 8 := by rw [rspE]; omega
        rw [size,rspE]
        exact range_below stack
      · exact .inr (.inl fixed)
      · exact .inr (.inr (.inl keptNode))
      · exact .inr (.inr (.inr cache))
    rw [memX,kept y covers,memE]
    exact (storeInt_frame _ _ 8 _ y notPush).symm

#print axioms rollback
end Binary.Statements.C1.Proof.Rollback
