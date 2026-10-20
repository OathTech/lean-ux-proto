import TrustBase
import StackFrame

namespace Binary.Kcov
open TrustBase
set_option maxHeartbeats 800000

def enabled (kind : KcovKind) (layout : KcovLayout) (preempt : BitVec 32) : Bool :=
  (!(preempt &&& 0xff0100 != 0) ||
    (!(preempt &&& 0x100 == 0 || preempt &&& 0xff0000 != 0) &&
      !(layout.softirqEnabled == 0))) &&
  !(layout.mode != (if kind = .pc then 2 else 3))

/-- The same buffer arithmetic as the machine, expressed as bounded natural
    word offsets to expose the physical write footprint. -/
def bufferPlan (kind : KcovKind) (layout : KcovLayout) (count : Nat)
    (returnPC arg1 arg2 : BitVec 64) : List WordWrite :=
  if kind = .pc then
    if count + 1 < layout.capacity.toNat then
      [⟨layout.area, .ofNat 64 (count + 1)⟩,
       ⟨layout.area + .ofNat 64 (8 * (count + 1)), returnPC⟩]
    else []
  else
    if 4 * count + 5 ≤ layout.capacity.toNat then
      [⟨layout.area, .ofNat 64 (count + 1)⟩,
       ⟨layout.area + .ofNat 64 (8 * (4 * count + 1)),
         KcovRecordTag kind⟩,
       ⟨layout.area + .ofNat 64 (8 * (4 * count + 2)), arg1⟩,
       ⟨layout.area + .ofNat 64 (8 * (4 * count + 3)), arg2⟩,
       ⟨layout.area + .ofNat 64 (8 * (4 * count + 4)), returnPC⟩]
    else []

def argument (kind : KcovKind) (s : MachineState) (reg : Reg64) : BitVec 64 :=
  KcovArgument kind s reg

set_option maxHeartbeats 1200000 in
/-- Conditional metadata supports exactly the same buffer arithmetic as the
    existing callback proof; the softirq and mode reads are required only
    when reached. This intermediate lemma is used on the active path. -/
theorem plan_normal_form_of_reads (kind : KcovKind) (layout : KcovLayout)
    (s : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64) (count : Nat)
    (task : load64 s.data.dmem currentTaskAddress = some layout.task)
    (softirq : LookupSoftRead preempt → load32 s.data.dmem (layout.task+0x704) = some layout.softirqEnabled)
    (mode : LookupModeRead layout preempt → load32 s.data.dmem (layout.task+0x6e0) = some layout.mode)
    (capacity : load32 s.data.dmem (layout.task+0x6e4) = some layout.capacity)
    (area : load64 s.data.dmem (layout.task+0x6e8) = some layout.area)
    (preemptRead : load32 s.data.dmem preemptCountAddress = some preempt)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (countRead : load64 s.data.dmem layout.area = some (.ofNat 64 count))
    (countBound : count ≤ layout.capacity.toNat) :
    KcovPlan kind s = some (if Kcov.enabled kind layout preempt then
      Kcov.bufferPlan kind layout count returnPC (Kcov.argument kind s .rdi) (Kcov.argument kind s .rsi)
      else []) := by
  have capBound := layout.capacity.isLt
  have nextBound : count + 1 < 2^64 := by omega
  have endBound : 32 * count + 40 < 2^64 := by omega
  have capWide : 8 * layout.capacity.toNat < 2^64 := by omega
  have nextNat : ((BitVec.ofNat 64 count) + 1).toNat = count + 1 := by
    simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : count < 2^64),
      Nat.mod_eq_of_lt nextBound]
  have endNat : (8 * (4 * (BitVec.ofNat 64 count)) + 40).toNat = 32 * count + 40 := by
    simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
    simp only [show (8 : BitVec 64).toNat = 8 from rfl,
      show (4 : BitVec 64).toNat = 4 from rfl, show (40 : BitVec 64).toNat = 40 from rfl]
    omega
  have capNat : (8 * layout.capacity.setWidth 64).toNat = 8 * layout.capacity.toNat := by
    simp [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le (by decide : 32 ≤ 64),
      Nat.mod_eq_of_lt capWide]
  have nextBV : (BitVec.ofNat 64 count) + 1 = BitVec.ofNat 64 (count+1) := by
    simp [BitVec.ofNat_add]
  have address (n : Nat) (hn : n ≤ 32) :
      layout.area + (8 * (4 * (BitVec.ofNat 64 count)) + 40) - .ofNat 64 n =
        layout.area + .ofNat 64 (32 * count + 40 - n) := by
    rw [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [← BitVec.sub_eq_add_neg]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, endNat, BitVec.toNat_ofNat]
    omega
  have endGuard : (8 * layout.capacity.setWidth 64 < 8 * (4 * BitVec.ofNat 64 count) + 40) ↔
      ¬(4 * count + 5 ≤ layout.capacity.toNat) := by
    rw [BitVec.lt_def, capNat, endNat]
    omega
  have a32 := address 32 (by decide)
  have a24 := address 24 (by decide)
  have a16 := address 16 (by decide)
  have a8 := address 8 (by decide)
  have o32 : 32*count+40-32 = 8*(4*count+1) := by omega
  have o24 : 32*count+40-24 = 8*(4*count+2) := by omega
  have o16 : 32*count+40-16 = 8*(4*count+3) := by omega
  have o8 : 32*count+40-8 = 8*(4*count+4) := by omega
  simp only [o32, o24, o16, o8] at a32 a24 a16 a8
  by_cases pcKind : kind = .pc
  all_goals by_cases h0 : preempt &&& 0xff0100#32 = 0#32
  all_goals by_cases h1 : preempt &&& 0x100#32 = 0#32
  all_goals by_cases h2 : preempt &&& 0xff0000#32 = 0#32
  all_goals by_cases h3 : layout.softirqEnabled = 0#32
  all_goals simp only [LookupSoftRead, LookupModeRead,    h3,

         ] at softirq mode
  all_goals simp [KcovPlan, preemptRead, returnRead, task,
    h0, h1, h2,  pcKind,      ]
  all_goals
    simp [enabled, bufferPlan, argument, pcKind,  BitVec.ofNat_mul,
      Nat.not_lt, ]
  all_goals by_cases h0 : preempt &&& 0xff0100#32 = 0#32 <;> simp_all
  all_goals by_cases h1 : preempt &&& 0x100#32 = 0#32 <;> simp_all
  all_goals by_cases h2 : preempt &&& 0xff0000#32 = 0#32 <;> simp_all
  all_goals by_cases h3 : layout.softirqEnabled = 0#32 <;> simp_all
  all_goals by_cases h4 : layout.mode = 2 <;> simp_all
  all_goals by_cases h5 : layout.mode = 3 <;> simp_all
  all_goals simp [Nat.mod_eq_of_lt nextBound, ← Nat.not_lt, ite_not]
  all_goals split <;> simp_all [BitVec.ofNat_mul]


theorem plan_normal_form (kind : KcovKind) (layout : KcovLayout)
    (s : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64) (count : Nat)
    (metadata : KcovMetadata layout s.data.dmem)
    (preemptRead : load32 s.data.dmem preemptCountAddress = some preempt)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (countRead : load64 s.data.dmem layout.area = some (.ofNat 64 count))
    (countBound : count ≤ layout.capacity.toNat) :
    KcovPlan kind s = some (if enabled kind layout preempt then
      bufferPlan kind layout count returnPC (argument kind s .rdi) (argument kind s .rsi)
      else []) := by
  obtain ⟨task, mode, capacity, area, softirq⟩ := metadata
  exact plan_normal_form_of_reads kind layout s preempt returnPC count task
    (fun _ => softirq) (fun _ => mode) capacity area preemptRead returnRead countRead countBound

/-- A nonempty callback writes the incremented header first and then only
    positive, in-bounds word indices. The zero-capacity case is included. -/
theorem bufferPlan_shape (kind : KcovKind) (layout : KcovLayout) (count : Nat)
    (returnPC arg1 arg2 : BitVec 64) :
    bufferPlan kind layout count returnPC arg1 arg2 = [] ∨
      ∃ tail, bufferPlan kind layout count returnPC arg1 arg2 =
        ⟨layout.area, .ofNat 64 (count+1)⟩ :: tail ∧
        count+1 ≤ layout.capacity.toNat ∧
        ∀ write ∈ tail, ∃ word, 0 < word ∧ word < layout.capacity.toNat ∧
          write.address = layout.area + .ofNat 64 (8*word) := by
  unfold bufferPlan
  split <;> split
  · right
    refine ⟨_, rfl, by omega, ?_⟩
    intro write member
    simp only [List.mem_singleton] at member
    subst write
    exact ⟨count+1, by omega, by omega, rfl⟩
  · exact .inl rfl
  · right
    refine ⟨_, rfl, by omega, ?_⟩
    intro write member
    simp only [List.mem_cons,  List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨4*count+1, by omega, by omega, rfl⟩
    · exact ⟨4*count+2, by omega, by omega, rfl⟩
    · exact ⟨4*count+3, by omega, by omega, rfl⟩
    · exact ⟨4*count+4, by omega, by omega, rfl⟩
  · exact .inl rfl

/-- Distinct words in any possible 32-bit-capacity buffer cannot alias,
    even when the base plus its extent crosses address zero. -/
theorem word_disjoint (base : BitVec 64) (i j : Nat)
    (hi : i < 2^32) (hj : j < 2^32) (different : i ≠ j) (address : BitVec 64)
    (atI : InRange (base + .ofNat 64 (8*i)) 8 address) :
    ¬InRange (base + .ofNat 64 (8*j)) 8 address := by
  rintro ⟨b, hb, atJ⟩
  obtain ⟨a, ha, atI⟩ := atI
  have equal : base + .ofNat 64 (8*i+a) = base + .ofNat 64 (8*j+b) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using atI.symm.trans atJ
  have nums := congrArg (fun x : BitVec 64 => (x-base).toNat) equal
  simp only [BitVec.add_comm base, BitVec.add_sub_cancel, BitVec.toNat_ofNat] at nums
  omega

def storesMemory (stores : List WordWrite) (memory : Mem 64) : Mem 64 :=
  stores.foldl (fun m write => m.storeInt write.address 8 write.value.toInt) memory

theorem stores_mapped (stores : List WordWrite) (memory : Mem 64)
    (address : BitVec 64) (width : Nat)
    (mapped : (memory.loadInt address width).isSome = true) :
    ((storesMemory stores memory).loadInt address width).isSome = true := by
  induction stores generalizing memory with
  | nil => exact mapped
  | cons write tail ih => exact ih _ (storeInt_defined _ _ _ _ _ _ mapped)

theorem stores_frame (stores : List WordWrite) (memory : Mem 64)
    (footprint : BitVec 64 → Prop)
    (inside : ∀ write ∈ stores, ∀ address, InRange write.address 8 address → footprint address) :
    EqualOutside footprint memory (storesMemory stores memory) := by
  induction stores generalizing memory with
  | nil => intro address outside; rfl
  | cons write tail ih =>
    intro address outside
    have first := storeInt_frame memory write.address 8 write.value.toInt address
      (fun inWord => outside (inside write (by simp) address inWord))
    have rest := ih (memory.storeInt write.address 8 write.value.toInt)
      (fun w hw => inside w (by simp [hw])) address outside
    exact first.trans rest

theorem bufferPlan_preserves (kind : KcovKind) (layout : KcovLayout) (count : Nat)
    (returnPC arg1 arg2 : BitVec 64) (memory : Mem 64)
    (buffer : KcovBuffer layout memory)
    (countRead : load64 memory layout.area = some (.ofNat 64 count))
    (countBound : count ≤ layout.capacity.toNat) :
    KcovBuffer layout (storesMemory (bufferPlan kind layout count returnPC arg1 arg2) memory) := by
  obtain ⟨mapped, old⟩ := buffer
  constructor
  · intro word bound
    exact stores_mapped _ _ _ _ (mapped word bound)
  · rcases bufferPlan_shape kind layout count returnPC arg1 arg2 with empty | ⟨tail, shape, bound, payload⟩
    · rw [empty]
      exact ⟨count, countBound, countRead⟩
    · rw [shape]
      refine ⟨count+1, bound, ?_⟩
      have frame := stores_frame tail
        (memory.storeInt layout.area 8 (BitVec.ofNat 64 (count+1)).toInt)
        (fun address => ¬InRange layout.area 8 address) (by
          intro write member address inside
          obtain ⟨word, positive, wordBound, addressEq⟩ := payload write member
          rw [addressEq] at inside
          have disjoint := word_disjoint layout.area word 0
            (Nat.lt_trans wordBound layout.capacity.isLt) (by decide) (by omega) address inside
          simpa using disjoint)
      have readback := load64_store memory layout.area (.ofNat 64 (count+1))
      have tailRead := frame.loadInt layout.area 8 (by
        intro byte bound
        intro outside
        exact outside ⟨byte, bound, rfl⟩)
      change load64 (storesMemory tail (memory.storeInt layout.area 8
        (BitVec.ofNat 64 (count+1)).toInt)) layout.area = _
      unfold load64
      rw [← tailRead, readback]
      simp only [Option.map_some, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem bufferPlan_addresses (kind : KcovKind) (layout : KcovLayout) (count : Nat)
    (returnPC arg1 arg2 : BitVec 64) (write : WordWrite)
    (member : write ∈ bufferPlan kind layout count returnPC arg1 arg2) :
    ∃ word < layout.capacity.toNat,
      write.address = layout.area + .ofNat 64 (8*word) := by
  rcases bufferPlan_shape kind layout count returnPC arg1 arg2 with empty | ⟨tail, shape, bound, payload⟩
  · simp [empty] at member
  · rw [shape] at member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨0, by omega, by simp⟩
    · obtain ⟨word, _, wordBound, address⟩ := payload write member
      exact ⟨word, wordBound, address⟩

theorem word_in_buffer (layout : KcovLayout) (word : Nat) (bound : word < layout.capacity.toNat)
    (address : BitVec 64) (inside : InRange (layout.area + .ofNat 64 (8*word)) 8 address) :
    KcovBufferBytes layout address := by
  obtain ⟨byte, byteBound, atByte⟩ := inside
  refine ⟨8*word+byte, by omega, ?_⟩
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using atByte

/-- All planned writes are inside the physical buffer, including at full
    capacity and at the exact comparison-record fit boundary. -/
theorem writes_inside (kind : KcovKind) (layout : KcovLayout)
    (s : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64)
    (metadata : KcovMetadata layout s.data.dmem)
    (buffer : KcovBuffer layout s.data.dmem)
    (preemptRead : load32 s.data.dmem preemptCountAddress = some preempt)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC) :
    ∀ address, KcovWrites kind s address → KcovBufferBytes layout address := by
  obtain ⟨count, countBound, countRead⟩ := buffer.2
  have normal := plan_normal_form kind layout s preempt returnPC count metadata
    preemptRead returnRead countRead countBound
  rintro address ⟨stores, plan, write, member, inside⟩
  rw [normal] at plan
  cases Option.some.inj plan
  split at member
  · obtain ⟨word, bound, atWord⟩ := bufferPlan_addresses kind layout count returnPC
      (argument kind s .rdi) (argument kind s .rsi) write member
    rw [atWord] at inside
    exact word_in_buffer layout word bound address inside
  · simp at member

/-- Readiness follows from one physical invariant and return-slot separation. -/
theorem ready (kind : KcovKind) (layout : KcovLayout)
    (s : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64)
    (metadata : KcovMetadata layout s.data.dmem)
    (buffer : KcovBuffer layout s.data.dmem)
    (preemptRead : load32 s.data.dmem preemptCountAddress = some preempt)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (stack : KcovSeparated layout (InRange s.data.regs.rsp.toBitVec 8)) :
    KcovReady kind s := by
  obtain ⟨mapped, count, countBound, countRead⟩ := buffer
  have normal := plan_normal_form kind layout s preempt returnPC count metadata
    preemptRead returnRead countRead countBound
  refine ⟨_, normal, ?_⟩
  intro write member
  split at member
  · obtain ⟨word, bound, atWord⟩ := bufferPlan_addresses kind layout count returnPC
      (argument kind s .rdi) (argument kind s .rsi) write member
    constructor
    · rw [atWord]
      exact mapped word bound
    · intro address inside
      rw [atWord] at inside
      exact stack address (word_in_buffer layout word bound address inside)
  · simp at member

/-- The exact service effect re-establishes the buffer invariant. No claim
    about a later callback's readiness is an assumption of this theorem. -/
theorem effect_preserves_buffer (kind : KcovKind) (layout : KcovLayout)
    (s t : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64)
    (metadata : KcovMetadata layout s.data.dmem)
    (buffer : KcovBuffer layout s.data.dmem)
    (preemptRead : load32 s.data.dmem preemptCountAddress = some preempt)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (effect : KcovEffect kind s t) : KcovBuffer layout t.data.dmem := by
  obtain ⟨count, countBound, countRead⟩ := buffer.2
  have normal := plan_normal_form kind layout s preempt returnPC count metadata
    preemptRead returnRead countRead countBound
  obtain ⟨stores, plan, afterMemory⟩ := effect
  rw [normal] at plan
  cases Option.some.inj plan
  rw [afterMemory]
  split
  · exact bufferPlan_preserves kind layout count returnPC (argument kind s .rdi)
      (argument kind s .rsi) s.data.dmem buffer countRead countBound
  · exact buffer

/-- Caller stores preserve the buffer when they preserve its storage. The
    header remains protected even for a zero-word-capacity buffer. -/
theorem buffer_frame (layout : KcovLayout) (before after : Mem 64)
    (buffer : KcovBuffer layout before) (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes before after)
    (separate : ∀ address, KcovStorageBytes layout address → ¬writes address) :
    KcovBuffer layout after := by
  obtain ⟨mapped, count, countBound, countRead⟩ := buffer
  constructor
  · intro word bound
    have read := frame.loadInt (layout.area + .ofNat 64 (8*word)) 8 (by
      intro byte byteBound
      apply separate
      exact .inr (word_in_buffer layout word bound _ ⟨byte, byteBound, rfl⟩))
    rw [← read]
    exact mapped word bound
  · refine ⟨count, countBound, ?_⟩
    have read := frame.loadInt layout.area 8 (by
      intro byte byteBound
      exact separate _ (.inl ⟨byte, byteBound, rfl⟩))
    simpa only [load64, ← read] using countRead

/-- Disabled tracing needs no buffer mapping or header read. -/
theorem inactive_plan (kind : KcovKind) (layout : KcovLayout)
    (s : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64)
    (metadata : KcovMetadata layout s.data.dmem)
    (preemptRead : load32 s.data.dmem preemptCountAddress = some preempt)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (inactive : layout.mode ≠ (if kind = .pc then 2 else 3)) :
    KcovPlan kind s = some [] := by
  obtain ⟨task, mode, capacity, area, softirq⟩ := metadata
  simp [KcovPlan, preemptRead, returnRead, task,  ]
  all_goals by_cases h0 : preempt &&& 0xff0100#32 = 0#32 <;> simp_all
  all_goals by_cases h1 : preempt &&& 0x100#32 = 0#32 <;> simp_all
  all_goals by_cases h2 : preempt &&& 0xff0000#32 = 0#32 <;> simp_all
  all_goals by_cases h3 : layout.softirqEnabled = 0#32 <;> simp_all

theorem inactive_ready (kind : KcovKind) (s : MachineState)
    (plan : KcovPlan kind s = some []) : KcovReady kind s :=
  ⟨[], plan, by simp⟩

theorem inactive_effect (kind : KcovKind) (s t : MachineState)
    (plan : KcovPlan kind s = some []) (effect : KcovEffect kind s t) :
    t.data.dmem = s.data.dmem := by
  obtain ⟨stores, computed, memory⟩ := effect
  rw [plan] at computed
  cases Option.some.inj computed
  exact memory

/-- Byte equality outside the buffer preserves every exact metadata read. -/
theorem metadata_frame (layout : KcovLayout) (before after : Mem 64)
    (metadata : KcovMetadata layout before)
    (frame : EqualOutside (KcovBufferBytes layout) before after)
    (separate : KcovSeparated layout (KcovMetadataBytes layout)) :
    KcovMetadata layout after := by
  have field (base : BitVec 64) (width : Nat)
      (part : ∀ address, InRange base width address → KcovMetadataBytes layout address) :
      before.loadInt base width = after.loadInt base width := by
    apply frame.loadInt
    intro byte byteBound inBuffer
    exact separate _ inBuffer (part _ ⟨byte, byteBound, rfl⟩)
  have task := field currentTaskAddress 8 (fun _ inside => .inl inside)
  have mode := field (layout.task+0x6e0) 4 (fun _ inside => .inr (.inl inside))
  have capacity := field (layout.task+0x6e4) 4 (fun _ inside => .inr (.inr (.inl inside)))
  have area := field (layout.task+0x6e8) 8 (fun _ inside => .inr (.inr (.inr (.inl inside))))
  have softirq := field (layout.task+0x704) 4 (fun _ inside => .inr (.inr (.inr (.inr inside))))
  simpa only [KcovMetadata, load32, load64, ← task, ← mode, ← capacity, ← area, ← softirq]
    using metadata

/-- Convert the callback's exact write footprint to the stable buffer
    footprint used by the caller's stack, object and metadata frames. -/
theorem effect_frame (kind : KcovKind) (layout : KcovLayout)
    (s t : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64)
    (metadata : KcovMetadata layout s.data.dmem)
    (buffer : KcovBuffer layout s.data.dmem)
    (preemptRead : load32 s.data.dmem preemptCountAddress = some preempt)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (frame : EqualOutside (KcovWrites kind s) s.data.dmem t.data.dmem) :
    EqualOutside (KcovBufferBytes layout) s.data.dmem t.data.dmem := by
  intro address outside
  exact frame address (fun written => outside
    (writes_inside kind layout s preempt returnPC metadata buffer preemptRead returnRead address written))

/-- A single physical state invariant supplies readiness for every callback
    kind; inactive modes use the actual early return and need no buffer. -/
theorem state_ready (kind : KcovKind) (layout : KcovLayout)
    (s : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64)
    (state : KcovState layout preempt s.data.dmem)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (stack : KcovSeparated layout (InRange s.data.regs.rsp.toBitVec 8)) :
    KcovReady kind s := by
  by_cases active : layout.mode = 2 ∨ layout.mode = 3
  · exact ready kind layout s preempt returnPC state.1 (state.2.2 active)
      state.2.1 returnRead stack
  · apply inactive_ready kind s
    apply inactive_plan kind layout s preempt returnPC state.1 state.2.1 returnRead
    split <;> intro mode <;> exact active (by simp_all)

/-- Re-establish all runtime callback state after its named service contract.
    Readiness of the next call is a consequence of this physical result. -/
theorem state_preserved (kind : KcovKind) (layout : KcovLayout)
    (s t : MachineState) (preempt : BitVec 32) (returnPC : BitVec 64)
    (state : KcovState layout preempt s.data.dmem)
    (returnRead : load64 s.data.dmem s.data.regs.rsp.toBitVec = some returnPC)
    (metadataSeparate : KcovSeparated layout (KcovMetadataBytes layout))
    (preemptSeparate : KcovSeparated layout (InRange preemptCountAddress 4))
    (effect : KcovEffect kind s t)
    (serviceFrame : EqualOutside (KcovWrites kind s) s.data.dmem t.data.dmem) :
    KcovState layout preempt t.data.dmem ∧
      EqualOutside (KcovBufferBytes layout) s.data.dmem t.data.dmem := by
  by_cases active : layout.mode = 2 ∨ layout.mode = 3
  · have buffer := state.2.2 active
    have frame := effect_frame kind layout s t preempt returnPC state.1 buffer
      state.2.1 returnRead serviceFrame
    refine ⟨⟨metadata_frame layout _ _ state.1 frame metadataSeparate, ?_, ?_⟩, frame⟩
    · have read := frame.loadInt preemptCountAddress 4 (by
        intro byte bound written
        exact preemptSeparate _ written ⟨byte, bound, rfl⟩)
      simpa only [load32, ← read] using state.2.1
    · intro _
      exact effect_preserves_buffer kind layout s t preempt returnPC state.1 buffer
        state.2.1 returnRead effect
  · have plan := inactive_plan kind layout s preempt returnPC state.1 state.2.1 returnRead
      (by split <;> intro mode <;> exact active (by simp_all))
    have same := inactive_effect kind s t plan effect
    rw [same]
    exact ⟨state, fun _ _ => rfl⟩

/-- Stack pushes and the successful reference-count store preserve callback
    state by byte separation, independently of any later execution. -/
theorem state_frame (layout : KcovLayout) (preempt : BitVec 32) (before after : Mem 64)
    (state : KcovState layout preempt before) (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes before after)
    (separate : ∀ address, KcovStateBytes layout address → ¬writes address) :
    KcovState layout preempt after := by
  have field (base : BitVec 64) (width : Nat)
      (part : ∀ address, InRange base width address → KcovStateBytes layout address) :
      before.loadInt base width = after.loadInt base width := by
    apply frame.loadInt
    intro byte bound
    exact separate _ (part _ ⟨byte, bound, rfl⟩)
  have task := field currentTaskAddress 8 (fun _ inside => .inl (.inl inside))
  have mode := field (layout.task+0x6e0) 4 (fun _ inside => .inl (.inr (.inl inside)))
  have capacity := field (layout.task+0x6e4) 4 (fun _ inside => .inl (.inr (.inr (.inl inside))))
  have area := field (layout.task+0x6e8) 8 (fun _ inside => .inl (.inr (.inr (.inr (.inl inside)))))
  have softirq := field (layout.task+0x704) 4 (fun _ inside => .inl (.inr (.inr (.inr (.inr inside)))))
  have pc := field preemptCountAddress 4 (fun _ inside => .inr (.inl inside))
  refine ⟨?_, ?_, ?_⟩
  · simpa only [KcovMetadata, load32, load64, ← task, ← mode, ← capacity, ← area, ← softirq]
      using state.1
  · simpa only [load32, ← pc] using state.2.1
  · intro active
    exact buffer_frame layout before after (state.2.2 active) writes frame
      (fun address inside => separate address (.inr (.inr ⟨active, inside⟩)))

#print axioms plan_normal_form_of_reads
#print axioms plan_normal_form
#print axioms bufferPlan_preserves
#print axioms ready
#print axioms effect_preserves_buffer
#print axioms inactive_plan
#print axioms metadata_frame
#print axioms effect_frame
#print axioms buffer_frame
#print axioms state_ready
#print axioms state_frame
#print axioms state_preserved
end Binary.Kcov
