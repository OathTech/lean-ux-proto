import FdLayouts
import Memory
import Leanux.Kernel.Defs

namespace Binary.FdHeap
open Leanux
abbrev Address := BitVec 64

/-- Names are injective among relevant file allocations, not among slots.
    Zero-count files awaiting deferred fput remain relevant. -/
structure Names (relevant : FileId → Prop) where
  address : FileId → Address
  nonnull : ∀ id, relevant id → address id ≠ 0
  unique : ∀ i j, relevant i → relevant j → address i = address j → i = j

def pointer (names : FileId → Address) : Option FileId → Address
  | none => 0
  | some id => names id

def Named (relevant : FileId → Prop) : Option FileId → Prop
  | none => True
  | some id => relevant id

theorem pointer_injective {relevant} (names : Names relevant) {first second}
    (hf : Named relevant first) (hs : Named relevant second)
    (equal : pointer names.address first = pointer names.address second) : first = second := by
  cases first with
  | none =>
    cases second with
    | none => rfl
    | some id => exact False.elim (names.nonnull id hs equal.symm)
  | some id =>
    cases second with
    | none => exact False.elim (names.nonnull id hf equal)
    | some other => exact congrArg some (names.unique id other hf hs equal)

def Word (memory : Mem 64) (address value : Address) : Prop :=
  memory.loadInt address 8 = some (value.toNat : Int)

theorem Word.functional {memory address first second}
    (hf : Word memory address first) (hs : Word memory address second) : first = second := by
  apply BitVec.eq_of_toNat_eq
  have equal := Option.some.inj (hf.symm.trans hs)
  omega

/-- Native unsigned-long bitmap words are little-endian. Unused high bits
    in a final word are not constrained by this one-bit observation. -/
def Bit (memory : Mem 64) (base : Address) (index : Nat) (value : Bool) : Prop :=
  ∃ word : BitVec 64,
    Word memory (base + .ofNat 64 (8 * (index / 64))) word ∧ word.getLsbD (index % 64) = value

theorem Bit.functional {memory base index first second}
    (hf : Bit memory base index first) (hs : Bit memory base index second) : first = second := by
  obtain ⟨wf, loadedF, bitF⟩ := hf
  obtain ⟨ws, loadedS, bitS⟩ := hs
  have equal := loadedF.functional loadedS
  subst ws
  exact bitF.symm.trans bitS

theorem Word.frame {before after address value writes}
    (same : EqualOutside writes before after)
    (apart : ∀ i < 8, ¬writes (address + .ofNat 64 i))
    (represented : Word before address value) : Word after address value :=
  (same.loadInt _ _ apart).symm.trans represented

theorem Bit.frame {before after base index value writes}
    (same : EqualOutside writes before after)
    (apart : ∀ i < 8, ¬writes (base + .ofNat 64 (8 * (index / 64)) + .ofNat 64 i))
    (represented : Bit before base index value) : Bit after base index value := by
  obtain ⟨word, loaded, bit⟩ := represented
  exact ⟨word, loaded.frame same apart, bit⟩

structure Storage where
  slots : Address
  opened : Address
  cloexec : Address

/-- Every modeled slot and bitmap bit, including reserved but uninstalled
    descriptors. Open bits and installed pointers are deliberately independent.
    full_fds_bits has no mirror field; its derived consistency is a separate,
    phase-sensitive invariant of the allocator, not imposed here. -/
structure Table (memory : Mem 64) (base : Address) (names : FileId → Address)
    (storage : Storage) (table : Fdtable) : Prop where
  capacity : memory.loadInt (base + .ofNat 64 FdLayouts.fdtable_max_fds) 4 = some (table.maxFds : Int)
  slotPointer : Word memory (base + .ofNat 64 FdLayouts.fdtable_fd) storage.slots
  openPointer : Word memory (base + .ofNat 64 FdLayouts.fdtable_open_fds) storage.opened
  closePointer : Word memory (base + .ofNat 64 FdLayouts.fdtable_close_on_exec) storage.cloexec
  slotSize : table.fd.size = table.maxFds
  openSize : table.openFds.size = table.maxFds
  closeSize : table.closeOnExec.size = table.maxFds
  slots : ∀ i (hi : i < table.fd.size),
    Word memory (storage.slots + .ofNat 64 (8 * i)) (pointer names table.fd[i])
  opened : ∀ i (hi : i < table.openFds.size), Bit memory storage.opened i table.openFds[i]
  cloexec : ∀ i (hi : i < table.closeOnExec.size), Bit memory storage.cloexec i table.closeOnExec[i]

def Reads (base : Address) (storage : Storage) (capacity : Nat) (address : Address) : Prop :=
  InRange (base + .ofNat 64 FdLayouts.fdtable_max_fds) 4 address ∨
  InRange (base + .ofNat 64 FdLayouts.fdtable_fd) 8 address ∨
  InRange (base + .ofNat 64 FdLayouts.fdtable_open_fds) 8 address ∨
  InRange (base + .ofNat 64 FdLayouts.fdtable_close_on_exec) 8 address ∨
  ∃ i < capacity,
    InRange (storage.slots + .ofNat 64 (8 * i)) 8 address ∨
    InRange (storage.opened + .ofNat 64 (8 * (i / 64))) 8 address ∨
    InRange (storage.cloexec + .ofNat 64 (8 * (i / 64))) 8 address

theorem Table.frame {before after base names storage table writes}
    (same : EqualOutside writes before after)
    (apart : ∀ address, Reads base storage table.maxFds address → ¬writes address)
    (represented : Table before base names storage table) : Table after base names storage table := by
  refine {represented with capacity := ?_, slotPointer := ?_, openPointer := ?_, closePointer := ?_, slots := ?_, opened := ?_, cloexec := ?_}
  · exact (same.loadInt _ _ (fun i hi => apart _ (.inl ⟨i, hi, rfl⟩))).symm.trans represented.capacity
  · exact represented.slotPointer.frame same (fun i hi => apart _ (.inr (.inl ⟨i, hi, rfl⟩)))
  · exact represented.openPointer.frame same (fun i hi => apart _ (.inr (.inr (.inl ⟨i, hi, rfl⟩))))
  · exact represented.closePointer.frame same (fun i hi => apart _ (.inr (.inr (.inr (.inl ⟨i, hi, rfl⟩)))))
  · intro i hi
    exact (represented.slots i hi).frame same (fun j hj => apart _
      (.inr (.inr (.inr (.inr ⟨i, by simpa only [represented.slotSize] using hi, .inl ⟨j, hj, rfl⟩⟩)))))
  · intro i hi
    exact (represented.opened i hi).frame same (fun j hj => apart _
      (.inr (.inr (.inr (.inr ⟨i, by simpa only [represented.openSize] using hi, .inr (.inl ⟨j, hj, rfl⟩)⟩)))))
  · intro i hi
    exact (represented.cloexec i hi).frame same (fun j hj => apart _
      (.inr (.inr (.inr (.inr ⟨i, by simpa only [represented.closeSize] using hi, .inr (.inr ⟨j, hj, rfl⟩)⟩)))))

/-- Physical storage is determined by its pointer words. -/
theorem Table.storage_unique {memory base names firstStorage secondStorage first second}
    (hf : Table memory base names firstStorage first) (hs : Table memory base names secondStorage second) :
    firstStorage = secondStorage := by
  have slots := hf.slotPointer.functional hs.slotPointer
  have opened := hf.openPointer.functional hs.openPointer
  have cloexec := hf.closePointer.functional hs.closePointer
  cases firstStorage
  cases secondStorage
  simp_all

theorem Table.functional {relevant memory base firstStorage secondStorage first second}
    (names : Names relevant)
    (hf : Table memory base names.address firstStorage first)
    (hs : Table memory base names.address secondStorage second)
    (nf : ∀ i (hi : i < first.fd.size), Named relevant first.fd[i])
    (ns : ∀ i (hi : i < second.fd.size), Named relevant second.fd[i]) : first = second := by
  have sameStorage := hf.storage_unique hs
  subst secondStorage
  have capacity : first.maxFds = second.maxFds := by
    have words := Option.some.inj (hf.capacity.symm.trans hs.capacity)
    omega
  have slots : first.fd = second.fd := by
    apply Array.ext (by rw [hf.slotSize, hs.slotSize, capacity])
    intro i hi hj
    exact pointer_injective names (nf i hi) (ns i hj) ((hf.slots i hi).functional (hs.slots i hj))
  have opened : first.openFds = second.openFds := by
    apply Array.ext (by rw [hf.openSize, hs.openSize, capacity])
    intro i hi hj
    exact (hf.opened i hi).functional (hs.opened i hj)
  have cloexec : first.closeOnExec = second.closeOnExec := by
    apply Array.ext (by rw [hf.closeSize, hs.closeSize, capacity])
    intro i hi hj
    exact (hf.cloexec i hi).functional (hs.cloexec i hj)
  cases first
  cases second
  simp_all

/-- The traced task is named independently of the current KCOV task.
    This relation is only its files pointer, not the rest of task_struct. -/
def TaskFiles (memory : Mem 64) (task files : Address) : Prop :=
  Word memory (task + .ofNat 64 FdLayouts.task_files) files

/-- fdtGeneration is supplied by publication/lifetime history separately;
    it is not treated as a physical integer or inferred from a fresh pointer. -/
structure Files (memory : Mem 64) (base table : Address) (files : FilesStruct) : Prop where
  count : memory.loadInt (base + .ofNat 64 FdLayouts.files_count) 4 = some (files.count : Int)
  resize : memory.loadInt (base + .ofNat 64 FdLayouts.files_resize_in_progress) 1 =
    some (if files.resizeInProgress then 1 else 0)
  next : memory.loadInt (base + .ofNat 64 FdLayouts.files_next_fd) 4 = some (files.nextFd : Int)
  pointer : Word memory (base + .ofNat 64 FdLayouts.files_fdt) table

def FilesReads (base address : Address) : Prop :=
  InRange (base + .ofNat 64 FdLayouts.files_count) 4 address ∨
  InRange (base + .ofNat 64 FdLayouts.files_resize_in_progress) 1 address ∨
  InRange (base + .ofNat 64 FdLayouts.files_next_fd) 4 address ∨
  InRange (base + .ofNat 64 FdLayouts.files_fdt) 8 address

theorem Files.frame {before after base table files writes}
    (same : EqualOutside writes before after)
    (apart : ∀ address, FilesReads base address → ¬writes address)
    (represented : Files before base table files) : Files after base table files := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (same.loadInt _ _ (fun i hi => apart _ (.inl ⟨i, hi, rfl⟩))).symm.trans represented.count
  · exact (same.loadInt _ _ (fun i hi => apart _ (.inr (.inl ⟨i, hi, rfl⟩)))).symm.trans represented.resize
  · exact (same.loadInt _ _ (fun i hi => apart _ (.inr (.inr (.inl ⟨i, hi, rfl⟩))))).symm.trans represented.next
  · exact represented.pointer.frame same (fun i hi => apart _ (.inr (.inr (.inr ⟨i, hi, rfl⟩))))

theorem TaskFiles.frame {before after task files writes}
    (same : EqualOutside writes before after)
    (apart : ∀ i < 8, ¬writes (task + .ofNat 64 FdLayouts.task_files + .ofNat 64 i))
    (represented : TaskFiles before task files) : TaskFiles after task files :=
  Word.frame same apart represented

#print axioms pointer_injective
#print axioms Word.functional
#print axioms Bit.functional
#print axioms Word.frame
#print axioms Bit.frame
#print axioms Table.frame
#print axioms Table.storage_unique
#print axioms Table.functional
#print axioms Files.frame
#print axioms TaskFiles.frame
end Binary.FdHeap
