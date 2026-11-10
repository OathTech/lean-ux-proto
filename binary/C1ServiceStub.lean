import C1ServiceRules

/-! Result C1, work package 4: a stub service in instruction terms, its
allocator state, and the parts of `AllocatorContract` that execute nothing
(`frame`, and what the `alloc` clause's conclusion needs of a store to the
state byte).

The stub is shaped by the finding in `C1ServiceContractFinding`: under the
contract as signed, a conforming service may not change any byte that some
coverage context valid at its entry reads. Every read of a coverage context
is at least two bytes wide. So the stub keeps its ONE mutable byte, the
number of answers given so far, at an address whose two neighbours are
unmapped: no coverage context, no stack scratch and no return word can
contain it. Everything else the allocator needs is read-only (the pending
outcomes, one byte each) or computed (object `k` is at `objects + 128*k`).
This is a stub that meets the signed text, not a model of an allocator. -/
namespace Binary.Statements.C1.Stub
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Statements.C1.Proof
open Kraken.X64.Parser
local instance : Labels := Image.linkedLabels

/-! ## The arena and the code -/

/-- The arena: one span. Its first page holds the state byte (which is also
the `kmem_cache` pointer the callers pass) and the outcome bytes; objects
start at the second page, 128 bytes apart. -/
def arenaBase : Nat := 0xa00000
def arenaSize : Nat := 0x10000
def state : Nat := 0xa00001
def table : Nat := 0xa00100
def objects : Nat := 0xa01000
def slots : Nat := 8
def slot (index : Nat) : Nat := objects + 128 * index

/-- The stub's layout, for any table and peers. -/
def layout (tableAt : Nat) (peers : List (PeerId × Nat)) : Layout :=
  ⟨tableAt,peers,[(arenaBase,arenaSize)],state⟩

/-- `kmem_cache_alloc_noprof` as a stub: read the count, advance it, read the
pending outcome; on 1 return object `count`, otherwise NULL. -/
def allocCode : List (Kraken.Sized Directive) :=
  List.zipWith (fun d n => ⟨d, n⟩) (parse("movzbl (%rdi),%ecx
lea    0x1(%rcx),%eax
mov    %al,(%rdi)
movzbl 0xa00100(%rcx),%edx
cmp    $0x1,%edx
jne L_ffffffff81196d40
shl    $0x7,%rcx
lea    0xa01000(%rcx),%rax
ret
xor    %eax,%eax
ret")) [3, 3, 2, 7, 3, 2, 4, 7, 1, 2, 1]

/-- `kmem_cache_free` as a stub: nothing is reused. -/
def freeCode : List (Kraken.Sized Directive) :=
  List.zipWith (fun d n => ⟨d, n⟩) (parse("ret")) [1]

def fetch (pc : Int64) : Option Decoded :=
  (Image.fetchIn allocEntry allocCode pc).orElse fun _ => Image.fetchIn freeEntry freeCode pc

/-! ## The allocator's state -/

/-- The outcome byte of a pending record: 1 for a success, 0 otherwise. -/
def outcome (record : HiddenRecord) : Int := if record.bytes.head? = some 1 then 1 else 0

/-- `Idle m live stream`: `count` answers have been given; the state byte
holds `count` and its neighbours are unmapped; the next outcome bytes are
those of `stream`; the object of every pending success is zeroed; the
objects handed out are earlier ones. -/
def Idle (m : Mem 64) (live : List Nat) (stream : List HiddenRecord) : Prop :=
  ∃ count : Nat,
    m.loadInt (.ofNat 64 state) 1 = some (count : Int) ∧
    count + stream.length ≤ slots ∧
    m.get? (.ofNat 64 (state-1)) = none ∧ m.get? (.ofNat 64 (state+1)) = none ∧
    (∀ i (bound : i < stream.length),
      m.loadInt (.ofNat 64 (table+(count+i))) 1 = some (outcome stream[i])) ∧
    (∀ i (bound : i < stream.length), stream[i].bytes.head? = some 1 →
      readNat ⟨{dmem := m},0⟩ (slot (count+i)) nodeSize = .ok 0) ∧
    (∀ object ∈ live, ∃ index < count, object = slot index)

def allocator : Allocator := ⟨Idle,8⟩

/-! ## Where the allocator's bytes are -/

theorem arena_contains {tableAt : Nat} {peers : List (PeerId × Nat)} {x : Nat}
    (lower : arenaBase ≤ x) (upper : x < arenaBase + arenaSize) :
    (layout tableAt peers).Arena (.ofNat 64 x) := by
  refine ⟨(arenaBase,arenaSize),List.mem_singleton.mpr rfl,?_⟩
  have offset : x - arenaBase < arenaSize := by omega
  have sum : arenaBase + (x - arenaBase) = x := by omega
  refine ⟨x - arenaBase,offset,?_⟩
  rw [← BitVec.ofNat_add, sum]

/-- A byte below the objects, or in an object not yet handed out, is in no
object handed out. -/
theorem not_kept {live : List Nat} {count : Nat}
    (lives : ∀ object ∈ live, ∃ index < count, object = slot index) (small : count ≤ slots) {x : Nat}
    (place : x < objects ∨ ∃ index, count ≤ index ∧ index < slots ∧ slot index ≤ x ∧ x < slot index + 72) :
    ¬Kept live (.ofNat 64 x) := by
  rintro ⟨object,member,inside⟩
  obtain ⟨index,before,rfl⟩ := lives object member
  have range := (inRange_iff (.ofNat 64 (slot index)) nodeSize (by
    simp only [BitVec.toNat_ofNat, slot, objects, nodeSize, slots] at *
    omega) (.ofNat 64 x)).mp inside
  simp only [BitVec.toNat_ofNat, slot, objects, nodeSize, slots] at *
  rcases place with below | ⟨other,least,most,lower,upper⟩ <;> omega

/-- Memories that agree on the arena outside the objects handed out agree on
every read the allocator's state is made of. -/
theorem same_bytes {tableAt : Nat} {peers : List (PeerId × Nat)} {m m' : Mem 64} {live : List Nat}
    {count : Nat} (lives : ∀ object ∈ live, ∃ index < count, object = slot index) (small : count ≤ slots)
    (agree : ∀ a, (layout tableAt peers).Arena a → ¬Kept live a → m.get? a = m'.get? a)
    (x size : Nat) (inArena : arenaBase ≤ x ∧ x + size ≤ arenaBase + arenaSize)
    (place : x + size ≤ objects ∨ ∃ index, count ≤ index ∧ index < slots ∧ slot index ≤ x ∧
      x + size ≤ slot index + 72) :
    m.loadBytes (.ofNat 64 x) size = m'.loadBytes (.ofNat 64 x) size := by
  unfold Mem.loadBytes
  congr 1
  apply List.map_congr_left
  intro i member
  have bound := List.mem_range.mp member
  rw [← BitVec.ofNat_add]
  refine agree _ (arena_contains (by omega) (by omega)) (not_kept lives small ?_)
  rcases place with below | ⟨index,least,most,lower,upper⟩
  · exact .inl (by omega)
  · exact .inr ⟨index,least,most,by omega,by omega⟩

/-- The contract's `frame` clause. -/
theorem idle_frame {tableAt : Nat} {peers : List (PeerId × Nat)} {m m' : Mem 64} {live : List Nat}
    {stream : List HiddenRecord} (idle : Idle m live stream)
    (agree : ∀ a, (layout tableAt peers).Arena a → ¬Kept live a → m.get? a = m'.get? a) :
    Idle m' live stream := by
  obtain ⟨count,stateRead,room,before,after,outcomes,zeroed,lives⟩ := idle
  have small : count ≤ slots := by omega
  have bytes := same_bytes lives small agree
  refine ⟨count,?_,room,?_,?_,?_,?_,lives⟩
  · unfold Mem.loadInt at stateRead ⊢
    rw [← bytes state 1 (by decide) (.inl (by decide))]
    exact stateRead
  · rw [← agree _ (arena_contains (by decide) (by decide)) (not_kept lives small (.inl (by decide)))]
    exact before
  · rw [← agree _ (arena_contains (by decide) (by decide)) (not_kept lives small (.inl (by decide)))]
    exact after
  · intro i bound
    have read := outcomes i bound
    unfold Mem.loadInt at read ⊢
    rw [← bytes (table+(count+i)) 1 (by simp only [table, arenaBase, arenaSize, slots] at *; omega)
      (.inl (by simp only [table, objects, slots] at *; omega))]
    exact read
  · intro i bound success
    have read := zeroed i bound success
    simp only [readNat] at read ⊢
    rw [← bytes (slot (count+i)) nodeSize
      (by simp only [slot, objects, nodeSize, arenaBase, arenaSize, slots] at *; omega)
      (.inr ⟨count+i,by omega,by omega,by omega,by simp only [nodeSize]; omega⟩)]
    exact read

#print axioms idle_frame
end Binary.Statements.C1.Stub
