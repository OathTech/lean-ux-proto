import C1WitnessScene
import C1ServiceRules
import PairFrameProof
import MemoryBytes

/-! Result C1, open proposition `WitnessHolds`: the facts about the concrete
memory of `C1WitnessScene` that `Executed` and `ServiceActive` need.

A `Mem 64` is a hash map, which the kernel does not evaluate. Every read of
`base` and of `over m` is therefore moved to the list function
`lookup baseSpans` first (`base_get`, `over_get`); what is left of an
executable check is then a closed Boolean, settled by kernel evaluation. -/
namespace Binary.Statements.C1.Witness
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1 Binary.Statements.C1.Proof
local instance : Labels := Image.linkedLabels

/-! ## Bytes of a built memory -/

/-- One store at a natural-number address, read back at any address. -/
theorem store_get (m : Mem 64) (b : Nat) (bytes : List UInt8) (fits : b + bytes.length < 2^64)
    (a : BitVec 64) :
    (m.storeBytes (.ofNat 64 b) bytes).get? a =
      if b ≤ a.toNat ∧ a.toNat < b + bytes.length then bytes[a.toNat - b]? else m.get? a := by
  have bound := a.isLt
  split
  · next inside =>
    have place : a = .ofNat 64 b + .ofNat 64 (a.toNat - b) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      omega
    have offset : a.toNat - b < bytes.length := by omega
    rw [List.getElem?_eq_getElem offset]
    conv => lhs; rw [place]
    exact MemoryBytes.get_storeBytes m _ bytes (by omega) _ offset
  · next outside =>
    have same := Stub.storeBytes_frame m (.ofNat 64 b) bytes a (by
      have apart := Stub.outside_range b bytes.length a.toNat (by omega) fits bound
      rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at apart)
    exact same.symm

def spansFit (spans : List (Nat × List UInt8)) : Bool := spans.all fun span => span.1 + span.2.length < 2^64

theorem build_get (spans : List (Nat × List UInt8)) (fit : spansFit spans = true) (a : BitVec 64) :
    (build spans).get? a = lookup spans a.toNat := by
  induction spans with
  | nil => simp [build, lookup]
  | cons span rest ih =>
    obtain ⟨b,bytes⟩ := span
    simp only [spansFit, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at fit
    simp only [build, lookup]
    rw [store_get _ _ _ fit.1, ih fit.2]

theorem base_build : base = build baseSpans := rfl

theorem base_get (a : BitVec 64) : base.get? a = lookup baseSpans a.toNat := by
  rw [base_build]
  exact build_get _ (by decide +kernel) a

theorem over_get (m : Mem 64) (a : BitVec 64) :
    (over m).get? a = if heapAt a.toNat then m.get? a else lookup baseSpans a.toNat := by
  have first := base_get a
  simp only [Std.ExtHashMap.get?_eq_getElem?] at first ⊢
  simp only [over, Std.ExtHashMap.getElem?_union, Std.ExtHashMap.getElem?_filter', first]
  cases heapAt a.toNat <;> cases m[a]? <;> cases lookup baseSpans a.toNat <;> simp

theorem heap_at {a : BitVec 64} (inside : L.Heap a) : heapAt a.toNat = true := by
  obtain ⟨span,member,i,bound,rfl⟩ := inside
  have valid : L.heap.all (fun span => span.1 + span.2 < 2^64) = true := by decide +kernel
  have small := List.all_eq_true.mp valid span member
  simp only [decide_eq_true_eq] at small
  simp only [heapAt, List.any_eq_true]
  refine ⟨span,member,?_⟩
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

theorem over_heap (m : Mem 64) : ∀ a, L.Heap a → m.get? a = (over m).get? a := by
  intro a inside
  rw [over_get, heap_at inside]
  rfl

/-! ## The same bytes without long lists

Reading far into `List.replicate n 0` costs the kernel a step per index, so
the base memory's bytes are restated over pieces whose fills answer at once. -/

inductive Piece where
  | fill (a n : Nat) (v : UInt8)
  | data (a : Nat) (bytes : List UInt8)

def Piece.span : Piece → Nat × List UInt8
  | .fill a n v => (a,List.replicate n v)
  | .data a bytes => (a,bytes)

def pieceAt : List Piece → Nat → Option UInt8
  | [], _ => none
  | .fill a n v :: rest, x => if a ≤ x ∧ x < a + n then some v else pieceAt rest x
  | .data a bytes :: rest, x => if a ≤ x ∧ x < a + bytes.length then bytes[x - a]? else pieceAt rest x

theorem pieceAt_lookup (pieces : List Piece) (x : Nat) :
    lookup (pieces.map Piece.span) x = pieceAt pieces x := by
  induction pieces with
  | nil => rfl
  | cons piece rest ih =>
    cases piece with
    | fill a n v =>
      simp only [List.map_cons, Piece.span, lookup, pieceAt, List.length_replicate, ih]
      split
      · next inside =>
        have small : x - a < n := by omega
        simp [small]
      · rfl
    | data a bytes => simp only [List.map_cons, Piece.span, lookup, pieceAt, ih]

def peerPieces (a : Nat) : List Piece :=
  [.data (a+AllowedipsMutationLayout.allowedips_list) (le 8 (a+AllowedipsMutationLayout.allowedips_list)),
   .data (a+AllowedipsMutationLayout.allowedips_list+8) (le 8 (a+AllowedipsMutationLayout.allowedips_list)),
   .data (a+Root.nodeOffsets.peerRefcount) (le 4 1),
   .fill a Layouts.peerSize 0]

def basePieces : List Piece :=
  [.fill Stub.objects (128*Stub.slots) 0,.data Stub.table (five.map Stub.outcomeByte),.data Stub.state [0],
   .data stack (le 8 ra.toNat),
   .data serviceStack (le 8 site.toNat),
   .fill (stack-0x800) 0x1000 0,
   .data preemptCountAddress.toNat (le 4 512),
   .data currentTaskAddress.toNat (le 8 task),
   .data softirqPendingAddress.toNat (le 2 0),
   .data (task+0x6e0) (le 4 2),
   .data (task+0x6e4) (le 4 capacity),
   .data (task+0x6e8) (le 8 area),
   .data (task+0x704) (le 4 0),
   .fill area (8*capacity) 0,
   .fill tableAt AllowedipsMutationLayout.tableSize 0] ++
  peerPieces 0x600000 ++ peerPieces 0x601000 ++
  [.data cacheWord (le 8 Stub.state),
   .data (keyAt 0) [10,0,0,0],.data (keyAt 1) [11,0,0,1],.data (keyAt 2) [12,0,0,1],.data (keyAt 3) [10,0,0,5]]

theorem base_pieces : baseSpans = basePieces.map Piece.span := rfl

/-- The byte of the base memory at `x`. -/
def baseAt (x : Nat) : Option UInt8 := pieceAt basePieces x

theorem lookup_base (x : Nat) : lookup baseSpans x = baseAt x := by
  rw [base_pieces]
  exact pieceAt_lookup _ x

/-! ## Reads as list functions -/

/-- `n` bytes from `a` of the base memory, without a memory. -/
def pureBytes (a : BitVec 64) (n : Nat) : Option (List UInt8) :=
  ((List.range n).map fun i => baseAt (a + .ofNat 64 i).toNat).allSome

/-- No byte of the range is a heap byte. -/
def outside (a : BitVec 64) (n : Nat) : Bool := (List.range n).all fun i => !heapAt (a + .ofNat 64 i).toNat

theorem base_at (a : BitVec 64) : base.get? a = baseAt a.toNat := by
  rw [base_get, lookup_base]

theorem base_loadBytes (a : BitVec 64) (n : Nat) : base.loadBytes a n = pureBytes a n := by
  simp only [Mem.loadBytes, pureBytes, base_at]

theorem base_loadInt (a : BitVec 64) (n : Nat) : base.loadInt a n = (pureBytes a n).map Int.ofBytes := by
  simp only [Mem.loadInt, base_loadBytes]

theorem over_get_outside (m : Mem 64) (a : BitVec 64) (apart : heapAt a.toNat = false) :
    (over m).get? a = baseAt a.toNat := by
  rw [over_get, apart, lookup_base]
  rfl

theorem over_loadBytes (m : Mem 64) (a : BitVec 64) (n : Nat) (apart : outside a n = true) :
    (over m).loadBytes a n = pureBytes a n := by
  simp only [Mem.loadBytes, pureBytes]
  congr 1
  apply List.map_congr_left
  intro i member
  have here := List.all_eq_true.mp apart i member
  exact over_get_outside m _ (by simpa using here)

theorem over_loadInt (m : Mem 64) (a : BitVec 64) (n : Nat) (apart : outside a n = true) :
    (over m).loadInt a n = (pureBytes a n).map Int.ofBytes := by
  simp only [Mem.loadInt, over_loadBytes m a n apart]

/-- An executable check that returned `ok`. -/
def passed (r : Except String Unit) : Bool := match r with | .ok () => true | _ => false

theorem of_passed {r : Except String Unit} (ok : passed r = true) : r = .ok () := by
  match r, ok with
  | .ok (), _ => rfl

/-! ## The base memory -/

theorem insert_ready_first :
    insertReady L allocator c (insertEntry base 0 24 0x600000) 4 0x0a000000 24 0 ra = .ok () := by
  apply of_passed
  simp only [insertReady, frameReady, readNat, Trie.networkKeyCheck, Trie.coverageCheck,
    Trie.coverageDataCheck, load32, load64, insertEntry, base_loadBytes, base_loadInt, base_at]
  decide +kernel

theorem base_empty : ∃ d, world.wg.dev = some d ∧ emptyTable L base d = .ok () := by
  refine ⟨_,rfl,?_⟩
  apply of_passed
  simp only [emptyTable, readNat, base_loadBytes]
  decide +kernel

theorem base_idle : Stub.Idle base [] five :=
  Stub.idle_initial (build preSpans) five (by decide)
    (by rw [build_get _ (by decide +kernel)]; decide +kernel)
    (by rw [build_get _ (by decide +kernel)]; decide +kernel)

theorem needed : c.Needed := by decide +kernel

/-! ## The service's own entry state -/

theorem service_frame : EntryFrame serviceEntry site := by
  simp only [EntryFrame, serviceEntry, base_loadInt]
  decide +kernel

theorem service_coverage : c.At base := by
  apply Trie.coverageCheck_sound
  simp only [Trie.coverageCheck, Trie.coverageDataCheck, load32, load64, base_loadInt]
  decide +kernel

theorem service_header : load64 base c.coverage.area = some (.ofNat 64 0) := by
  simp only [load64, base_loadInt]
  decide +kernel

theorem service_saved : base.loadInt (serviceEntry.data.regs.rsp.toBitVec - 8) 8 = some 0 := by
  simp only [base_loadInt]
  decide +kernel

theorem service_ready : ServiceReady L allocator c serviceEntry :=
  Proof.serviceReady (s := insertEntry base 0 24 0x600000) (ready_of_insertReady insert_ready_first)
    ⟨by decide +kernel,by decide +kernel,fun _ _ => rfl,fun _ _ mapped => mapped,by decide +kernel,
      service_coverage⟩

/-! ## Entry states over another memory's heap -/

theorem over_all_get (m : Mem 64) (n : Nat) (f : Nat → BitVec 64)
    (apart : (List.range n).all (fun i => !heapAt (f i).toNat) = true) :
    ((List.range n).all fun i => ((over m).get? (f i)).isSome) =
      (List.range n).all fun i => (baseAt (f i).toNat).isSome := by
  have same : ∀ i ∈ List.range n, ((over m).get? (f i)).isSome = (baseAt (f i).toNat).isSome := by
    intro i member
    have here := List.all_eq_true.mp apart i member
    rw [over_get_outside m _ (by simpa using here)]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun all i member => same i member ▸ all i member,fun all i member => same i member ▸ all i member⟩

theorem over_all_loadInt (m : Mem 64) (n k : Nat) (f : Nat → BitVec 64)
    (apart : (List.range n).all (fun i => outside (f i) k) = true) :
    ((List.range n).all fun i => ((over m).loadInt (f i) k).isSome) =
      (List.range n).all fun i => ((pureBytes (f i) k).map Int.ofBytes).isSome := by
  have same : ∀ i ∈ List.range n,
      ((over m).loadInt (f i) k).isSome = ((pureBytes (f i) k).map Int.ofBytes).isSome := by
    intro i member
    rw [over_loadInt m _ _ (List.all_eq_true.mp apart i member)]
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  exact ⟨fun all i member => same i member ▸ all i member,fun all i member => same i member ▸ all i member⟩

/-! ## The caller's conditions from their clauses -/

theorem bind_require {α : Type} {condition : Bool} {error : String} {rest : Unit → Except String α}
    (holds : condition = true) : (require condition error >>= rest) = rest () := by
  subst holds
  rfl

theorem frameReady_insert {L : Layout} {c : Context} {s : MachineState} {ra : UInt64} {window : Nat}
    {query : Pair.Span}
    (abi : (s.data.regs.rsp.toNat % 8 == 0 &&
      s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 == some (ra.toNat : Int)) = true)
    (mapping : ((List.range window).all fun i =>
      (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 (i+1))).isSome) = true)
    (coverage : Trie.coverageCheck c s.data.dmem = true)
    (room : (if c.Needed then decide (0 < c.coverage.capacity.toNat) else true) = true)
    (forward : (s.data.system.bits[10] == false) = true)
    (heap : spansApart L.heap (callerSpans s window query true ++ Trie.callServices c ++ Trie.callBuffers c) = true)
    (services : spansApart (Trie.callServices c) [(callerSpans s window query true).head!] = true)
    (buffers : spansApart (Trie.callBuffers c)
      (callerSpans s window query true ++ Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)]) = true)
    (preempt : spansApart ([(callerSpans s window query true).head!] ++ Trie.callMetadata c ++ Trie.callHeaders c)
      [(preemptCountAddress.toNat,4)] = true)
    (caller : spansApart [((s.data.regs.rsp.toBitVec - .ofNat 64 window).toNat, window)]
      (callerSpans s window query true).tail! = true) :
    frameReady L c s ra window query true false = .ok () := by
  unfold frameReady
  simp only [bind_require abi, bind_require mapping, bind_require coverage, bind_require room,
    bind_require forward, bind_require heap, bind_require services, bind_require buffers,
    bind_require preempt, caller, ↓reduceIte, Bool.false_eq_true]
  rfl

theorem frameReady_lookup {L : Layout} {c : Context} {s : MachineState} {ra : UInt64} {window : Nat}
    {query : Pair.Span}
    (abi : (s.data.regs.rsp.toNat % 8 == 0 &&
      s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 == some (ra.toNat : Int)) = true)
    (mapping : ((List.range window).all fun i =>
      (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 (i+1))).isSome) = true)
    (coverage : Trie.coverageCheck c s.data.dmem = true)
    (second : Trie.coverageDataCheck ⟨c.coverage,c.preempt+512⟩ s.data.dmem = true)
    (hard : ((c.preempt+512) &&& 0x000f0000 == 0) = true)
    (pending : (if LookupPendingRead c.preempt then
      s.data.dmem.loadInt softirqPendingAddress 2 == some 0 else true) = true)
    (heap : spansApart L.heap (callerSpans s window query false ++ Trie.callServices c ++ Trie.callBuffers c) = true)
    (services : spansApart (Trie.callServices c) [(callerSpans s window query false).head!] = true)
    (buffers : spansApart (Trie.callBuffers c)
      (callerSpans s window query false ++ Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)]) = true)
    (preempt : spansApart ([(callerSpans s window query false).head!] ++ Trie.callMetadata c ++ Trie.callHeaders c)
      [(preemptCountAddress.toNat,4)] = true)
    (caller : spansApart [((s.data.regs.rsp.toBitVec - .ofNat 64 window).toNat, window)]
      (callerSpans s window query false).tail! = true) :
    frameReady L c s ra window query false true = .ok () := by
  unfold frameReady
  simp only [bind_require abi, bind_require mapping, bind_require coverage, bind_require second,
    bind_require hard, bind_require pending, bind_require heap, bind_require services, bind_require buffers,
    bind_require preempt, caller, ↓reduceIte, Bool.false_eq_true]
  rfl

theorem insertReady_v4 {L : Layout} {A : Allocator} {c : Context} {s : MachineState} {key cidr pid peer : Nat}
    {ra : UInt64}
    (entry : (s.pc == AllowedipsMutationImage.Insert4.entry) = true)
    (table : (s.data.regs.rdi.toNat == L.table) = true)
    (address : Trie.address L.peers (some pid) = .ok peer)
    (registered : (peer != 0 && s.data.regs.rcx.toNat == peer) = true)
    (length : (s.data.regs.rdx.toNat % 256 == cidr) = true)
    (query : Trie.networkKeyCheck s.data.dmem s.data.regs.rsi.toBitVec 32 key = true)
    (cache : readNat s cacheWord 8 = .ok L.cache)
    (stackPeers : spansApart
      [((s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat, insertWindow + A.depth)]
      (L.peers.map fun (_,a) => (a,Layouts.peerSize)) = true)
    (frame : frameReady L c s ra (insertWindow + A.depth) (s.data.regs.rsi.toNat, 4) true false = .ok ()) :
    insertReady L A c s 4 key cidr pid ra = .ok () := by
  unfold insertReady
  simp only [BEq.rfl, Bool.true_or, ↓reduceIte, bind_require entry, bind_require table, address,
    bind_require length, bind_require query, cache, bind_require stackPeers, Nat.reduceDiv, frame]
  simp [require, registered, bind, Except.bind]

theorem lookupReady_v4 {L : Layout} {c : Context} {s : MachineState} {key root : Nat} {ra : UInt64}
    (entry : (s.pc == AllowedipsImage.Lookup.entry) = true)
    (slot : readNat s (L.table + AllowedipsMutationLayout.root4) 8 = .ok root)
    (argument : (s.data.regs.rdi.toNat == root) = true)
    (width : (s.data.regs.rsi.toNat == 32) = true)
    (query : Trie.networkKeyCheck s.data.dmem s.data.regs.rdx.toBitVec 32 key = true)
    (frame : frameReady L c s ra lookupWindow (s.data.regs.rdx.toNat, 4) false true = .ok ()) :
    lookupReady L c s 4 key ra = .ok () := by
  unfold lookupReady
  simp only [BEq.rfl, Bool.true_or, ↓reduceIte, bind_require entry, slot,
    bind_require width, bind_require query, Nat.reduceDiv, frame]
  simp [require, argument, bind, Except.bind]

/-! ## Entry states over another memory's heap: the caller's conditions -/

theorem over_loadBytes_heap (m : Mem 64) (a : BitVec 64) (n : Nat)
    (inside : (List.range n).all (fun i => heapAt (a + .ofNat 64 i).toNat) = true) :
    (over m).loadBytes a n = m.loadBytes a n := by
  simp only [Mem.loadBytes]
  congr 1
  apply List.map_congr_left
  intro i member
  rw [over_get, List.all_eq_true.mp inside i member]
  rfl

/-- The value of a read that succeeded. -/
def valueOf (r : Except String Nat) : Option Nat := match r with | .ok v => some v | _ => none

theorem of_valueOf {r : Except String Nat} {v : Nat} (read : valueOf r = some v) : r = .ok v := by
  match r, read with
  | .ok _, same => exact congrArg Except.ok (Option.some.inj same)

/-- One clause of the caller's conditions at an entry state over `over m`:
unfold the clause to its reads, move the reads (all outside the heap) to the
base memory's bytes, and evaluate what is left, which no longer mentions `m`. -/
local macro "clause" : tactic => `(tactic|
  (try simp only [insertEntry, lookupEntry, callerSpans, readNat, Trie.networkKeyCheck, Trie.coverageCheck,
     Trie.coverageDataCheck, load32, load64]
   try simp (disch := decide +kernel) only [over_all_get, over_all_loadInt]
   try simp (disch := decide +kernel) only [over_loadBytes, over_loadInt]
   decide +kernel))

/-- The address bytes, from the word they hold. -/
theorem key_check {memory : Mem 64} {a : BitVec 64} {key : Nat} (word : BitVec 32)
    (read : load32 memory a = some word) (same : ((Allowedips.swap32 word).toNat == key) = true) :
    Trie.networkKeyCheck memory a 32 key = true := by
  simp [Trie.networkKeyCheck, read, same]

theorem over_load32 (m : Mem 64) (a : BitVec 64) (apart : outside a 4 = true) :
    load32 (over m) a = (pureBytes a 4).map fun bytes => .ofInt 32 (Int.ofBytes bytes) := by
  rw [load32, over_loadInt m a 4 apart, Option.map_map]
  rfl

/-- The address bytes of call `i` over any heap. -/
theorem over_key (m : Mem 64) (i key : Nat) (word : BitVec 32)
    (apart : outside (.ofNat 64 (keyAt i)) 4 = true)
    (value : (pureBytes (.ofNat 64 (keyAt i)) 4).map (fun bytes => BitVec.ofInt 32 (Int.ofBytes bytes)) =
      some word)
    (same : ((Allowedips.swap32 word).toNat == key) = true) :
    Trie.networkKeyCheck (over m) (.ofNat 64 (keyAt i)) 32 key = true :=
  key_check word ((over_load32 m _ apart).trans value) same

theorem flags_forward : (flags.bits[10] == false) = true := by decide

theorem insert_ready_second (m : Mem 64) :
    insertReady L allocator c (insertEntry (over m) 1 32 0x601000) 4 0x0b000001 32 1 ra = .ok () := by
  refine insertReady_v4 (peer := 0x601000) ?_ ?_ rfl ?_ ?_
    (over_key m 1 _ 0x0100000b (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (of_valueOf ?_) ?_ (frameReady_insert ?_ ?_ ?_ ?_ flags_forward ?_ ?_ ?_ ?_ ?_)
  all_goals clause

theorem insert_ready_third (m : Mem 64) :
    insertReady L allocator c (insertEntry (over m) 2 32 0x600000) 4 0x0c000001 32 0 ra = .ok () := by
  refine insertReady_v4 (peer := 0x600000) ?_ ?_ rfl ?_ ?_
    (over_key m 2 _ 0x0100000c (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (of_valueOf ?_) ?_ (frameReady_insert ?_ ?_ ?_ ?_ flags_forward ?_ ?_ ?_ ?_ ?_)
  all_goals clause

theorem lookup_ready (m : Mem 64) (root : Nat) (small : root < 2^64)
    (read : readNat ⟨{dmem := m},0⟩ (L.table+AllowedipsMutationLayout.root4) 8 = .ok root) :
    lookupReady L c (lookupEntry (over m) root) 4 0x0a000005 ra = .ok () := by
  have slot := over_loadBytes_heap m (.ofNat 64 (L.table+AllowedipsMutationLayout.root4)) 8 (by decide +kernel)
  refine lookupReady_v4 (root := root) ?_ ?_ ?_ ?_
    (over_key m 3 _ 0x0500000a (by decide +kernel) (by decide +kernel) (by decide +kernel))
    (frameReady_lookup ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  case refine_2 =>
    simp only [readNat, lookupEntry, slot]
    simpa only [readNat] using read
  case refine_3 =>
    simp only [lookupEntry, UInt64.toNat_ofNat', Nat.mod_eq_of_lt small, BEq.rfl]
  all_goals clause

#print axioms base_get
#print axioms over_get
#print axioms heap_at
#print axioms over_heap
#print axioms base_empty
#print axioms base_idle
#print axioms insert_ready_first
#print axioms insert_ready_second
#print axioms insert_ready_third
#print axioms lookup_ready
#print axioms needed
#print axioms service_frame
#print axioms service_coverage
#print axioms service_header
#print axioms service_saved
#print axioms service_ready
end Binary.Statements.C1.Witness
