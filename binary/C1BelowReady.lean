import C1Interfaces

/-! Result C1, work package 3: what the caller's conditions (`insertReady`)
give a path, as propositions. The executable check is unfolded once here. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- The caller's stack window with the return word (`callerSpans`'s first span). -/
def ownWindow (A : Allocator) (s : MachineState) : Pair.Span :=
  ((s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat, insertWindow + A.depth + 8)

theorem callerSpans_true (A : Allocator) (s : MachineState) (query : Pair.Span) :
    callerSpans s (insertWindow + A.depth) query true = [ownWindow A s,query,(cacheWord,8)] := rfl

theorem callerSpans_head (A : Allocator) (s : MachineState) (query : Pair.Span) :
    (callerSpans s (insertWindow + A.depth) query true).head! = ownWindow A s := rfl

theorem callerSpans_tail (A : Allocator) (s : MachineState) (query : Pair.Span) :
    (callerSpans s (insertWindow + A.depth) query true).tail! = [query,(cacheWord,8)] := rfl

/-- The conjuncts of `insertReady` a path below the placement uses. `window`
is the stack window with the allocator's scratch; `own` is the caller's
spans (`callerSpans`: the window with the return word, the address bytes,
the `node_cache` word). -/
structure ReadyFacts (L : Layout) (A : Allocator) (c : Context) (s : MachineState)
    (family : Nat) (ra : UInt64) : Prop where
  families : family = 4 ∨ family = 6
  cacheAt : readNat s cacheWord 8 = .ok L.cache
  aligned : s.data.regs.rsp.toNat % 8 = 0
  returnWord : s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 = some (ra.toNat : Int)
  stackMapped : ∀ i < insertWindow + A.depth,
    (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 (i+1))).isSome = true
  coverage : Trie.coverageCheck c s.data.dmem = true
  capacity : c.Needed → 0 < c.coverage.capacity.toNat
  forward : s.data.system.bits[10] = false
  heapApart : spansApart L.heap
    ([ownWindow A s,(s.data.regs.rsi.toNat,(if family == 4 then 32 else 128)/8),(cacheWord,8)] ++
      Trie.callServices c ++ Trie.callBuffers c) = true
  serviceStack : spansApart (Trie.callServices c)
    [ownWindow A s] = true
  bufferApart : spansApart (Trie.callBuffers c)
    ([ownWindow A s,(s.data.regs.rsi.toNat,(if family == 4 then 32 else 128)/8),(cacheWord,8)] ++
      Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)]) = true
  preemptApart : spansApart
    ([ownWindow A s] ++
      Trie.callMetadata c ++ Trie.callHeaders c) [(preemptCountAddress.toNat,4)] = true
  callerApart : spansApart
    [((s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat, insertWindow + A.depth)]
    [(s.data.regs.rsi.toNat,(if family == 4 then 32 else 128)/8),(cacheWord,8)] = true

theorem ready_facts {L : Layout} {A : Allocator} {c : Context} {s : MachineState}
    {family key cidr pid : Nat} {ra : UInt64}
    (ready : insertReady L A c s family key cidr pid ra = .ok ()) : ReadyFacts L A c s family ra := by
  unfold insertReady at ready
  obtain ⟨families,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨peer,_,ready⟩ := bind_ok ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨_,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨cache,cacheRead,ready⟩ := bind_ok ready
  obtain ⟨cacheEq,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨-,ready⟩ := require_bind_ok _ _ _ _ ready
  unfold frameReady at ready
  obtain ⟨abi,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨mapped,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨coverage,ready⟩ := require_bind_ok _ _ _ _ ready
  simp only [↓reduceIte] at ready
  obtain ⟨_,service,ready⟩ := bind_ok ready
  have capacity := require_ok service
  obtain ⟨forward,ready⟩ := require_bind_ok _ _ _ _ ready
  simp only [Bool.false_eq_true,↓reduceIte] at ready
  obtain ⟨heapApart,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨serviceStack,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨bufferApart,ready⟩ := require_bind_ok _ _ _ _ ready
  obtain ⟨preemptApart,ready⟩ := require_bind_ok _ _ _ _ ready
  have callerApart := require_ok ready
  rw [callerSpans_true] at heapApart bufferApart
  rw [callerSpans_head] at serviceStack preemptApart
  rw [callerSpans_tail] at callerApart
  have abi : s.data.regs.rsp.toNat % 8 = 0 ∧
      s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8 = some (ra.toNat : Int) := by
    simpa only [Bool.and_eq_true,beq_iff_eq] using abi
  refine ⟨by simpa only [Bool.or_eq_true,beq_iff_eq] using families,eq_of_beq cacheEq ▸ cacheRead,
    abi.1,abi.2,?_,coverage,?_,eq_of_beq forward,heapApart,serviceStack,bufferApart,preemptApart,callerApart⟩
  · intro i bound
    exact List.all_eq_true.mp mapped i (List.mem_range.mpr bound)
  · intro needed
    simpa only [needed,↓reduceIte,decide_eq_true_eq] using capacity

#print axioms ready_facts
end Binary.Statements.C1.Proof
