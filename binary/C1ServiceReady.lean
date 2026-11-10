import C1Interfaces

/-! Result C1, work package 4: what the two service rules use of the caller's
conditions (`insertReady`), in address arithmetic over natural numbers. No
instruction is executed here. -/
namespace Binary.Statements.C1.Proof
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.CommonBitsCoverage Binary.Statements.C1
local instance : Labels := Image.linkedLabels

/-- The insertion's stack span as the caller's conditions name it: the window
below the return word, and the return word. -/
def stackSpan (A : Allocator) (s : MachineState) : Pair.Span :=
  ((s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat, insertWindow + A.depth + 8)

/-- The clauses of `insertReady` the service rules use. -/
structure Ready (L : Layout) (A : Allocator) (c : Context) (s : MachineState) : Prop where
  capacity : c.Needed → 0 < c.coverage.capacity.toNat
  stack : ∀ i < insertWindow + A.depth,
    (s.data.dmem.get? (s.data.regs.rsp.toBitVec - .ofNat 64 (i+1))).isSome = true
  heapStack : spansApart L.heap [stackSpan A s] = true
  heapCache : spansApart L.heap [(cacheWord,8)] = true
  heapBuffers : spansApart L.heap (Trie.callBuffers c) = true
  buffersStack : spansApart (Trie.callBuffers c) [stackSpan A s] = true
  buffersCache : spansApart (Trie.callBuffers c) [(cacheWord,8)] = true
  windowCache : spansApart
    [((s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)).toNat, insertWindow + A.depth)]
    [(cacheWord,8)] = true

private theorem spansApart_sub {left right left' right' : List Pair.Span}
    (ok : spansApart left right = true) (subLeft : ∀ x ∈ left', x ∈ left)
    (subRight : ∀ x ∈ right', x ∈ right) : spansApart left' right' = true := by
  simp only [spansApart, List.all_eq_true] at ok ⊢
  exact fun a ha b hb => ok a (subLeft a ha) b (subRight b hb)

theorem ready_of_insertReady {L : Layout} {A : Allocator} {c : Context} {s : MachineState}
    {family key cidr pid : Nat} {ra : UInt64}
    (ok : insertReady L A c s family key cidr pid ra = .ok ()) : Ready L A c s := by
  unfold insertReady at ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨peer,-,ok⟩ := bind_ok ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨cache,-,ok⟩ := bind_ok ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  unfold frameReady at ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨mapped,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  simp only [↓reduceIte, Bool.false_eq_true] at ok
  obtain ⟨capacity,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨heap,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨buffers,ok⟩ := require_bind_ok _ _ _ _ ok
  obtain ⟨-,ok⟩ := require_bind_ok _ _ _ _ ok
  have caller := require_ok ok
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro needed
    simpa only [needed, ↓reduceIte, decide_eq_true_eq] using capacity
  · intro i bound
    exact List.all_eq_true.mp mapped i (List.mem_range.mpr bound)
  · exact spansApart_sub heap (fun _ h => h) (by simp [callerSpans, stackSpan])
  · exact spansApart_sub heap (fun _ h => h) (by simp [callerSpans])
  · exact spansApart_sub heap (fun _ h => h) (fun x h => by simp [h])
  · exact spansApart_sub buffers (fun _ h => h) (by simp [callerSpans, stackSpan])
  · exact spansApart_sub buffers (fun _ h => h) (by simp [callerSpans])
  · exact spansApart_sub caller (fun _ h => h) (by simp [callerSpans])

end Binary.Statements.C1.Proof
