import C1TrunkThrough
/-! Result C1, package 2: `PathTooLong`. The over-long prefix: wrapper,
increment, `add`'s first guard, `-EINVAL`, both returns. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

theorem step_tooLong {d : Device} {family key cidr pid : Nat} {placed : Option NodeId} {exact : Bool}
    {outcomes : List Bool}
    (hc : (step d family key cidr pid placed exact outcomes).case = .tooLong) :
    cidr > (if family == 4 then 32 else 128) ∧
    step d family key cidr pid placed exact outcomes = ⟨.tooLong,-EINVAL,bump d,0⟩ := by
  by_cases long : cidr > (if family == 4 then 32 else 128)
  · exact ⟨long,by simp only [step, long, ↓reduceIte]⟩
  · exfalso
    unfold step at hc
    simp only [long, ↓reduceIte] at hc
    repeat' split at hc
    all_goals first | cases hc | simp at hc

/-- `add`'s frame window, inside the insertion's stack window. -/
theorem window_tight {c : Context} {s a : MachineData} {seq : BitVec 64} {v4 : Bool} {key : Nat}
    (atAdd : AtAdd c s seq v4 key a) (W : Nat) (wide : 200 ≤ W) (x : BitVec 64) (h : Window a x) :
    InRange (s.regs.rsp.toBitVec - .ofNat 64 W) (W - frameSize v4 + 8) x := by
  have fs := frameSize_range v4
  have h' : InRange (a.regs.rsp.toBitVec - .ofNat 64 104) 112 x := h
  rw [atAdd.stackAt, sub_sub_ofNat] at h'
  exact below_sub _ (frameSize v4 + 104) 112 W (W - frameSize v4 + 8) (by omega) (by omega) x h'

theorem range_mono (base : BitVec 64) (n m : Nat) (le : n ≤ m) (x : BitVec 64) (h : InRange base n x) :
    InRange base m x := by
  obtain ⟨i,hi,eq⟩ := h
  exact ⟨i,by omega,eq⟩

theorem arena_heap {L : Statements.C1.Layout} (x : BitVec 64) (h : L.Arena x) : L.Heap x := by
  obtain ⟨span,member,inside⟩ := h
  exact ⟨span,List.mem_append_right _ member,inside⟩

/-- The table (hence its sequence word) is apart from the arena. -/
theorem arena_not_seq {L : Statements.C1.Layout}
    (objectsApart : spansApart ([(L.table,AllowedipsMutationLayout.tableSize)] ++
      L.peers.map fun (_,a) => (a,Layouts.peerSize)) L.arena = true)
    (x : BitVec 64) (h : L.Arena x) :
    ¬InRange (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 x := by
  obtain ⟨span,member,inside⟩ := h
  intro seqAt
  have tableAt : Pair.Span.contains (L.table,AllowedipsMutationLayout.tableSize) x :=
    span_within _ _ _ _ (by omega) (by show L.table + 16 + 8 ≤ L.table + 24; omega) x seqAt
  exact spansApart_sound objectsApart (List.mem_append_left _ (List.mem_singleton.mpr rfl)) member
    tableAt inside

/-- The allocator's state survives writes to the stack window, the sequence
word and the coverage buffer: the contract's `frame` clause. -/
theorem Trunk.idleFrame {fetch : Int64 → Option Decoded} {L : Statements.C1.Layout} {A : Allocator}
    (premises : Premises fetch L A) {c : Context} {s : MachineState} {w : World} {v4 : Bool}
    {key cidr pid : Nat} {ra : UInt64} {names : Allowedips.Names} {stream : List HiddenRecord}
    {d : Device} {seq : BitVec 64} {a : MachineData}
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a) {m : Mem 64}
    (frame : EqualOutside (fun x =>
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth + 8) x ∨
      InRange (s.data.regs.rdi.toBitVec+16) 8 x ∨ c.writes x) s.data.dmem m) :
    A.Idle m (names.trie.nodes.map (·.2)) stream := by
  apply premises.allocator.frame s.data.dmem m _ _ trunk.idle
  intro x arena _
  apply frame x
  intro written
  rcases written with h | h | h
  · exact trunk.sep.heapStack x (arena_heap x arena) h
  · rw [seq_address _ L.table trunk.tableReg] at h
    exact arena_not_seq trunk.objectsApart x arena h
  · exact trunk.sep.heapWrites x (arena_heap x arena) h

theorem eax_inval (r : Reg64s) (h : r.rax = 0xffffffea) :
    r.get (.low .rax .W32) = BitVec.ofInt 32 (-EINVAL) := by
  simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, h, EINVAL]
  decide

/-- `add` on the over-long prefix, entry to return, against `AddPost`. -/
theorem tooLong_body (fetch : Int64 → Option Decoded) (L : Statements.C1.Layout) (A : Allocator)
    (premises : Premises fetch L A) {c : Context} {s : MachineState} {w w' : World} {v4 : Bool}
    {key cidr pid : Nat} {ra : UInt64} {names : Allowedips.Names} {stream : List HiddenRecord}
    {d : Device} {seq : BitVec 64} {a : MachineData}
    (trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a)
    (long : cidr > (if v4 then 32 else 128))
    (after : ∃ d', w'.wg.dev = some d' ∧ Allowedips.target d' = Allowedips.target (bump d))
    (recordsAfter : w'.ambient.hidden = some stream) (armedAfter : armed w' = true) :
    Eventually (instructionStep fetch) (AddPost L A c s w' v4 (-EINVAL) seq a) ⟨a,Add.entry⟩ := by
  have wide := window_wide A
  have entry : EntryBase names c (fun _ => False) (bumped w d) a (if v4 then 32 else 128)
      (s.data.regs.rdx.toNat % 256) (site v4).toUInt64 (bump d) :=
    entry_base wide trunk.caller trunk.sep trunk.table trunk.peers trunk.inArena trunk.tableReg
      trunk.related trunk.shape trunk.atAdd trunk.mapped
  have byte : s.data.regs.rdx.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (add_inval_machine fetch premises.insertion premises.tracePc premises.cmp1 entry
      (by rw [trunk.cidr]; exact long) byte)
  rintro t ⟨returned,rax,_,relatedT,shapeT,frameT⟩
  have tight := window_tight trunk.atAdd (insertWindow + A.depth) wide
  have fs := frameSize_range v4
  have wideOf (x : BitVec 64) (h : Window a x) :
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth + 8) x :=
    range_mono _ _ _ (by omega) x (tight x h)
  refine ⟨returned,eax_inval _ rax,?_,?_,?_⟩
  · rw [← seq_address _ L.table trunk.tableReg,
      ← frameT.loadInt _ 8 (fun i hi h => by
        have inHeap := seq_heap (L := L) _ trunk.tableReg _ ⟨i,hi,rfl⟩
        rcases h with h | h | h
        · exact trunk.sep.heapStack _ inHeap (wideOf _ h)
        · exact trunk.sep.heapWrites _ inHeap h
        · exact h)]
    exact trunk.atAdd.seqWord
  · obtain ⟨d',device',same⟩ := after
    refine ⟨names,stream,trunk.table,trunk.peers,?_,armedAfter,recordsAfter,trunk.sites,
      trunk.objectsApart,trunk.inArena,?_⟩
    · apply assertAt_of_related device'
      · show Allowedips.reconstruct names Root.nodeOffsets t.data.dmem = .ok (Allowedips.target d')
        rw [same]
        exact relatedT
      · rw [same]
        exact shapeT
    · apply trunk.idleFrame premises
      intro x hx
      refine (trunk.atAdd.frameAt x (fun h => hx ?_)).trans (frameT x (fun h => hx ?_))
      · rcases h with h | h | h
        · exact .inl (below_sub _ _ _ _ _ (by omega) (by omega) x h)
        · exact .inr (.inl h)
        · exact .inr (.inr h)
      · rcases h with h | h | h
        · exact .inl (wideOf x h)
        · exact .inr (.inr h)
        · exact h.elim
  · intro x hx
    apply frameT x
    intro h
    rcases h with h | h | h
    · exact hx (.inl (tight x h))
    · exact hx (.inr (.inl h))
    · exact h

#print axioms tooLong_body
end C1Trunk
