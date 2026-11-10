import C1TrunkEnter
import C1Interfaces
/-! Result C1, package 2: the caller's executable conditions (`insertReady`,
`frameReady`) as propositions. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- `frameReady` for an insertion, clause by clause. -/
structure FrameFacts (L : Statements.C1.Layout) (c : Context) (s : MachineState) (ra : UInt64)
    (window : Nat) (query : Pair.Span) : Prop where
  entry : EntryFrame s ra
  mapped : Below s.data.dmem s.data.regs.rsp.toBitVec window
  coverage : c.At s.data.dmem
  capacity : c.Needed → 0 < c.coverage.capacity.toNat
  forward : s.data.system.bits[10] = false
  heapApart : spansApart L.heap
    (callerSpans s window query true ++ Trie.callServices c ++ Trie.callBuffers c) = true
  serviceStack : spansApart (Trie.callServices c) [(callerSpans s window query true).head!] = true
  bufferApart : spansApart (Trie.callBuffers c)
    (callerSpans s window query true ++ Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)]) = true
  preemptApart : spansApart ([(callerSpans s window query true).head!] ++ Trie.callMetadata c ++
    Trie.callHeaders c) [(preemptCountAddress.toNat,4)] = true
  callerApart : spansApart [((s.data.regs.rsp.toBitVec - .ofNat 64 window).toNat, window)]
    (callerSpans s window query true).tail! = true

theorem frameReady_facts {L : Statements.C1.Layout} {c : Context} {s : MachineState} {ra : UInt64}
    {window : Nat} {query : Pair.Span}
    (checked : frameReady L c s ra window query true false = .ok ()) :
    FrameFacts L c s ra window query := by
  unfold frameReady at checked
  obtain ⟨abi,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨stack,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨coverage,checked⟩ := require_bind_ok _ _ _ _ checked
  simp only [↓reduceIte, Bool.false_eq_true] at checked
  obtain ⟨capacity,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨forward,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨heapApart,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨serviceStack,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨bufferApart,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨preemptApart,checked⟩ := require_bind_ok _ _ _ _ checked
  have callerApart := require_ok checked
  simp only [Bool.and_eq_true, beq_iff_eq] at abi
  exact {
    entry := ⟨abi.1,abi.2⟩
    mapped := fun i hi => List.all_eq_true.mp stack i (List.mem_range.mpr hi)
    coverage := Trie.coverageCheck_sound coverage
    capacity := fun needed => by simpa only [needed, ↓reduceIte, decide_eq_true_eq] using capacity
    forward := eq_of_beq forward
    heapApart, serviceStack, bufferApart, preemptApart, callerApart }

/-- `insertReady`, clause by clause. -/
structure ReadyFacts (L : Statements.C1.Layout) (A : Allocator) (c : Context) (s : MachineState)
    (family key cidr pid : Nat) (ra : UInt64) : Prop where
  families : family = 4 ∨ family = 6
  pc : s.pc = if family = 4 then Insert4.entry else Insert6.entry
  table : s.data.regs.rdi.toNat = L.table
  peer : Trie.address L.peers (some pid) = .ok s.data.regs.rcx.toNat
  peerNonNull : s.data.regs.rcx.toNat ≠ 0
  cidr : s.data.regs.rdx.toNat % 256 = cidr
  key : Allowedips.NetworkKey s.data.dmem s.data.regs.rsi.toBitVec (if family = 4 then 32 else 128) key
  cache : readNat s cacheWord 8 = .ok L.cache
  frame : FrameFacts L c s ra (insertWindow + A.depth)
    (s.data.regs.rsi.toNat, (if family = 4 then 32 else 128)/8)

theorem insertReady_facts {L : Statements.C1.Layout} {A : Allocator} {c : Context} {s : MachineState}
    {family key cidr pid : Nat} {ra : UInt64}
    (checked : insertReady L A c s family key cidr pid ra = .ok ()) :
    ReadyFacts L A c s family key cidr pid ra := by
  unfold insertReady at checked
  obtain ⟨families,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨pc,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨table,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨peer,peerAt,checked⟩ := bind_ok checked
  obtain ⟨peerOk,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨cidrOk,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨keyOk,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨cache,cacheAt,checked⟩ := bind_ok checked
  obtain ⟨cacheOk,checked⟩ := require_bind_ok _ _ _ _ checked
  obtain ⟨-,checked⟩ := require_bind_ok _ _ _ _ checked
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at peerOk
  have cacheEq : cache = L.cache := eq_of_beq cacheOk
  have keyFact := Trie.networkKeyCheck_sound keyOk
  have frame := frameReady_facts checked
  simp only [beq_iff_eq] at keyFact frame
  exact {
    families := by simpa only [Bool.or_eq_true, beq_iff_eq] using families
    pc := by simpa only [beq_iff_eq] using eq_of_beq pc
    table := eq_of_beq table
    peer := peerOk.2 ▸ peerAt
    peerNonNull := peerOk.2 ▸ peerOk.1
    cidr := eq_of_beq cidrOk
    key := keyFact
    cache := cacheEq ▸ cacheAt
    frame := frame }

#print axioms frameReady_facts
#print axioms insertReady_facts

end C1Trunk
