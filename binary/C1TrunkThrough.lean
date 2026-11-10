import C1TrunkBase
import SystemInvariant
import MemoryInvariant
/-! Result C1, package 2: the wrapper around `add`. `Trunk` is everything
known at `add`'s entry (the caller's conditions, the invariant's
interpretation, the wrapper's frame); `through` reduces `InsertPost` for a
whole insertion to a statement about `add` from its entry to its return. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
open Binary.TrustBase Binary.CommonBitsCoverage Binary.Instrumentation
open Binary.Statements.C1 Binary.Statements.C1.Proof Leanux Leanux.WG
local instance : Labels := Image.linkedLabels

/-- The sequence word is mapped and holds some 64-bit value. -/
theorem seq_exists {names : Allowedips.Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d : Device}
    (related : Allowedips.Corresponds names o m d) :
    ∃ seq : BitVec 64, m.loadInt (.ofNat 64 (names.table+AllowedipsMutationLayout.seq)) 8 =
      some (seq.toNat : Int) := by
  unfold Allowedips.Corresponds Allowedips.reconstruct at related
  obtain ⟨_,_,h⟩ := bind_ok related
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨_,_,h⟩ := bind_ok h
  obtain ⟨v,hv,_⟩ := bind_ok h
  have read := word_loadInt _ _ _ _ _ hv
  have range := (loadInt_range _ _ _ _ read).2
  refine ⟨BitVec.ofNat 64 v,?_⟩
  rw [read, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have : ((v : Nat) : Int) < 256^8 := range
    omega)]

theorem get_rax_congr (r1 r2 : Reg64s) (h : r1.rax = r2.rax) :
    r1.get (.low .rax .W32) = r2.get (.low .rax .W32) := by
  simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, h]

/-- Everything known at `add`'s entry `a` inside an insertion entered at `s`. -/
structure Trunk (L : Statements.C1.Layout) (A : Allocator) (c : Context) (s : MachineState) (w : World)
    (v4 : Bool) (key cidr pid : Nat) (ra : UInt64) (names : Allowedips.Names)
    (stream : List HiddenRecord) (d : Device) (seq : BitVec 64) (a : MachineData) : Prop where
  tableReg : s.data.regs.rdi.toNat = L.table
  peer : Trie.address L.peers (some pid) = .ok s.data.regs.rcx.toNat
  peerNonNull : s.data.regs.rcx.toNat ≠ 0
  cidr : s.data.regs.rdx.toNat % 256 = cidr
  cache : readNat s cacheWord 8 = .ok L.cache
  entry : EntryFrame s ra
  capacity : c.Needed → 0 < c.coverage.capacity.toNat
  forward : s.data.system.bits[10] = false
  stackMapped : Below s.data.dmem s.data.regs.rsp.toBitVec (insertWindow + A.depth)
  sep : Separate L c s.data (insertWindow + A.depth) (if v4 then 4 else 16)
  table : names.table = L.table
  peers : names.trie.peers = L.peers
  related : Allowedips.Corresponds names Root.nodeOffsets s.data.dmem d
  shape : Allowedips.heap names (Allowedips.target d) s.data.dmem = .ok ()
  device : w.wg.dev = some d
  armed : armed w = true
  hidden : w.ambient.hidden = some stream
  sites : ∀ record ∈ stream, record.site ∈ allocSites.map (·.2)
  objectsApart : spansApart ([(L.table,AllowedipsMutationLayout.tableSize)] ++
    L.peers.map fun (_,a) => (a,Layouts.peerSize)) L.arena = true
  inArena : ∀ node ∈ names.trie.nodes, ∃ span ∈ L.arena, span.1 ≤ node.2 ∧ node.2+nodeSize ≤ span.1+span.2
  idle : A.Idle s.data.dmem (names.trie.nodes.map (·.2)) stream
  caller : Caller c s.data seq
  atAdd : AtAdd c s.data seq v4 key a
  mapped : ∀ x k, (s.data.dmem.loadInt x k).isSome = true → (a.dmem.loadInt x k).isSome = true
  forwardA : a.system.bits[10] = false
  relatedA : Allowedips.Corresponds names Root.nodeOffsets a.dmem (bump d)
  shapeA : Allowedips.heap names (Allowedips.target (bump d)) a.dmem = .ok ()

theorem window_wide (A : Allocator) : 200 ≤ insertWindow + A.depth := by
  unfold insertWindow
  omega

theorem seq_heap {L : Statements.C1.Layout} (x : UInt64) (held : x.toNat = L.table) (a : BitVec 64)
    (inside : InRange (x.toBitVec+16) 8 a) : L.Heap a := by
  rw [seq_address x L.table held] at inside
  exact ⟨(L.table+AllowedipsMutationLayout.seq,8),
    by simp [Layout.heap, Layout.fixed, tableFields],inside⟩

/-- What `add` must do, from its entry to its return, for `InsertPost`. -/
def AddPost (L : Statements.C1.Layout) (A : Allocator) (c : Context) (s : MachineState) (w' : World)
    (v4 : Bool) (answer : Int) (seq : BitVec 64) (a : MachineData) (t : MachineState) : Prop :=
  Returned ⟨a,Add.entry⟩ t (site v4).toUInt64 ∧
  t.data.regs.get (.low .rax .W32) = BitVec.ofInt 32 answer ∧
  t.data.dmem.loadInt (.ofNat 64 (L.table+AllowedipsMutationLayout.seq)) 8 = some ((1+seq).toNat : Int) ∧
  Inv L A w' t.data.dmem ∧
  EqualOutside (fun x =>
    InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth))
      (insertWindow + A.depth - frameSize v4 + 8) x ∨ c.writes x ∨ L.Heap x) a.dmem t.data.dmem

/-- The wrapper around `add`, for one address family. -/
theorem through_core (fetch : Int64 → Option Decoded) (L : Statements.C1.Layout) (A : Allocator)
    (premises : Premises fetch L A) (c : Context) (s : MachineState) (w w' : World)
    (v4 : Bool) (key cidr pid : Nat) (ra : UInt64) (answer : Int)
    (inv : Inv L A w s.data.dmem)
    (pc : s.pc = if v4 then Insert4.entry else Insert6.entry)
    (tableReg : s.data.regs.rdi.toNat = L.table)
    (peer : Trie.address L.peers (some pid) = .ok s.data.regs.rcx.toNat)
    (peerNonNull : s.data.regs.rcx.toNat ≠ 0)
    (cidrReg : s.data.regs.rdx.toNat % 256 = cidr)
    (keyAt : Binary.Allowedips.NetworkKey s.data.dmem s.data.regs.rsi.toBitVec (if v4 then 32 else 128) key)
    (cache : readNat s cacheWord 8 = .ok L.cache)
    (frame : FrameFacts L c s ra (insertWindow + A.depth) (s.data.regs.rsi.toNat, if v4 then 4 else 16))
    (body : ∀ names stream d seq a, Trunk L A c s w v4 key cidr pid ra names stream d seq a →
      Eventually (instructionStep fetch) (AddPost L A c s w' v4 answer seq a) ⟨a,Add.entry⟩) :
    Eventually (instructionStep fetch) (InsertPost L A c s w' ra answer) s := by
  have wide := window_wide A
  have sep := frame.separate
  obtain ⟨names,stream,tableEq,peersEq,asserted,armedW,hiddenW,sitesW,objectsApart,inArena,idle⟩ := inv
  obtain ⟨d,device,related,shape⟩ := assertAt_ok asserted
  obtain ⟨seq,seqWord⟩ := seq_exists related
  have address := seq_address s.data.regs.rdi names.table (tableReg.trans tableEq.symm)
  rw [← address] at seqWord
  have wideStack (x : BitVec 64) (h : InRange (s.data.regs.rsp.toBitVec - .ofNat 64 200) 208 x) :
      InRange (s.data.regs.rsp.toBitVec - .ofNat 64 (insertWindow + A.depth)) (insertWindow + A.depth + 8) x :=
    below_sub _ 200 208 (insertWindow + A.depth) (insertWindow + A.depth + 8) wide (by have := wide; omega) x h
  have caller : Caller c s.data seq := {
    aligned := frame.entry.1
    room := by have := sep.room; omega
    below := fun i hi => frame.mapped i (by omega)
    coverage := frame.coverage
    coverageStack := fun x read h => sep.bytesStack x read (wideStack x h)
    metadataSeparate := sep.writesMetadata
    preemptSeparate := sep.writesPreempt
    seqWord := seqWord
    seqStack := fun x h hs => sep.heapStack x (seq_heap _ tableReg x h) (wideStack x hs)
    seqCoverage := fun x h => sep.heapBytes x (seq_heap _ tableReg x h) }
  have entered := enter fetch premises.insertion premises.tracePc caller v4 key keyAt
    (fun x h hs => sep.stackQuery x (below_sub _ 200 200 _ _ wide (by omega) x hs) h)
    (fun x h hw => sep.writesQuery x hw h)
    (fun x h hq => sep.heapQuery x (seq_heap _ tableReg x hq) h)
  have run := SystemInvariant.eventually_mode fetch (MemoryInvariant.eventually_mapped fetch entered)
  have start : s = ⟨s.data,if v4 then Insert4.entry else Insert6.entry⟩ := Placement.at_pc s _ pc
  rw [start]
  apply eventually_trans (instructionStep fetch) _ _ _ run
  rintro a ⟨⟨⟨pcA,atAdd⟩,mapped⟩,_,forwardA⟩
  obtain ⟨relatedA,shapeA⟩ := related_at_add wide sep tableEq peersEq inArena tableReg seqWord related shape atAdd
  have trunk : Trunk L A c s w v4 key cidr pid ra names stream d seq a.data := {
    tableReg, peer, peerNonNull, cidr := cidrReg, cache, entry := frame.entry, capacity := frame.capacity
    forward := frame.forward, stackMapped := frame.mapped, sep, table := tableEq, peers := peersEq
    related, shape, device, armed := armedW, hidden := hiddenW, sites := sitesW, objectsApart, inArena
    idle, caller, atAdd, mapped
    forwardA := forwardA.trans frame.forward
    relatedA, shapeA }
  rw [Placement.at_pc a _ pcA]
  apply eventually_trans (instructionStep fetch) _ _ _ (body names stream d seq a.data trunk)
  rintro t ⟨returned,eax,seqT,invT,frameT⟩
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (leave fetch premises.insertion (insertWindow + A.depth) wide sep.room sep.top atAdd frame.entry.2
      (fun x h hs => sep.bytesStack x (writes_bytes h) (wideStack x hs)) caller.seqStack
      (fun x h hs => sep.heapStack x h (wideStack x hs)) returned frameT)
  rintro f ⟨pcF,spF,bxF,bpF,r12F,r13F,r14F,r15F,raxF,memF⟩
  have fs := frameSize_range v4
  refine ⟨⟨pcF,spF,bxF,bpF,r12F,r13F,r14F,r15F⟩,?_,?_,?_,?_⟩
  · rw [get_rax_congr _ _ raxF]
    exact eax
  · refine ⟨seq.toNat,readNat_of_load ?_,readNat_of_load ?_⟩
    · rw [← tableEq, ← address]
      exact seqWord
    · rw [memF, seqT]
      congr 2
      rw [BitVec.toNat_add]
      show (1 + seq.toNat) % 2^64 = (seq.toNat + 1) % 2^64
      rw [Nat.add_comm]
  · rw [memF]
    exact invT
  · rw [memF]
    intro x hx
    refine (atAdd.frameAt x (fun h => hx ?_)).trans (frameT x (fun h => hx ?_))
    · rcases h with h | h | h
      · exact .inl (below_sub _ _ _ _ _ (by omega) (by omega) x h)
      · exact .inr (.inr (seq_heap _ tableReg x h))
      · exact .inr (.inl h)
    · rcases h with h | h | h
      · exact .inl (below_sub _ _ _ _ _ (Nat.le_refl _) (by omega) x h)
      · exact .inr (.inl h)
      · exact .inr (.inr h)

#print axioms through_core
end C1Trunk
