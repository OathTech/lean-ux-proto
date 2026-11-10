import C1BelowUndoBytes
import AllowedipsNodePending
import AllowedipsRingBudget
import AllowedipsPeerListEdges
import AllowedipsExactLists

/-! Result C1, work package 3, rollback: the list words the first
initialization leaves, read off its executable summary. `list_add_tail` put
the fresh node between the owner's sentinel and its old last link; the
rollback's `list_del` needs those two neighbours, and the restoration needs
that, at the cut, the old last link pointed forward to the sentinel. -/
namespace Binary.Statements.C1.Proof.Undo
open Leanux Leanux.WG Binary.Pair Binary.Pair.Allowedips Binary.TrustBase
open Binary.Statements.C1 Binary.Pair.Allowedips.Root

/-- A link slot lies, with its two words, inside one allocation of the interpretation. -/
theorem slot_allocation {names : Allowedips.Names} {link : Nat} (slot : LinkSlot names link) :
    ∃ span ∈ allocations names nodeOffsets, span.1 ≤ link ∧ link+16 ≤ span.1+span.2 := by
  cases slot with
  | node named => exact ⟨_,node_allocation named,Nat.le_add_right _ _,Nat.le_refl _⟩
  | peer named => exact ⟨_,peer_allocation named,Nat.le_add_right _ _,by
      show _+1096+16 ≤ _+1520
      omega⟩

/-- What the first initialization leaves in the owner's ring. `head` is the
owner's sentinel, `last` its old last link. -/
structure Ringed (names : Allowedips.Names) (e : MachineData) (pid base : Nat) (m1 : DataMem)
    (last : Nat) : Prop where
  owner : (pid,e.regs.r14.toNat) ∈ names.trie.peers
  slot : LinkSlot names last
  tail : e.dmem.loadInt (.ofNat 64 (e.regs.r14.toNat+1096+8)) 8 = some (last : Int)
  closed : e.dmem.loadInt (.ofNat 64 last) 8 = some ((e.regs.r14.toNat+1096 : Nat) : Int)
  next : m1.loadInt (.ofNat 64 (base+56)) 8 = some ((e.regs.r14.toNat+1096 : Nat) : Int)
  prev : m1.loadInt (.ofNat 64 (base+56+8)) 8 = some (last : Int)
  headBack : m1.loadInt (.ofNat 64 (e.regs.r14.toNat+1096+8)) 8 = some ((base+56 : Nat) : Int)
  lastNext : m1.loadInt (.ofNat 64 last) 8 = some ((base+56 : Nat) : Int)
  frame : EqualOutside (fun x => InRange (.ofNat 64 base) 72 x ∨ NodeInit.StackWrites e.regs.rsp.toNat x ∨
    InRange (.ofNat 64 (e.regs.r14.toNat+1096+8)) 8 x ∨ InRange (.ofNat 64 last) 8 x) e.dmem m1
  /-- The fresh node's 72 bytes end below 2^64 and miss every old allocation. -/
  extent : base+72 < 2^64
  fresh : ∀ span ∈ allocations names nodeOffsets, base+72 ≤ span.1 ∨ span.1+span.2 ≤ base
  bounded : ∀ span ∈ allocations names nodeOffsets, span.1+span.2 ≤ 2^64

theorem ringed {names : Allowedips.Names} {world : World} {e : MachineState} {key cidr pid base : Nat}
    {m1 : DataMem}
    (checked : NodeInit.boundary names nodeOffsets world e key cidr pid = .ok base)
    (summary : NodeInit.effect e.data = .ok (m1,base)) :
    ∃ last, Ringed names e.data pid base m1 last := by
  have fields := NodeInit.boundary_fields checked
  obtain ⟨d,_,related,_⟩ := assertAt_ok fields.asserted
  obtain ⟨owner,peerNamed,hasPeer⟩ := peer_of_address fields.owner related
  obtain ⟨attached,initialized,attachment,headerCheck,copyCheck⟩ := NodeInit.effect_parts fields.original summary
  obtain ⟨last,tailRead,attachedEq⟩ := NodeInit.attach_as_ring attachment
  obtain ⟨_,_,extent,freshAll,_⟩ := allocated_facts fields.allocated
  have extent : base+72 < 2^64 := extent
  have g := Allowedips.geometry related
  have fresh : ∀ span ∈ allocations names nodeOffsets, base+72 ≤ span.1 ∨ span.1+span.2 ≤ base := by
    intro span member
    have apart := freshAll span member
    change disjointRanges base 72 span.1 span.2 = true at apart
    simpa only [disjointRanges,Bool.or_eq_true,decide_eq_true_eq] using apart
  have headSlot : LinkSlot names (e.data.regs.r14.toNat+1096) := .peer peerNamed
  obtain ⟨hspan,hmem,hlow,hhigh⟩ := slot_allocation headSlot
  have hb := g.bounded hspan hmem
  have hf := fresh hspan hmem
  -- the owner's list at the cut
  have ownerMember : (pid,owner.refcount,owner.allowedipsList) ∈ (Allowedips.target d).peers :=
    List.mem_map.mpr ⟨(pid,owner),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr hasPeer,rfl⟩
  have decoded := Reconstructed.peer_at related peerNamed ownerMember
  have tailLoad := Trie.readNat_loadInt tailRead
  have tailLoad : e.data.dmem.loadInt (.ofNat 64 (e.data.regs.r14.toNat+1096+8)) 8 = some (last : Int) := tailLoad
  have back : word e.data.dmem "peer.list.prev" (e.data.regs.r14.toNat+1096+8) 8 = .ok last :=
    Trie.word_of_loadInt _ (by omega) tailLoad
  have lastSlot := Ring.decoded_tail_slot headSlot decoded back
  obtain ⟨lspan,lmem,llow,lhigh⟩ := slot_allocation lastSlot
  have lb := g.bounded lspan lmem
  have lf := fresh lspan lmem
  obtain ⟨firstWord,firstRead,run⟩ := bind_ok decoded
  obtain ⟨nodes,_,linkEq,shape,_⟩ := Ring.peerList_shape run
  have closed := word_loadInt _ _ _ _ _
    (shape.last_forward (Binary.Pair.word_path (linkEq ▸ firstRead) _) back)
  -- the attached memory
  have cross : ∀ a, InRange (.ofNat 64 last) 8 a → ¬InRange (.ofNat 64 (e.data.regs.r14.toNat+1096+8)) 8 a :=
    lastSlot.forward_back_apart headSlot g rfl
  have initFrame := NodeInit.header_copy_frame (by omega : base<2^64) headerCheck copyCheck
  have offInit (address : Nat) (stack : ∀ a, InRange (.ofNat 64 address) 8 a →
        ¬NodeInit.StackWrites e.data.regs.rsp.toNat a)
      (numeric : address+8 ≤ 2^64 ∧ (address+8 ≤ base ∨ base+56 ≤ address)) (value : Int)
      (read : attached.loadInt (.ofNat 64 address) 8 = some value) :
      m1.loadInt (.ofNat 64 address) 8 = some value := by
    rw [←initFrame.loadInt (.ofNat 64 address) 8 (fun i bound written => by
      rcases written with record | stackWrite
      · exact range_apart numeric.1 (by omega : base+56 ≤ 2^64) (by omega) _ ⟨i,bound,rfl⟩ record
      · exact stack _ ⟨i,bound,rfl⟩ stackWrite)]
    exact read
  have nodeStack (offset : Nat) (within : offset+8 ≤ 72) :
      ∀ a, InRange (.ofNat 64 (base+offset)) 8 a → ¬NodeInit.StackWrites e.data.regs.rsp.toNat a :=
    fields.stack_slice_apart (span := (base,72)) (by simp) offset 8 within
  have oldStack {span : Pair.Span} (member : span ∈ allocations names nodeOffsets) (address : Nat)
      (low : span.1 ≤ address) (high : address+8 ≤ span.1+span.2) :
      ∀ a, InRange (.ofNat 64 address) 8 a → ¬NodeInit.StackWrites e.data.regs.rsp.toNat a := by
    have at_ := fields.stack_slice_apart (span := span)
      (List.mem_append_right _ member) (address-span.1) 8 (by omega)
    rwa [show span.1+(address-span.1) = address by omega] at at_
  have skip (m : DataMem) (address destination value : Nat) (first : address+8 ≤ 2^64)
      (second : destination+8 ≤ 2^64) (apart : address+8 ≤ destination ∨ destination+8 ≤ address) :
      (write64 m destination value).loadInt (.ofNat 64 address) 8 = m.loadInt (.ofNat 64 address) 8 :=
    ((write64_frame m destination value).loadInt (.ofNat 64 address) 8
      (fun i bound => range_apart first second apart _ ⟨i,bound,rfl⟩)).symm
  have skipCross (m : DataMem) (value : Nat) :
      (write64 m last value).loadInt (.ofNat 64 (e.data.regs.r14.toNat+1096+8)) 8 =
        m.loadInt (.ofNat 64 (e.data.regs.r14.toNat+1096+8)) 8 :=
    ((write64_frame m last value).loadInt _ 8
      (fun i bound written => cross _ written ⟨i,bound,rfl⟩)).symm
  have hit (m : DataMem) (address value : Nat) (small : value < 2^64) :
      (write64 m address value).loadInt (.ofNat 64 address) 8 = some (value : Int) :=
    load_store_nat m _ small
  subst attachedEq
  refine ⟨last,peerNamed,lastSlot,tailLoad,closed,?_,?_,?_,?_,?_,extent,fresh,g.bounded⟩
  · apply offInit _ (nodeStack 56 (by decide)) (by omega)
    simp only [Ring.appendMemory]
    rw [skip _ _ _ _ (by omega) (by omega) (by omega),skip _ _ _ _ (by omega) (by omega) (by omega)]
    exact hit _ _ _ (by omega)
  · apply offInit _ (nodeStack 64 (by decide)) (by omega)
    simp only [Ring.appendMemory]
    rw [skip _ _ _ _ (by omega) (by omega) (by omega)]
    exact hit _ _ _ (by omega)
  · apply offInit _ (oldStack hmem _ (by omega) (by omega)) (by omega)
    simp only [Ring.appendMemory]
    rw [skipCross,skip _ _ _ _ (by omega) (by omega) (by omega),skip _ _ _ _ (by omega) (by omega) (by omega)]
    exact hit _ _ _ (by omega)
  · apply offInit _ (oldStack lmem _ (by omega) (by omega)) (by omega)
    simp only [Ring.appendMemory]
    exact hit _ _ _ (by omega)
  · intro x outside
    have step (m : DataMem) (address value : Nat) (inside : ∀ y, InRange (.ofNat 64 address) 8 y →
        InRange (.ofNat 64 base) 72 y ∨ NodeInit.StackWrites e.data.regs.rsp.toNat y ∨
        InRange (.ofNat 64 (e.data.regs.r14.toNat+1096+8)) 8 y ∨ InRange (.ofNat 64 last) 8 y) :
        m.get? x = (write64 m address value).get? x :=
      write64_frame m address value x (fun h => outside (inside x h))
    have toAttached : e.data.dmem.get? x = (Ring.appendMemory (write64 e.data.dmem base e.data.regs.r14.toNat)
        (e.data.regs.r14.toNat+1096) last (base+56)).get? x := by
      simp only [Ring.appendMemory]
      exact (step e.data.dmem base e.data.regs.r14.toNat
          (fun y h => .inl (range_slice (offset := 0) (by decide) h))).trans
        ((step _ (e.data.regs.r14.toNat+1096+8) (base+56) (fun y h => .inr (.inr (.inl h)))).trans
        ((step _ (base+56) (e.data.regs.r14.toNat+1096) (fun y h => .inl (range_slice (by decide) h))).trans
        ((step _ (base+56+8) last (fun y h => .inl (range_slice (offset := 64) (by decide) h))).trans
        (step _ last (base+56) (fun y h => .inr (.inr (.inr h)))))))
    exact toAttached.trans (initFrame x (fun written => outside (written.elim
      (fun record => .inl (by
        obtain ⟨i,bound,at_⟩ := record
        exact ⟨i,by omega,at_⟩))
      (fun stackWrite => .inr (.inl stackWrite)))))

#print axioms ringed
end Binary.Statements.C1.Proof.Undo
