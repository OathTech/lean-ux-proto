import AllowedipsRootPublishDecode
import AllowedipsRootLists

namespace Binary.Pair.Allowedips.Root

/-- The non-list initialization stores: fresh record fields and the slot
actually read by publication. This is a write footprint, not a relation clause. -/
def InitWrites (base slot : Nat) (a : BitVec 64) : Prop :=
  InRange (.ofNat 64 base) 56 a ∨ InRange (.ofNat 64 slot) 8 a

private theorem record_subrange {base offset size a}
    (within : offset+size≤56) (inside : InRange (.ofNat 64 (base+offset)) size a) :
    InRange (.ofNat 64 base) 56 a := by
  obtain ⟨i,small,equal⟩ := inside
  refine ⟨offset+i,by omega,?_⟩
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using equal

theorem store_record_frame {before after base offset size value}
    (within : offset+size≤56)
    (checked : store before (base+offset) size value=.ok after) :
    EqualOutside (InRange (.ofNat 64 base) 56) before after := by
  rw [(store_facts checked).2]
  intro a outside
  exact storeInt_frame _ _ _ _ a (fun inside => outside (record_subrange within inside))

/-- Copy's footprint follows the ordered executed stores even if a source
address aliases a destination. No query-separation premise is needed here. -/
theorem copy_frame {s before after} (checked : copy s before=.ok after) :
    EqualOutside (InRange (.ofNat 64 s.regs.rbx.toNat) 56) before after := by
  unfold copy at checked
  split at checked
  all_goals
    obtain ⟨first,_,checked⟩ := bind_ok checked
    obtain ⟨middle,firstStore,checked⟩ := bind_ok checked
    obtain ⟨second,_,checked⟩ := bind_ok checked
    obtain ⟨last,lastStore,checked⟩ := bind_ok checked
    cases Except.ok.inj checked
    exact fun a outside => (store_record_frame (by decide) firstStore a outside).trans
      (store_record_frame (by decide) lastStore a outside)

/-- Preserve the actual saved-slot read: publication's destination is derived
from this execution, and its equality to a table slot is proved by callers. -/
theorem publish_frame {s before after} (checked : publish s before=.ok after) :
    ∃ slot, readNat ⟨{s with dmem:=before},0⟩ (s.regs.rsp.toNat+8) 8=.ok slot ∧
      EqualOutside (InitWrites s.regs.rbx.toNat slot) before after := by
  unfold publish at checked
  obtain ⟨slot,read,checked⟩ := bind_ok checked
  obtain ⟨middle,parentStore,rootStore⟩ := bind_ok checked
  refine ⟨slot,read,?_⟩
  have parentFrame := store_record_frame (by decide) parentStore
  rw [(store_facts rootStore).2]
  intro a outside
  exact (parentFrame a (fun inside => outside (.inl inside))).trans
    (storeInt_frame _ _ _ _ a (fun inside => outside (.inr inside)))

theorem initialization_frame {s attached cidr withHeader copied after}
    (header : store attached (s.regs.rbx.toNat+24) 4 (headerWord s.regs.rbp.toNat cidr)=.ok withHeader)
    (copy : Root.copy s withHeader=.ok copied)
    (publish : Root.publish s copied=.ok after) :
    ∃ slot, readNat ⟨{s with dmem:=copied},0⟩ (s.regs.rsp.toNat+8) 8=.ok slot ∧
      EqualOutside (InitWrites s.regs.rbx.toNat slot) attached after := by
  obtain ⟨slot,read,last⟩ := publish_frame publish
  refine ⟨slot,read,?_⟩
  have first := store_record_frame (by decide) header
  have middle := copy_frame copy
  intro a outside
  have outsideRecord : ¬InRange (.ofNat 64 s.regs.rbx.toNat) 56 a :=
    fun inside => outside (.inl inside)
  exact (first a outsideRecord).trans ((middle a outsideRecord).trans (last a outside))

/-- Any memory update that preserves the list words preserves the executable
list traversal, including its failures. -/
theorem list_read_frame {names before after writes head fuel}
    (frame : EqualOutside writes before after)
    (apart : ∀ a, ListWrites names a → ¬writes a)
    (headSlot : LinkSlot names head) :
    (do
      let first ← word before "peer.list.head" head 8
      peerList names before head fuel first head [])=
    (do
      let first ← word after "peer.list.head" head 8
      peerList names after head fuel first head []) := by
  have words (link) (slot : LinkSlot names link) (path offset) (which : offset=0 ∨ offset=8) :
      word before path (link+offset) 8=word after path (link+offset) 8 :=
    Trie.word_frame frame path _ _ (fun a inside => apart a ⟨link,slot,offset,which,inside⟩)
  have first := words head headSlot "peer.list.head" 0 (.inl rfl)
  simp only [Nat.add_zero] at first
  rw [first]
  cases word after "peer.list.head" head 8 with
  | error e => rfl
  | ok value =>
    exact peerList_congr names before after head (words head headSlot)
      (fun id base named => words (base+56) (.node named)) fuel value head []

#print axioms initialization_frame
#print axioms list_read_frame
end Binary.Pair.Allowedips.Root
