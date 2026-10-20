import AllowedipsRootCopyDecode
import AllowedipsParentDecode

namespace Binary.Pair.Allowedips.Root
open Leanux Leanux.WG

/-- These offsets are generated from the pinned image, not an alternative
record model. Reconstruction validation already checks each component. -/
def nodeOffsets : AllowedipsProbe.Offsets :=
  ⟨AllowedipsLayout.nodeSize,AllowedipsLayout.peer,AllowedipsLayout.bit,
    AllowedipsLayout.cidr,AllowedipsLayout.bit_at_a,AllowedipsLayout.bit_at_b,
    AllowedipsLayout.bitlen,AllowedipsLayout.bits,Layouts.peer_refcount⟩

private theorem copy_frame_widen {base : Nat} {before after : DataMem}
    (frame : EqualOutside (InRange (.ofNat 64 (base+32)) 4) before after) :
    EqualOutside (InRange (.ofNat 64 (base+32)) 16) before after := by
  intro a outside
  apply frame a
  rintro ⟨i,bound,eq⟩
  exact outside ⟨i,by omega,eq⟩

/-- The initialized record is reconstructed after the actual packed-header
store and tested copy phase. The owner/null-child facts are supplied by the
preceding allocation and attachment phases, not by a post-state assertion. -/
theorem header_copy_core {names : Names} {s : MachineData} {before after : DataMem}
    {cidr key pid : Nat}
    (family : s.regs.rbp.toNat=32 ∨ s.regs.rbp.toNat=128)
    (prefixBound : cidr≤s.regs.rbp.toNat) (extent : s.regs.rbx.toNat+72≤2^64)
    (owner : word before "node.peer" s.regs.rbx.toNat 8=.ok s.regs.r14.toNat)
    (peer : Trie.pointer names.trie.peers "node.peer" s.regs.r14.toNat=.ok (some pid))
    (left : word before "node.child[0]" (s.regs.rbx.toNat+8) 8=.ok 0)
    (right : word before "node.child[1]" (s.regs.rbx.toNat+16) 8=.ok 0)
    (query : if s.regs.rbp.toNat=32 then
      word (before.storeInt (.ofNat 64 (s.regs.rbx.toNat+24)) 4 (headerWord s.regs.rbp.toNat cidr))
        "query" s.regs.r13.toNat 4=.ok key else
      ∃ hi lo,
        word (before.storeInt (.ofNat 64 (s.regs.rbx.toNat+24)) 4 (headerWord s.regs.rbp.toNat cidr))
          "query.high" s.regs.r13.toNat 8=.ok hi ∧
        word (before.storeInt (.ofNat 64 (s.regs.rbx.toNat+24)) 4 (headerWord s.regs.rbp.toNat cidr))
          "query.low" (s.regs.r13.toNat+8) 8=.ok lo ∧ key=hi*2^64+lo)
    (queryApart : ∀ a, InRange s.regs.r13.toBitVec (if s.regs.rbp.toNat=32 then 4 else 8) a →
      ¬InRange (.ofNat 64 (s.regs.rbx.toNat+32)) 16 a)
    (checked : copy s (before.storeInt (.ofNat 64 (s.regs.rbx.toNat+24)) 4
        (headerWord s.regs.rbp.toNat cidr))=.ok after) :
    Trie.decodeNode names.trie nodeOffsets after s.regs.rbx.toNat=
      .ok (Trie.targetNode (Leanux.WG.newNode key cidr s.regs.rbp.toNat (some pid))) := by
  let h := before.storeInt (.ofNat 64 (s.regs.rbx.toNat+24)) 4 (headerWord s.regs.rbp.toNat cidr)
  have copied : (if s.regs.rbp.toNat=32 then
      word after "node.key32" (s.regs.rbx.toNat+32) 4=.ok key else
      ∃ hi lo,word after "node.key128.high" (s.regs.rbx.toNat+32) 8=.ok hi ∧
        word after "node.key128.low" (s.regs.rbx.toNat+40) 8=.ok lo ∧ key=hi*2^64+lo) ∧
      EqualOutside (InRange (.ofNat 64 (s.regs.rbx.toNat+32)) 16) h after := by
    rcases family with four|six
    · rw [ite_eq_left four] at query queryApart ⊢
      have run := copy4_key four (by omega) query (by
        intro a read written
        rcases read with ⟨i,small,eq⟩
        rcases written with ⟨j,short,same⟩
        exact queryApart a ⟨i,by omega,eq⟩ ⟨j,by omega,same⟩) checked
      exact ⟨run.1,copy_frame_widen run.2⟩
    · have not4 : s.regs.rbp.toNat≠32 := by omega
      rw [ite_eq_right not4] at query queryApart ⊢
      obtain ⟨hi,lo,high,low,keyEq⟩ := query
      have run := copy128_key six (by omega) high low (by
        intro a read written
        apply queryApart a read
        rcases written with ⟨i,small,eq⟩
        refine ⟨8+i,by omega,?_⟩
        rw [←BitVec.ofNat_add]
        have sum : s.regs.rbx.toNat+32+(8+i)=s.regs.rbx.toNat+40+i := by omega
        rw [sum]
        simpa only [←BitVec.ofNat_add] using eq) checked
      exact ⟨⟨hi,lo,run.1,run.2.1,keyEq⟩,run.2.2⟩
  have keep (offset size : Nat) (within : offset+size≤32) (path : String) :
      word after path (s.regs.rbx.toNat+offset) size=word h path (s.regs.rbx.toNat+offset) size := by
    apply (Trie.word_frame copied.2 path _ _ _).symm
    simpa only [BitVec.ofNat_add] using InRange.offset_disjoint (.ofNat 64 s.regs.rbx.toNat)
      offset size 32 16 (by omega) (by decide) (.inl within)
  have old (offset size : Nat) (within : offset+size≤24) (path : String) :
      word after path (s.regs.rbx.toNat+offset) size=word before path (s.regs.rbx.toNat+offset) size := by
    rw [keep offset size (by omega) path]
    exact word_store_frame before path s.regs.rbx.toNat offset size 24 4 _ (by omega) (by decide) (.inl within)
  have header (byte : Fin 4) (path : String) :
      word after path (s.regs.rbx.toNat+24+byte.val) 1=.ok (headerByte s.regs.rbp.toNat cidr byte) := by
    rw [Nat.add_assoc,keep (24+byte.val) 1 (by have := byte.isLt; omega) path]
    simpa only [Nat.add_assoc] using header_field before s.regs.rbx.toNat s.regs.rbp.toNat cidr path
      family prefixBound (by omega) byte
  apply Trie.DecodedFields.decode
  refine ⟨⟨s.regs.r14.toNat,?_,peer⟩,?_,?_,?_,family,prefixBound,?_,?_,?_⟩
  · change word after "node.peer" (s.regs.rbx.toNat+0) 8=_
    rw [old 0 8 (by decide)]
    exact owner
  · refine ⟨none,none,0,0,rfl,?_,rfl,?_,rfl⟩
    · change word after "node.child[0]" (s.regs.rbx.toNat+8) 8=_
      rw [old 8 8 (by decide)]
      exact left
    · change word after "node.child[1]" (s.regs.rbx.toNat+8+8) 8=_
      rw [Nat.add_assoc]
      rw [old 16 8 (by decide)]
      exact right
  · exact header 0 "node.cidr"
  · simpa [headerByte,Trie.targetNode,Leanux.WG.newNode,nodeOffsets,
      AllowedipsLayout.bitlen,Nat.add_assoc] using header ⟨3,by decide⟩ "node.width"
  · simpa [headerByte,Trie.targetNode,Leanux.WG.newNode,nodeOffsets,
      AllowedipsLayout.bit_at_a,Nat.add_assoc] using header 1 "node.byte-selector"
  · simpa [headerByte,Trie.targetNode,Leanux.WG.newNode,nodeOffsets,
      AllowedipsLayout.bit_at_b,Nat.add_assoc] using header 2 "node.bit-selector"
  · simpa only [Trie.targetNode,Leanux.WG.newNode,nodeOffsets,AllowedipsLayout.bits,Nat.add_assoc] using copied.1

#print axioms header_copy_core
end Binary.Pair.Allowedips.Root
