import AllowedipsWitnessMemory
import AllowedipsProjection
namespace Binary.AllowedipsWitness
open Leanux Leanux.WG AllowedipsRelation
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def nodes : NodeId → Option AipNode := fun id => device.nodes.get? id

def row (id : Fin 10) : NodeFixture := fixtures[id.val]'(by simp [fixtures])

theorem node_present (id : Fin 10) : nodes id.val = some (row id).node := by
  rcases id with ⟨id, bound⟩
  have cases : id = 0 ∨ id = 1 ∨ id = 2 ∨ id = 3 ∨ id = 4 ∨ id = 5 ∨ id = 6 ∨ id = 7 ∨ id = 8 ∨ id = 9 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem reached4 (id : NodeId) (reach : Reached nodes (some 7) 32 key4 id) :
    id = 7 ∨ id = 0 ∨ id = 2 ∨ id = 4 ∨ id = 5 := by
  induction reach with
  | root id eq => cases eq; exact .inl rfl
  | child id node next reached present matched short link ih =>
    rcases ih with rfl | rfl | rfl | rfl | rfl
    · have selected : nodes 7 = some (row 7).node := node_present 7
      rw [selected] at present
      cases Option.some.inj present
      change some (some 0) = some (some next) at link
      simp only [Option.some.injEq] at link
      exact .inr (.inl link.symm)
    · have selected : nodes 0 = some (row 0).node := node_present 0
      rw [selected] at present
      cases Option.some.inj present
      change some (some 2) = some (some next) at link
      simp only [Option.some.injEq] at link
      exact .inr (.inr (.inl link.symm))
    · have selected : nodes 2 = some (row 2).node := node_present 2
      rw [selected] at present
      cases Option.some.inj present
      change some (some 4) = some (some next) at link
      simp only [Option.some.injEq] at link
      exact .inr (.inr (.inr (.inl link.symm)))
    · have selected : nodes 4 = some (row 4).node := node_present 4
      rw [selected] at present
      cases Option.some.inj present
      change some (some 5) = some (some next) at link
      simp only [Option.some.injEq] at link
      exact .inr (.inr (.inr (.inr link.symm)))
    · have selected : nodes 5 = some (row 5).node := node_present 5
      rw [selected] at present
      cases Option.some.inj present
      change some none = some (some next) at link
      simp only [Option.some.injEq] at link
      cases link
theorem reached6 (id : NodeId) (reach : Reached nodes (some 1) 128 key6 id) :
    id = 1 ∨ id = 9 ∨ id = 8 := by
  induction reach with
  | root id eq => cases eq; exact .inl rfl
  | child id node next reached present matched short link ih =>
    rcases ih with rfl | rfl | rfl
    · have selected : nodes 1 = some (row 1).node := node_present 1
      rw [selected] at present
      cases Option.some.inj present
      change some (some 9) = some (some next) at link
      exact .inr (.inl (Option.some.inj (Option.some.inj link)).symm)
    · have selected : nodes 9 = some (row 9).node := node_present 9
      rw [selected] at present
      cases Option.some.inj present
      change some (some 8) = some (some next) at link
      exact .inr (.inr (Option.some.inj (Option.some.inj link)).symm)
    · have selected : nodes 8 = some (row 8).node := node_present 8
      rw [selected] at present
      cases Option.some.inj present
      change some none = some (some next) at link
      cases Option.some.inj link

theorem fields4_7 : NodeFields (memory 32 key4) nodeAddress peerAddress 32 key4 7 (row 7).node := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_⟩
    change (memory 32 key4).loadInt (nodeAddress 7 + .ofNat 64 AllowedipsLayout.bits) 4 = some (row 7).node.bits
    witness_read
  · witness_read
  · intro matched
    refine ⟨?_, ?_, ?_⟩
    · witness_read
    · intro pid atPeer
      change none = some pid at atPeer
      cases atPeer
    · intro short
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · witness_read
      · witness_read
      · intro next atNext
        change some (some 0) = some next at atNext
        cases Option.some.inj atNext
        refine ⟨?_, ?_⟩
        · change (memory 32 key4).loadInt (nodeAddress 7 + .ofNat 64 (AllowedipsLayout.bit + 8*0)) 8 = some (pointer nodeAddress (some 0)).toNat
          witness_read
        · intro nid atId
          cases Option.some.inj atId
          decide

#print axioms fields4_7

theorem fields4_0 : NodeFields (memory 32 key4) nodeAddress peerAddress 32 key4 0 (row 0).node := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_⟩
    change (memory 32 key4).loadInt (nodeAddress 0 + .ofNat 64 AllowedipsLayout.bits) 4 = some (row 0).node.bits
    witness_read
  · witness_read
  · intro matched
    refine ⟨?_, ?_, ?_⟩
    · witness_read
    · intro pid atPeer
      change some 0 = some pid at atPeer
      cases Option.some.inj atPeer
      decide
    · intro short
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · witness_read
      · witness_read
      · intro next atNext
        change some (some 2) = some next at atNext
        cases Option.some.inj atNext
        refine ⟨?_, ?_⟩
        · change (memory 32 key4).loadInt (nodeAddress 0 + .ofNat 64 (AllowedipsLayout.bit + 8*0)) 8 = some (pointer nodeAddress (some 2)).toNat
          witness_read
        · intro nid atId
          cases Option.some.inj atId
          decide

#print axioms fields4_0

theorem fields4_2 : NodeFields (memory 32 key4) nodeAddress peerAddress 32 key4 2 (row 2).node := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_⟩
    change (memory 32 key4).loadInt (nodeAddress 2 + .ofNat 64 AllowedipsLayout.bits) 4 = some (row 2).node.bits
    witness_read
  · witness_read
  · intro matched
    refine ⟨?_, ?_, ?_⟩
    · witness_read
    · intro pid atPeer
      change some 1 = some pid at atPeer
      cases Option.some.inj atPeer
      decide
    · intro short
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · witness_read
      · witness_read
      · intro next atNext
        change some (some 4) = some next at atNext
        cases Option.some.inj atNext
        refine ⟨?_, ?_⟩
        · change (memory 32 key4).loadInt (nodeAddress 2 + .ofNat 64 (AllowedipsLayout.bit + 8*0)) 8 = some (pointer nodeAddress (some 4)).toNat
          witness_read
        · intro nid atId
          cases Option.some.inj atId
          decide

#print axioms fields4_2

theorem fields4_4 : NodeFields (memory 32 key4) nodeAddress peerAddress 32 key4 4 (row 4).node := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_⟩
    change (memory 32 key4).loadInt (nodeAddress 4 + .ofNat 64 AllowedipsLayout.bits) 4 = some (row 4).node.bits
    witness_read
  · witness_read
  · intro matched
    refine ⟨?_, ?_, ?_⟩
    · witness_read
    · intro pid atPeer
      change some 2 = some pid at atPeer
      cases Option.some.inj atPeer
      decide
    · intro short
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · witness_read
      · witness_read
      · intro next atNext
        change some (some 5) = some next at atNext
        cases Option.some.inj atNext
        refine ⟨?_, ?_⟩
        · change (memory 32 key4).loadInt (nodeAddress 4 + .ofNat 64 (AllowedipsLayout.bit + 8*0)) 8 = some (pointer nodeAddress (some 5)).toNat
          witness_read
        · intro nid atId
          cases Option.some.inj atId
          decide

#print axioms fields4_4

theorem fields4_5 : NodeFields (memory 32 key4) nodeAddress peerAddress 32 key4 5 (row 5).node := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_⟩
    change (memory 32 key4).loadInt (nodeAddress 5 + .ofNat 64 AllowedipsLayout.bits) 4 = some (row 5).node.bits
    witness_read
  · witness_read
  · intro matched
    refine ⟨?_, ?_, ?_⟩
    · witness_read
    · intro pid atPeer
      change some 3 = some pid at atPeer
      cases Option.some.inj atPeer
      decide
    · intro short
      change 32 < 32 at short
      omega

#print axioms fields4_5

theorem fields6_1 : NodeFields (memory 128 key6) nodeAddress peerAddress 128 key6 1 (row 1).node := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_⟩
    change (memory 128 key6).loadInt (nodeAddress 1 + .ofNat 64 AllowedipsLayout.bits) 8 = some ((row 1).node.bits / 2^64 : Nat) ∧ _
    constructor
    · witness_read
    · intro same
      change (memory 128 key6).loadInt (nodeAddress 1 + .ofNat 64 (AllowedipsLayout.bits+8)) 8 = some ((row 1).node.bits % 2^64 : Nat)
      witness_read
  · witness_read
  · intro matched
    refine ⟨?_, ?_, ?_⟩
    · witness_read
    · intro pid atPeer
      change some 0 = some pid at atPeer
      cases Option.some.inj atPeer
      decide
    · intro short
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · witness_read
      · witness_read
      · intro next atNext
        change some (some 9) = some next at atNext
        cases Option.some.inj atNext
        refine ⟨?_, ?_⟩
        · change (memory 128 key6).loadInt (nodeAddress 1 + .ofNat 64 (AllowedipsLayout.bit + 8*0)) 8 = some (pointer nodeAddress (some 9)).toNat
          witness_read
        · intro nid atId
          cases Option.some.inj atId
          decide

#print axioms fields6_1

theorem fields6_9 : NodeFields (memory 128 key6) nodeAddress peerAddress 128 key6 9 (row 9).node := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_⟩
    change (memory 128 key6).loadInt (nodeAddress 9 + .ofNat 64 AllowedipsLayout.bits) 8 = some ((row 9).node.bits / 2^64 : Nat) ∧ _
    constructor
    · witness_read
    · intro same
      change (memory 128 key6).loadInt (nodeAddress 9 + .ofNat 64 (AllowedipsLayout.bits+8)) 8 = some ((row 9).node.bits % 2^64 : Nat)
      witness_read
  · witness_read
  · intro matched
    refine ⟨?_, ?_, ?_⟩
    · witness_read
    · intro pid atPeer
      change none = some pid at atPeer
      cases atPeer
    · intro short
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · witness_read
      · witness_read
      · intro next atNext
        change some (some 8) = some next at atNext
        cases Option.some.inj atNext
        refine ⟨?_, ?_⟩
        · change (memory 128 key6).loadInt (nodeAddress 9 + .ofNat 64 (AllowedipsLayout.bit + 8*1)) 8 = some (pointer nodeAddress (some 8)).toNat
          witness_read
        · intro nid atId
          cases Option.some.inj atId
          decide

#print axioms fields6_9

theorem fields6_8 : NodeFields (memory 128 key6) nodeAddress peerAddress 128 key6 8 (row 8).node := by
  refine ⟨by decide, by decide, ?_, ?_, ?_⟩
  · refine ⟨by decide, by decide, ?_⟩
    change (memory 128 key6).loadInt (nodeAddress 8 + .ofNat 64 AllowedipsLayout.bits) 8 = some ((row 8).node.bits / 2^64 : Nat) ∧ _
    constructor
    · witness_read
    · intro same
      change (memory 128 key6).loadInt (nodeAddress 8 + .ofNat 64 (AllowedipsLayout.bits+8)) 8 = some ((row 8).node.bits % 2^64 : Nat)
      witness_read
  · witness_read
  · intro matched
    refine ⟨?_, ?_, ?_⟩
    · witness_read
    · intro pid atPeer
      change some 4 = some pid at atPeer
      cases Option.some.inj atPeer
      decide
    · intro short
      refine ⟨rfl, rfl, ?_, ?_, ?_⟩
      · witness_read
      · witness_read
      · intro next atNext
        change some none = some next at atNext
        cases Option.some.inj atNext
        refine ⟨?_, ?_⟩
        · change (memory 128 key6).loadInt (nodeAddress 8 + .ofNat 64 (AllowedipsLayout.bit + 8*0)) 8 = some (pointer nodeAddress none).toNat
          witness_read
        · intro nid atId
          cases atId

#print axioms fields6_8

theorem trie4 : TrieHeap (memory 32 key4) nodeAddress peerAddress nodes (some 7) 32 key4 := by
  refine ⟨by decide, by decide, ?_⟩
  intro id reached
  rcases reached4 id reached with rfl | rfl | rfl | rfl | rfl
  · exact ⟨(row 7).node, node_present 7, fields4_7⟩
  · exact ⟨(row 0).node, node_present 0, fields4_0⟩
  · exact ⟨(row 2).node, node_present 2, fields4_2⟩
  · exact ⟨(row 4).node, node_present 4, fields4_4⟩
  · exact ⟨(row 5).node, node_present 5, fields4_5⟩

#print axioms trie4
theorem trie6 : TrieHeap (memory 128 key6) nodeAddress peerAddress nodes (some 1) 128 key6 := by
  refine ⟨by decide, by decide, ?_⟩
  intro id reached
  rcases reached6 id reached with rfl | rfl | rfl
  · exact ⟨(row 1).node, node_present 1, fields6_1⟩
  · exact ⟨(row 9).node, node_present 9, fields6_9⟩
  · exact ⟨(row 8).node, node_present 8, fields6_8⟩

#print axioms trie6
end Binary.AllowedipsWitness
