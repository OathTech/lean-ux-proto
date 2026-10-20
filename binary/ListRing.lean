import Layouts
import Memory

namespace Binary.ListRing
abbrev Address := BitVec 64

/-- One exact list_head, including the backward link used by deletion. -/
def Links (memory : Mem 64) (here previous next : Address) : Prop :=
  memory.loadInt (here + .ofNat 64 Layouts.list_prev) 8 = some (previous.toNat : Int) ∧
  memory.loadInt (here + .ofNat 64 Layouts.list_next) 8 = some (next.toNat : Int)

/-- The finite active chain ends at its sentinel. Retired/unlinked objects
    are not forced to self-link, nor identified with the active list. -/
def Chain (memory : Mem 64) (sentinel : Address) :
    Address → Address → List Address → Prop
  | previous, cursor, [] => cursor = sentinel ∧
      memory.loadInt (sentinel + .ofNat 64 Layouts.list_prev) 8 = some (previous.toNat : Int)
  | previous, cursor, node :: rest =>
      cursor = node ∧ node ≠ sentinel ∧ node ≠ 0 ∧
      ∃ next, Links memory node previous next ∧ Chain memory sentinel node next rest

/-- A circular doubly-linked list is observed as its exact ordered sequence
    of embedded node addresses, starting after the sentinel. -/
def Ring (memory : Mem 64) (sentinel : Address) (nodes : List Address) : Prop :=
  sentinel ≠ 0 ∧ ∃ first,
    memory.loadInt (sentinel + .ofNat 64 Layouts.list_next) 8 = some (first.toNat : Int) ∧
    Chain memory sentinel sentinel first nodes

/-- The exact two-word support, for the sentinel and all active nodes. -/
def Reads (sentinel : Address) (nodes : List Address) (address : Address) : Prop :=
  ∃ node ∈ sentinel :: nodes,
    InRange (node + .ofNat 64 Layouts.list_prev) 8 address ∨
    InRange (node + .ofNat 64 Layouts.list_next) 8 address

private theorem word_unique {a b : Address} {memory : Mem 64} {location : Address}
    (ha : memory.loadInt location 8 = some (a.toNat : Int))
    (hb : memory.loadInt location 8 = some (b.toNat : Int)) : a = b := by
  apply BitVec.eq_of_toNat_eq
  have eq := Option.some.inj (ha.symm.trans hb)
  omega

theorem Chain.functional {memory sentinel previous cursor first second}
    (ha : Chain memory sentinel previous cursor first)
    (hb : Chain memory sentinel previous cursor second) : first = second := by
  induction first generalizing previous cursor second with
  | nil =>
    cases second with
    | nil => rfl
    | cons node rest => exact False.elim (hb.2.1 (hb.1.symm.trans ha.1))
  | cons node rest ih =>
    cases second with
    | nil => exact False.elim (ha.2.1 (ha.1.symm.trans hb.1))
    | cons other tail =>
      obtain ⟨ca, na, za, nextA, linksA, chainA⟩ := ha
      obtain ⟨cb, nb, zb, nextB, linksB, chainB⟩ := hb
      rw [← ca] at linksA chainA
      rw [← cb] at linksB chainB
      have next : nextA = nextB := word_unique linksA.2 linksB.2
      rw [← next] at chainB
      rw [← ca, ← cb, ih chainA chainB]

theorem Ring.functional {memory sentinel first second}
    (ha : Ring memory sentinel first) (hb : Ring memory sentinel second) : first = second := by
  obtain ⟨_, firstA, loadA, chainA⟩ := ha
  obtain ⟨_, firstB, loadB, chainB⟩ := hb
  have eq : firstA = firstB := word_unique loadA loadB
  subst firstB
  exact Chain.functional chainA chainB

private theorem Chain.frame {before after : Mem 64} {writes : Address → Prop}
    (same : EqualOutside writes before after) (sentinel previous cursor : Address)
    (nodes : List Address)
    (apart : ∀ address, Reads sentinel nodes address → ¬writes address)
    (represented : Chain before sentinel previous cursor nodes) :
    Chain after sentinel previous cursor nodes := by
  induction nodes generalizing previous cursor with
  | nil =>
    refine ⟨represented.1, ?_⟩
    exact (same.loadInt _ 8 (fun i hi => apart _ ⟨sentinel, by simp, .inl ⟨i, hi, rfl⟩⟩)).symm.trans represented.2
  | cons node nodes ih =>
    obtain ⟨eq, distinct, nonnull, next, links, tail⟩ := represented
    refine ⟨eq, distinct, nonnull, next, ⟨?_, ?_⟩, ?_⟩
    · exact (same.loadInt _ 8 (fun i hi => apart _ ⟨node, by simp, .inl ⟨i, hi, rfl⟩⟩)).symm.trans links.1
    · exact (same.loadInt _ 8 (fun i hi => apart _ ⟨node, by simp, .inr ⟨i, hi, rfl⟩⟩)).symm.trans links.2
    · apply ih node next _ tail
      rintro address ⟨cell, member, read⟩
      apply apart address
      refine ⟨cell, ?_, read⟩
      rcases List.mem_cons.mp member with sameHead | tailMember
      · exact List.mem_cons.mpr (.inl sameHead)
      · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inr tailMember)))

theorem Ring.frame {before after : Mem 64} {writes : Address → Prop}
    (same : EqualOutside writes before after) (sentinel : Address) (nodes : List Address)
    (apart : ∀ address, Reads sentinel nodes address → ¬writes address)
    (represented : Ring before sentinel nodes) : Ring after sentinel nodes := by
  obtain ⟨nonnull, first, loaded, chain⟩ := represented
  refine ⟨nonnull, first, ?_, Chain.frame same sentinel sentinel first nodes apart chain⟩
  exact (same.loadInt _ 8 (fun i hi => apart _ ⟨sentinel, by simp, .inr ⟨i, hi, rfl⟩⟩)).symm.trans loaded

/-- Device enumeration is the active circular list, not the peer store's
    domain and not num_peers at intermediate teardown cuts. -/
def DevicePeers (memory : Mem 64) (deviceAddress : Address)
    (peers : Leanux.WG.PeerId → Address) (device : Leanux.WG.Device) : Prop :=
  Ring memory (deviceAddress + .ofNat 64 Layouts.device_peer_list)
    (device.peerList.map (fun id => peers id + .ofNat 64 Layouts.peer_peer_list))

/-- An allowed-IPs node is linked through its union's peer_list field while
    active in this peer's list. RCU-retired nodes require separate lifetimes. -/
def PeerAllowedIPs (memory : Mem 64) (peerAddress : Address)
    (nodes : Leanux.WG.NodeId → Address) (peer : Leanux.WG.Peer) : Prop :=
  Ring memory (peerAddress + .ofNat 64 Layouts.peer_allowedips_list)
    (peer.allowedipsList.map (fun id => nodes id + .ofNat 64 Layouts.allowedipsNode_peer_list))

#print axioms Chain.functional
#print axioms Ring.functional
#print axioms Ring.frame
end Binary.ListRing
