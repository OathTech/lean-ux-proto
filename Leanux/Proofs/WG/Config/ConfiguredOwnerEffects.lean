import Leanux.Proofs.WG.Config.ConfiguredOwnerModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps

theorem configuredOwners_empty (d : Device) : ConfiguredOwners d .empty .empty := by
  intro e member
  simp only [Tree.entries,List.append_nil,List.not_mem_nil] at member

theorem configuredOwners_resident (d : Device) (t4 t6 : Tree)
    (owners : ConfiguredOwners d t4 t6)
    (listed : ∀ pid ∈ d.peerList, ∃ p, d.peers[pid]? = some p)
    (lists : ResidentLists d t4 t6) : ResidentOwnerLists d t4 t6 := by
  intro e member
  obtain ⟨p,found⟩ := listed e.peer (owners e member)
  exact ⟨p,found,((lists e.peer p found).2 e.id).mpr ⟨e,member,rfl,rfl⟩⟩

theorem configuredOwners_inserted (d out : Device) (t4 t6 : Tree)
    (v4 : Bool) (addr cidr pid : Nat)
    (routing : RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6) (selected : pid ∈ d.peerList)
    (frame : out.peerList = d.peerList)
    (addrBound : addr < 2 ^ rootWidth v4) (cidrBound : cidr ≤ rootWidth v4) :
    ConfiguredOwners out (insertedTree4 d v4 t4 addr cidr pid)
      (insertedTree6 d v4 t6 addr cidr pid) := by
  intro e member
  rw [frame]
  cases v4 with
  | false =>
    change e ∈ t4.entries ++ (t6.insertFresh 128 d.nextNode addr cidr pid).tree.entries at member
    rcases List.mem_append.mp member with old | changed
    · exact owners e (List.mem_append_left _ old)
    · rcases (Tree.insertFresh_entries routing.valid6 addrBound cidrBound d.nextNode pid e).mp changed with same | ⟨old,_⟩
      · subst e
        simpa only [Tree.insertFresh_peer] using selected
      · exact owners e (List.mem_append_right _ old)
  | true =>
    change e ∈ (t4.insertFresh 32 d.nextNode addr cidr pid).tree.entries ++ t6.entries at member
    rcases List.mem_append.mp member with changed | old
    · rcases (Tree.insertFresh_entries routing.valid4 addrBound cidrBound d.nextNode pid e).mp changed with same | ⟨old,_⟩
      · subst e
        simpa only [Tree.insertFresh_peer] using selected
      · exact owners e (List.mem_append_left _ old)
    · exact owners e (List.mem_append_right _ old)

theorem configuredOwners_removed (d out : Device) (t4 t6 : Tree)
    (pid : PeerId) (p : Peer) (peer : d.peers[pid]? = some p)
    (owners : ConfiguredOwners d t4 t6) (lists : ResidentLists d t4 t6)
    (frame : out.peerList = d.peerList.filter (· != pid)) :
    ConfiguredOwners out (t4.eraseIds p.allowedipsList) (t6.eraseIds p.allowedipsList) := by
  intro e member
  rw [Tree.eraseIds_entries,Tree.eraseIds_entries,←List.filter_append] at member
  obtain ⟨old,notRemoved⟩ := List.mem_filter.mp member
  have different : e.peer ≠ pid := by
    intro same
    have stored := ((lists pid p peer).2 e.id).mpr ⟨e,old,rfl,same⟩
    simp only [List.contains_eq_mem,stored,decide_true,Bool.not_true,Bool.false_eq_true] at notRemoved
  rw [frame]
  exact List.mem_filter.mpr ⟨owners e old,by simpa only [bne_iff_ne] using different⟩

theorem allowedipRoutingEffect_configured (d out : Device) (t4 t6 : Tree)
    (pid : PeerId) (attrs : AllowedIpAttrs) (ret : Int)
    (routing : RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6) (selected : pid ∈ d.peerList)
    (effect : AllowedipRoutingEffect d out t4 t6 pid attrs ret) :
    ∃ u4 u6, RoutingInvariant out u4 u6 ∧ ConfiguredOwners out u4 u6 := by
  rcases effect with ⟨_,rfl⟩ | ⟨v4,_,addrBound,cidrBound,outcome⟩
  · exact ⟨t4,t6,routing,owners⟩
  · have frame : out.peerList = d.peerList := by
      have same := congrArg Device.peerList outcome.frame
      exact same
    rcases outcome.result with ⟨_,_,next⟩ | ⟨_,refused⟩
    · exact ⟨_,_,next,configuredOwners_inserted d out t4 t6 v4
        (attrs.addr.getD 0) (attrs.cidr.getD 0) pid routing owners selected frame addrBound cidrBound⟩
    · exact ⟨t4,t6,refused.invariant,fun e member => frame.symm ▸ owners e member⟩

theorem allowedipRoutingEffect_listed (d out : Device) (t4 t6 : Tree)
    (pid : PeerId) (attrs : AllowedIpAttrs) (ret : Int)
    (listed : ∀ q ∈ d.peerList, ∃ p, d.peers[q]? = some p)
    (effect : AllowedipRoutingEffect d out t4 t6 pid attrs ret) :
    ∀ q ∈ out.peerList, ∃ p, out.peers[q]? = some p := by
  rcases effect with ⟨_,rfl⟩ | ⟨v4,_,_,_,outcome⟩
  · exact listed
  · have frame : out.peerList = d.peerList := by
      have same := congrArg Device.peerList outcome.frame
      exact same
    intro q member
    obtain ⟨old,present⟩ := listed q (frame ▸ member)
    rcases outcome.result with ⟨_,inserted,_⟩ | ⟨_,refused⟩
    · rw [inserted.peers]
      change ∃ p, (d.peers[q]?).map _ = some p
      rw [present]
      exact ⟨_,rfl⟩
    · exact ⟨old,(refused.peers q).trans present⟩


end Leanux.Proofs.WG.Config
