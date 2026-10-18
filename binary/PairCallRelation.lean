import PairCallFacts
import PairTrieReadProof
import PairLocalsProof

namespace Binary.Pair.Trie
open Leanux Leanux.WG AllowedipsRelation TrustBase
set_option maxRecDepth 2048

theorem Reconstructed.peer {names : Names} {o : AllowedipsProbe.Offsets}
    {m : DataMem} {d : Device} (fields : Reconstructed names o m (target d))
    {id : PeerId} {peer : Peer} (present : d.peers.get? id = some peer) :
    ∃ base, (id,base) ∈ names.peers ∧ word m s!"peer[{id}].refcount" (base+o.peerRefcount) 4 = .ok peer.refcount := by
  have member : (id,peer.refcount) ∈ (target d).counts :=
    List.mem_map.mpr ⟨(id,peer),Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr present,rfl⟩
  obtain ⟨⟨id',base⟩,named,equal,read⟩ := fields.peers.right _ member
  subst id'
  exact ⟨base,named,read⟩

theorem pointer_some_named {names : List (Nat×Nat)} {path : String} {raw id : Nat}
    (ok : pointer names path raw = .ok (some id)) : ∃ base, (id,base) ∈ names := by
  unfold pointer at ok
  split at ok
  · cases ok
  · cases found : names.find? (·.2 == raw) with
    | none => rw [found] at ok; cases ok
    | some pair =>
      rw [found] at ok
      have equal : pair.1 = id := Option.some.inj (Except.ok.inj ok)
      exact ⟨pair.2,equal ▸ List.mem_of_find?_eq_some found⟩

theorem node_peer_present {names : Names} {o : AllowedipsProbe.Offsets} {m : DataMem} {d : Device}
    (related : Corresponds names o m d) {id : NodeId} {node : AipNode} {pid : PeerId}
    (present : d.nodes.get? id = some node) (selected : node.peer = some pid) :
    ∃ peer, d.peers.get? pid = some peer := by
  have fields := reconstruct_fields related
  obtain ⟨base,_,decoded⟩ := fields.node present
  obtain ⟨raw,_,pointerOk⟩ := (decodeNode_fields decoded).peer
  rw [show (targetNode node).peer = some pid from selected] at pointerOk
  obtain ⟨peerBase,named⟩ := pointer_some_named pointerOk
  obtain ⟨⟨pid',count⟩,member,equal,_⟩ := fields.peers.left (pid,peerBase) named
  obtain ⟨⟨id',peer⟩,source,value⟩ := List.mem_map.mp member
  have same : id' = pid := (Prod.mk.inj value).1.trans equal.symm
  subst id'
  exact ⟨peer,Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp source⟩

def callConfig (names : Names) (w : World) (d : Device)
    (root : Option NodeId) (bits key : Nat) : Config :=
  let selected := (AllowedipsSource.select (fun id => d.nodes.get? id) root bits key).join
  ⟨root,bits,key,interpretation names.nodes,interpretation names.peers,
    ⟨selected,selected.bind (fun id => (d.nodes.get? id).bind (·.peer))⟩,w.steps.toList,w.netRxSection⟩

def callView (c : Config) (d : Device) : View :=
  ⟨fun id => d.nodes.get? id,c.focus.peer.bind (fun id => (d.peers.get? id).map (·.refcount))⟩

theorem callFocus_peer {names w d root bits key}
    {pid : PeerId} (selected : (callConfig names w d root bits key).focus.peer = some pid) :
    ∃ id node, d.nodes.get? id = some node ∧ node.peer = some pid := by
  unfold callConfig at selected
  obtain ⟨id,_,selected⟩ := Option.bind_eq_some_iff.mp selected
  obtain ⟨node,present,word⟩ := Option.bind_eq_some_iff.mp selected
  exact ⟨id,node,present,word⟩

theorem callCount_bytes {names w d root bits key o m}
    (related : Corresponds names o m d) {pid : PeerId}
    (selected : (callConfig names w d root bits key).focus.peer = some pid)
    {a : BitVec 64} (inside : InRange (interpretation names.peers pid + .ofNat 64 Layouts.peer_refcount) 4 a) :
    CountBytes names o a := by
  obtain ⟨id,node,present,word⟩ := callFocus_peer selected
  obtain ⟨peer,presentPeer⟩ := node_peer_present related present word
  have fields := reconstruct_fields related
  obtain ⟨base,named,_⟩ := fields.peer presentPeer
  refine ⟨pid,base,named,?_⟩
  simpa only [interpretation_of_mem fields.peerIds named,fields.layout.2.2.2.2.2.2.2.2,BitVec.ofNat_add] using inside

theorem callRelated {names w d root bits key o s}
    (device : w.k.wg = some d) (related : Corresponds names o s.data.dmem d)
    (heapOk : heap (target d) [d.peerAllowedips.root4,d.peerAllowedips.root6] = .ok ())
    (input : callInput names o s.data.dmem root bits key = .ok ()) :
    R (callConfig names w d root bits key) [s] [LookupObservation.call "lookup" s] s w := by
  let c := callConfig names w d root bits key
  refine ⟨rfl,⟨callView c d,by simp [project,device,callView,c],?_,?_⟩,?_,rfl⟩
  · exact trieHeap_of_checks related heapOk input
  · cases selected : c.focus.peer with
    | none => simp [callView,selected]
    | some pid =>
      obtain ⟨id,node,present,word⟩ := callFocus_peer selected
      obtain ⟨peer,presentPeer⟩ := node_peer_present related present word
      have fields := reconstruct_fields related
      obtain ⟨base,named,read⟩ := fields.peer presentPeer
      have bounds := fields.peerRange pid base named
      refine ⟨peer.refcount,?_,interpretation_nonnull fields.peerIds named bounds.1 (by omega),?_⟩
      · simp only [callView,selected,Option.bind_some,presentPeer,Option.map_some]
      · change s.data.dmem.loadInt (interpretation names.peers pid+.ofNat 64 Layouts.peer_refcount) 4 = some (peer.refcount : Int)
        simpa only [interpretation_of_mem fields.peerIds named,fields.layout.2.2.2.2.2.2.2.2,BitVec.ofNat_add] using
          word_loadInt _ _ _ _ _ read
  · simp [callConfig,LookupObservation.call]

#print axioms callRelated
end Binary.Pair.Trie
