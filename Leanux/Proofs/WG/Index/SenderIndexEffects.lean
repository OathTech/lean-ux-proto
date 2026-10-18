import Leanux.Proofs.WG.Index.SenderIndexModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise TimerDiscipline Std.Do Leanux.Proofs.Framing
open Queues.RxCredits

theorem senderFields_peerWrite (d : Device) (pid : PeerId) (p q : Peer)
    (resident : d.peers[pid]? = some p) (same : senderPeerCell q = senderPeerCell p) :
    senderDeviceCell {d with peers := d.peers.insert pid q} = senderDeviceCell d := by
  simp only [senderDeviceCell,Prod.mk.injEq,true_and]
  funext target
  by_cases equal : pid = target
  · subst target; simp [resident,same]
  · simp [Std.TreeMap.getElem?_insert,equal]

theorem senderDeviceCell_coherent (d e : Device)
    (same : senderDeviceCell e = senderDeviceCell d)
    (pre : HashedOwnersCoherent d) : HashedOwnersCoherent e := by
  have table : e.indexTable = d.indexTable := congrArg Prod.fst same
  have keys (kid : KeypairId) : e.keypairs[kid]? = d.keypairs[kid]? :=
    congrFun (congrArg (fun x => x.2.2.1) same) kid
  have peers (target : PeerId) : e.peers[target]?.map senderPeerCell = d.peers[target]?.map senderPeerCell :=
    congrFun (congrArg (fun x => x.2.2.2) same) target
  have word (owner : IndexOwner) : ownerWord e owner = ownerWord d owner := by
    cases owner with
    | keypair kid => simp only [ownerWord,keys]
    | handshake target =>
      have projected := congrArg (Option.map (fun x : SenderPeerCell => x.2.2.1)) (peers target)
      simpa [ownerWord,senderPeerCell,Option.map_map,Function.comp_def] using projected
  intro entry member
  obtain ⟨target,p,stored,found,positive,kind⟩ := pre entry (table ▸ member)
  have current : e.peers[target]?.map senderPeerCell = some (senderPeerCell p) := by
    rw [peers,found]; rfl
  obtain ⟨q,resident,cell⟩ := Option.map_eq_some_iff.mp current
  have refs : q.refcount = p.refcount := congrArg (fun x => x.2.1) cell
  refine ⟨target,q,(word entry.owner).trans stored,resident,refs ▸ positive,?_⟩
  cases shape : entry.owner with
  | handshake own => simpa only [shape] using kind
  | keypair kid => simpa only [shape,keys] using kind

theorem senderDeviceCell_transports (d e : Device) (retired : Reservations) (pid : PeerId)
    (same : senderDeviceCell e = senderDeviceCell d) :
    (HashSlotCoverage d → HashSlotCoverage e) ∧
    (DeadHashedReserved retired d → DeadHashedReserved retired e) ∧
    (HandshakeCompatible pid d → HandshakeCompatible pid e) := by
  have table : e.indexTable = d.indexTable := congrArg Prod.fst same
  have epoch : e.ifindex = d.ifindex := congrArg (fun x => x.2.1) same
  have keys (kid : KeypairId) : e.keypairs[kid]? = d.keypairs[kid]? :=
    congrFun (congrArg (fun x => x.2.2.1) same) kid
  have peers (target : PeerId) : e.peers[target]?.map senderPeerCell = d.peers[target]?.map senderPeerCell :=
    congrFun (congrArg (fun x => x.2.2.2) same) target
  have word (owner : IndexOwner) : ownerWord e owner = ownerWord d owner := by
    cases owner with
    | keypair kid => simp only [ownerWord,keys]
    | handshake target =>
      have projected := congrArg (Option.map (fun x : SenderPeerCell => x.2.2.1)) (peers target)
      simpa [ownerWord,senderPeerCell,Option.map_map,Function.comp_def] using projected
  refine ⟨?_,?_,?_⟩
  · intro pre
    apply hashSlotCoverage_transport d e table ?_ (fun kid => congrArg (Option.map Keypair.peer) (keys kid)) pre
    intro target
    have projected := congrArg (Option.map Prod.fst) (peers target)
    simpa [senderPeerCell,Option.map_map,Function.comp_def] using projected
  · intro pre
    apply deadHashedReserved_transport retired d e epoch (fun entry member => table ▸ member)
      (fun entry _ _ _ => word entry.owner) ?_ pre
    intro target q current
    have observed := (peers target).symm
    rw [current] at observed
    obtain ⟨p,found,cell⟩ := Option.map_eq_some_iff.mp observed
    exact ⟨p,found,congrArg (fun x => x.2.2.2.1) cell,congrArg (fun x => x.2.2.2.2) cell⟩
  · intro pre
    refine ⟨senderDeviceCell_coherent d e same pre.1,?_⟩
    intro q current
    have observed := (peers pid).symm
    rw [current] at observed
    obtain ⟨p,found,cell⟩ := Option.map_eq_some_iff.mp observed
    have refs : p.refcount = q.refcount := congrArg (fun x => x.2.1) cell
    have self : p.handshakeEntryPeer = q.handshakeEntryPeer := congrArg (fun x => x.2.2.1) cell
    simpa only [← refs,← self] using pre.2 p found

end Leanux.Proofs.WG.Index
