import Leanux.Proofs.WG.RetirementSecurity.HolderResponseSession
import Leanux.Proofs.WG.RetirementSecurity.RemovalPeerFunding
import Leanux.Proofs.WG.Queues.BaseLookupRemoval
import Leanux.Proofs.WG.Queues.SessionCarrier

/-! Session publication retains the selected peer's independent base reference.
The selected occurrence is derived from actual funded holders and source lookup;
the handshake's temporary acquisition is never counted as that base reference. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

variable {holders : DurableHolders} {w v : WGWorld} {d : Device} {p : Peer}

theorem base_peer_reference (funded : holders.Funded carriers loans w)
    (selected : pid ∈ holders.base.map Owner.slot)
    (device : w.dev = some d) (stored : d.peers[pid]? = some p) :
    (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ holders.base := by
  obtain ⟨o,member,slot⟩ := List.mem_map.mp selected
  have allMember : o ∈ holders.owners := by simp [DurableHolders.owners,member]
  obtain ⟨q,resident⟩ := funded.resident allMember
  obtain ⟨old,oldDevice,epoch,oldStored,stamp⟩ := resident_fields resident
  have devices : old = d := Option.some.inj (oldDevice.symm.trans device)
  subst old
  rw [slot] at oldStored
  have peers : q = p := Option.some.inj (oldStored.symm.trans stored)
  subst q
  have owner : o = ⟨d.ifindex,pid,p.internalId⟩ := by
    cases o
    simp_all
  simpa only [owner] using member

theorem SlotPeerReferences.selected_transport
    (before : SlotPeerReferences holders loans w)
    (selected : ∀ d p, w.dev = some d → d.peers[pid]? = some p →
      (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ holders.base ++ loans)
    (peers : peerView v = peerView w)
    (perimeter : holderPerimeter pid v = holderPerimeter pid w) :
    SlotPeerReferences holders loans v := by
  intro d other p device stored slots
  have epoch := congrArg Prod.fst peers
  cases oldDevice : w.dev with
  | none => simp [peerView,device,oldDevice] at epoch
  | some old =>
    have sameEpoch : d.ifindex = old.ifindex := by
      simpa only [peerView,device,oldDevice,Option.map_some,Option.some.injEq] using epoch
    have cell := congrFun (congrArg Prod.snd peers) other
    have mapped : (old.peers[other]?).map (fun q => (q.internalId,q.refcount,q.rxQueue)) =
        some (p.internalId,p.refcount,p.rxQueue) := by
      simpa only [peerView,device,oldDevice,Option.bind_some,stored,Option.map_some] using cell.symm
    obtain ⟨q,resident,fields⟩ := Option.map_eq_some_iff.mp mapped
    have stamp : q.internalId = p.internalId := congrArg Prod.fst fields
    by_cases same : other = pid
    · subst other
      simpa only [sameEpoch,stamp] using selected old q oldDevice resident
    · have unchanged := congrFun (congrArg Prod.fst perimeter) other
      have equal : p = q := by
        simpa only [holderPerimeter,peersAt,device,oldDevice,Option.map_some,
          Option.bind_some,ite_eq_right same,stored,resident,Option.some.injEq] using unchanged
      subst q
      simpa only [sameEpoch] using before old other p oldDevice resident slots

/-- Session allocation and rotation cannot remove independent peer protection:
the selected base occurrence remains distinct from its temporary caller loan. -/
theorem SlotPeerReferences.session_from_base
    (before : SlotPeerReferences holders loans w)
    (funded : holders.Funded carriers loans w)
    (selected : pid ∈ holders.base.map Owner.slot) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    SlotPeerReferences holders loans v := by
  apply before.selected_transport (pid := pid)
  · intro d p device stored
    exact List.mem_append_left _ (base_peer_reference funded selected device stored)
  · exact congrArg (fun s => s.1.1) ((ProjectedAction.iff_run_ambient _ _ _).mp
      (SessionCarrier.beginSession_view pid) w a result v b run)
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp (session_perimeter pid) w a result v b run

/-- Successful native public-key lookup identifies an actual stamped base
reference in addition to the newly acquired handshake loan. -/
theorem pubkey_selected_base_reference (key : Key)
    (funded : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (coherent : BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (a b : Ambient)
    (run : ((pubkeyLookup key).run w).run a = .ok ((some pid,v),b)) :
    ∃ o : Owner, o.slot = pid ∧ holders.Funded carriers (o :: loans) v ∧
      pid ∈ holders.base.map Owner.slot ∧
      ∀ d p, v.dev = some d → d.peers[pid]? = some p →
        (⟨d.ifindex,pid,p.internalId⟩ : Owner) ∈ holders.base := by
  obtain ⟨o,slot,paid,_,_,_,selected⟩ :=
    BaseLookupRemoval.lookup_selected key funded stable coherent configured a b run
  exact ⟨o,slot,paid,selected,fun _ _ device stored =>
    base_peer_reference paid selected device stored⟩

end Leanux.Proofs.WG.RetirementSecurity
