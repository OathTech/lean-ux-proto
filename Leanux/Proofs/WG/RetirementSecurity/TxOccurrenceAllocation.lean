import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceFrames

/-! Native staged allocation creates one unpublished physical batch. Its
IDs are fresh against all queued and caller-held packets by the existing
packet frontier; no batch-separation hypothesis is required at allocation. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem allocate_items_resident (packets : List DataPacket) (device : w.dev = some d)
    (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    ∀ id ∈ items, ∃ packet, Queues.TxDisposition.txPackets v id = some packet := by
  induction packets generalizing w d a b items v with
  | nil => simp only [List.mapM_nil] at run; cases run; simp
  | cons packet rest ih =>
    simp only [List.mapM_cons,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨first,u,c,headRun,tail,t,e,tailRun,done⟩ := run
    rw [Packets.newTxSkb_run w a d packet device] at headRun
    cases headRun
    cases done
    let next := {d with txSkbs := d.txSkbs.insert d.nextSkb packet,nextSkb := d.nextSkb + 1}
    have after : (Packets.update w (fun current => {current with
        txSkbs := current.txSkbs.insert d.nextSkb packet,nextSkb := d.nextSkb + 1})).dev = some next := by
      simp [Packets.update,device,next]
    intro id member
    rcases List.mem_cons.mp member with same | inTail
    · subst id
      obtain ⟨_,_,_,_,_,_,kept⟩ := Queues.TxDisposition.ItemSeparation.allocate_result rest after tailRun
      exact ⟨packet,by
        rw [kept d.nextSkb (by simp [next])]
        simp [Queues.TxDisposition.txPackets,Packets.update,device]⟩
    · exact ih after a b tailRun id inTail

theorem TxInventory.allocate (inventory : TxInventory locals w)
    (bounded : Packets.Inv w) (device : w.dev = some d) (pid : PeerId)
    (packets : List DataPacket) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    TxInventory (⟨.unpublished,pid,items⟩ :: locals) v := by
  have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
    (allocate_perimeter packets) w a items v b run
  have peers : peersAt v = peersAt w := congrArg (fun fields => fields.2.1) perimeter
  have peerCells : ∀ other, peerAt v other = peerAt w other := by
    intro other
    simpa [peerAt,peersAt,Option.bind_map,Function.comp_def] using
      congrArg (fun cells => cells.bind fun entries => entries[other]?) peers
  have kept := inventory.transport (fun other p found => ⟨p,(peerCells other).symm.trans found,rfl⟩)
    (fun id packet found => ⟨packet,(Queues.TxDisposition.ItemSeparation.allocate_resident bounded found run).2⟩)
  have fresh : ∀ id packet, Queues.TxDisposition.txPackets w id = some packet → id ∉ items :=
    fun _ _ found => (Queues.TxDisposition.ItemSeparation.allocate_resident bounded found run).1
  have newResident := allocate_items_resident packets device a b run
  refine ⟨?_,kept.queueUnique,kept.peersSeparate,?_,?_,kept.queueResident⟩
  · change (items ++ txLocalItems locals).Nodup
    refine List.nodup_append.mpr
      ⟨Queues.TxDisposition.ItemSeparation.allocate_nodup device run,inventory.localUnique,?_⟩
    intro id member other old same
    subst other
    obtain ⟨packet,resident⟩ := inventory.localResident id old
    exact fresh id packet resident member
  · intro other p found id member queued
    rcases List.mem_append.mp member with new | old
    · obtain ⟨packet,resident⟩ := inventory.queueResident other p
        ((peerCells other).symm.trans found) id queued
      exact fresh id packet resident new
    · exact kept.localsSeparate other p found id old queued
  · intro id member
    rcases List.mem_append.mp member with new | old
    · exact newResident id new
    · exact kept.localResident id old

end Leanux.Proofs.WG.RetirementSecurity
