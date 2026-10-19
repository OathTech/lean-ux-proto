import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextAdmission

/-! Actual allocator freshness retains each resident queued packet. The
physical census supplies residency; no old packet may be replaced by a fresh
empty-buffer allocation under the same numeric ID. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem allocate (before : Inv w) (inventory : TxInventory locals w)
    (bounded : Packets.Inv w) (packets : List DataPacket) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((items,v),b)) : Inv v := by
  have perimeter:=(ProjectedAction.iff_run_ambient _ _ _).mp
    (allocate_perimeter packets) w a items v b run
  have peers:peersAt v=peersAt w:=congrArg (fun fields=>fields.2.1) perimeter
  have cells:∀pid,peerAt v pid=peerAt w pid:=by
    intro pid
    simpa [peerAt,peersAt,Option.bind_map,Function.comp_def] using
      congrArg (fun entries=>entries.bind fun table=>table[pid]?) peers
  intro pid p resident batch member first head crypted
  have oldPeer:=(cells pid).symm.trans resident
  have kept (id : SkbId) (inside : id∈batch) : TxDisposition.txPackets v id=TxDisposition.txPackets w id := by
    obtain ⟨old,stored⟩:=inventory.queueResident pid p oldPeer id (List.mem_flatten.mpr ⟨batch,member,inside⟩)
    exact (TxDisposition.ItemSeparation.allocate_resident bounded stored run).2.trans stored.symm
  have oldHead:TxDisposition.HeadState first .crypted w:=by
    obtain ⟨packet,stored,mark⟩:=crypted
    exact ⟨packet,kept first (List.mem_of_head? head) ▸ stored,mark⟩
  have complete:=before pid p oldPeer batch member first head oldHead
  intro id inside
  exact (complete id inside).frame (kept id inside)

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext
