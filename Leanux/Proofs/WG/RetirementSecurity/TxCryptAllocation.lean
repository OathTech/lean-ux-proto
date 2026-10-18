import Leanux.Proofs.WG.RetirementSecurity.TxCryptCreate

/-! Fresh allocation preserves every live encryption alias and its actual
queued owner. The native allocator/create composition transports physical
ownership and encryption phase together, without a separate freshness premise. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem TxCryptInventory.allocate (crypt : TxCryptInventory active w)
    (bounded : Packets.Inv w) (packets : List DataPacket) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    TxCryptInventory active v := by
  have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
    (allocate_perimeter packets) w a items v b run
  have peers : peersAt v = peersAt w := congrArg (fun fields => fields.2.1) perimeter
  have peerCells : ∀ other, peerAt v other = peerAt w other := by
    intro other
    simpa [peerAt,peersAt,Option.bind_map,Function.comp_def] using
      congrArg (fun cells => cells.bind fun entries => entries[other]?) peers
  apply crypt.frame ((ProjectedAction.iff_run_ambient _ _ _).mp
    (TxDisposition.LiveFrontier.allocation_ring packets) w a items v b run)
  · intro batch owned
    obtain ⟨pid,p,found,member⟩ := owned
    exact ⟨pid,p,(peerCells pid).trans found,member⟩
  · intro batch member
    obtain ⟨first,head,packet,resident,mark⟩ := crypt.uncrypted batch member
    exact ⟨first,head,packet,
      (TxDisposition.ItemSeparation.allocate_resident bounded resident run).2,mark⟩

/-- The original allocation and creation suffix preserves both actual
packet ownership and exclusive pending/active encryption. The frontier bound
comes from campaign 1; initialized caller transport is a separate obligation. -/
theorem allocate_create_occurrences (inventory : TxInventory locals w)
    (crypt : TxCryptInventory active w) (bounded : Packets.Inv w)
    (device : w.dev = some d) (pid : PeerId) (packets : List DataPacket) (a b : Ambient)
    (run : ((do let items ← packets.mapM newTxSkb; createData pid items).run w).run a =
      .ok (((),v),b)) : TxInventory locals v ∧ TxCryptInventory active v := by
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨items,u,c,allocateRun,createRun⟩ := run
  have owned := inventory.allocate bounded device pid packets a c allocateRun
  have phase := crypt.allocate bounded packets a c allocateRun
  exact ⟨owned.create c b createRun,phase.create owned c b createRun⟩

end Leanux.Proofs.WG.RetirementSecurity
