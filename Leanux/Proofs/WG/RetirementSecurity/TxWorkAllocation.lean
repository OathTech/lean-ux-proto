import Leanux.Proofs.WG.RetirementSecurity.TxWorkCreate

/-! Fresh native allocation leaves existing service obligations intact,
then the original createData call establishes service for the new owning batch.
Freshness is derived from campaign 1's packet allocation frontier. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem allocation_work (packets : List DataPacket) : SameView queued (packets.mapM newTxSkb) := by
  intro initial
  apply mapM_view_spec id (fun w=>queued w=initial)
  intro packet
  unfold newTxSkb
  apply hoare_liftSkb
  intro w d store before device
  simpa only [id_eq,queued,device,Option.map_some,Option.getD_some] using before

theorem Obligations.allocate (before : Obligations crypt tx w) (bounded : Packets.Inv w)
    (packets : List DataPacket) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a=.ok ((items,v),b)) : Obligations crypt tx v := by
  have perimeter:=(ProjectedAction.iff_run_ambient _ _ _).mp (allocate_perimeter packets) w a items v b run
  apply before.head_frames
    (queueContents_of_peers (congrArg (fun fields=>fields.2.1) perimeter))
    ?_
    (crypt_items_eq ((ProjectedAction.iff_run_ambient _ _ _).mp
      (TxDisposition.LiveFrontier.allocation_ring packets) w a items v b run))
    ((ProjectedAction.iff_run_ambient _ _ _).mp (allocation_work packets) w a items v b run)
  intro pid p found batch member first head
  obtain ⟨id,packet,chosen,resident,_⟩:=before.batches pid p found batch member
  have same:id=first := Option.some.inj (chosen.symm.trans head)
  subst id
  exact ((TxDisposition.ItemSeparation.allocate_resident bounded resident run).2).trans resident.symm

theorem Obligations.allocate_create (before : Obligations crypt tx w)
    (inventory : TxInventory locals w) (bounded : Packets.Inv w)
    (physical : TxDisposition.LiveFrontier.Physical w) (device : w.dev=some d)
    (pid : PeerId) (packets : List DataPacket) (a b : Ambient)
    (run : ((do let items←packets.mapM newTxSkb; createData pid items).run w).run a=
      .ok (((),v),b)) : Obligations crypt tx v := by
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨items,u,c,allocated,created⟩:=run
  have pending:=before.allocate bounded packets a c allocated
  have owned:=inventory.allocate bounded device pid packets a c allocated
  have same:=(ProjectedAction.iff_run_ambient _ _ _).mp
    (TxDisposition.LiveFrontier.allocation_ring packets) w a items u c allocated
  have physicalAfter:=TxDisposition.LiveFrontier.physical_transport same physical
  cases after:u.dev with
  | none=>simp [TxRing.nativeCell,after,device] at same
  | some result=>exact pending.create owned physicalAfter after c b created

end Leanux.Proofs.WG.RetirementSecurity.TxWork
