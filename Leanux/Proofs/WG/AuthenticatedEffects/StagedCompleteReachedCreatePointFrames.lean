import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointSource

/-! Same-ledger native mutation frames, before pending access or queued
receipts. The unpublished alias is consumed by the actual peer-queue write;
state marking preserves the exact allocated ticket and material. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompleteCarrier StagedTerminalComplete Staged.Obligations
set_option maxHeartbeats 600000

theorem mark_accounted (id : SkbId) (state : PacketState)
    (before : Accounted history ledger debts locals w)
    (native : ((setTxSkb id fun p=>{p with state}).run w).run a=.ok (((),v),b)) :
    Accounted history ledger debts locals v :=
  ⟨publication_mark_native id state before.entry a b native,before.complete⟩

theorem install_native (pid : PeerId) (peer : Peer) (items : List SkbId)
    (device : w.dev=some d) :
    ((setPeer pid {peer with txQueue:=peer.txQueue.enqueue items}).run w).run a=
      .ok (((),replacePeer w d pid {peer with txQueue:=peer.txQueue.enqueue items}),a) := by
  simp [setPeer,modifyDev,device,replacePeer]

theorem install_accounted (pid : PeerId) (peer : Peer) (items : List SkbId)
    (device : w.dev=some d) (resident : d.peers[pid]?=some peer)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w) :
    Accounted history ledger debts locals
      (replacePeer w d pid {peer with txQueue:=peer.txQueue.enqueue items}) := by
  have material:=QueueHandoff.installed_material (pid:=pid)
    (p:={peer with txQueue:=peer.txQueue.enqueue items}) device
  have core:=before.entry.core.quiet_views
    (v:=replacePeer w d pid {peer with txQueue:=peer.txQueue.enqueue items}) [] (by simp)
    (by simp [Packets.epoch,replacePeer,device])
    (QueueHandoff.installed_queues device resident) (congrArg Prod.snd material)
  simp only [List.append_nil] at core
  obtain ⟨coverage,inventory⟩:=QueueHandoff.installed_ownership device resident
    before.entry.coverage before.entry.inventory
  have bounds : Packets.Inv (replacePeer w d pid {peer with txQueue:=peer.txQueue.enqueue items}) := by
    simpa only [Packets.Inv,Packets.snapshot,Packets.deviceStore,replacePeer,device,Option.map_some]
      using before.entry.packets
  exact ⟨⟨core,before.entry.justified,before.entry.allocationLinks,before.entry.noSelected,
    bounds,coverage,inventory⟩,before.complete⟩

/-- Every old disposition access/queue marker is independently birth- and
terminal-quiet; this rule applies to the already derived native cut world. -/
theorem disposition_history (before : Accounted history ledger debts locals w)
    (events : List TxDisposition.Event) :
    Accounted (history++events.map CausalJournal.txEvent) ledger debts locals w := by
  apply before.append_quiet
  · intro event member
    obtain ⟨old,_,rfl⟩:=List.mem_map.mp member
    rfl
  · intro event member
    obtain ⟨old,_,rfl⟩:=List.mem_map.mp member
    intro position
    rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
