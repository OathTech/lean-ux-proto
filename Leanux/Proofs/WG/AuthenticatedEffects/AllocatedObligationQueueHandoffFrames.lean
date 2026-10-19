import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueHandoffSource

/-! Native queue ownership and allocation material are separate projections.
Only the actual queue installation consumes the caller's unpublished local. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open RetirementSecurity
set_option pp.structureInstances false

theorem install_erases (pid : PeerId) (p : Peer) (items : List SkbId) :
    ErasesPrefix (install pid p items)
      (liftWG (setPeer pid {p with txQueue := p.txQueue.enqueue items})) := by
  intro w h
  rw [install,runPrefix_bind]
  have same := TxDisposition.nativeAccess_erases
    (setPeerMixed_erases pid {p with txQueue := p.txQueue.enqueue items}) w h
  cases performed : runPrefix (TxDisposition.nativeAccess
    (setPeerMixed pid {p with txQueue := p.txQueue.enqueue items})) w h with
  | mk result hist =>
    cases result with
    | error stop => simpa only [performed] using same
    | ok out =>
      obtain ⟨⟨⟩,v⟩ := out
      simpa only [performed,runPrefix_emit] using same

theorem install_appends (pid : PeerId) (p : Peer) (items : List SkbId) :
    Appends (install pid p items) :=
  Appends.bind (Appends.focus _ _ _) (fun _ _ _ => ⟨[_],rfl⟩)

theorem after_erases (items : List SkbId) :
    ErasesPrefix (after items) (liftWG (RxCredits.enqueueTailItem items)) := by
  unfold after RxCredits.enqueueTailItem
  simp only [liftWG_bind,liftWG_pure,apply_ite]
  repeat' first
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_bind
    | apply erasesPrefix_ite
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only

theorem after_appends (items : List SkbId) : Appends (after items) := by
  unfold after
  repeat' first
    | exact Appends.lift _
    | exact Appends.pure _
    | apply Appends.bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem installed_ownership
    (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (coverage : TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w)
    (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w) :
    TxCoverage locals (replacePeer w d pid {p with txQueue := p.txQueue.enqueue items}) ∧
    TxInventory locals (replacePeer w d pid {p with txQueue := p.txQueue.enqueue items}) :=
  ⟨coverage.enqueue device found,inventory.enqueue device found⟩

theorem installed_material (device : w.dev = some d) :
    PacketOrigins.snapshot (replacePeer w d pid p) = PacketOrigins.snapshot w := by
  apply Prod.ext
  · simp only [PacketOrigins.snapshot,PacketOrigins.epoch,replacePeer,device,Option.map_some]
  · funext id
    simp only [PacketOrigins.snapshot,PacketMaterial.view,TxDisposition.txPackets,
      replacePeer,device,Option.bind_some]

theorem after_ownership (items : List SkbId)
    (coverage : TxCoverage locals w.wg) (inventory : TxInventory locals w.wg)
    (performed : runPrefix (after items) w history = (.ok (ret,v),last)) :
    TxCoverage locals v.wg ∧ TxInventory locals v.wg := by
  have full := (after_erases items w history).symm.trans (congrArg Prod.fst performed)
  rw [liftWG_run] at full
  cases native : ((RxCredits.enqueueTailItem items).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (enqueue_tail_ownership items) w.wg w.ambient _ g ambient native
    exact ⟨coverage.points same,inventory.points same⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
