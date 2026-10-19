import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueFrontier

/-! Native packet allocation bounds at queue-admission source cuts. Marking
a cell or installing an owning peer queue never allocates another packet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queue
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AllocatedObligation QueueHandoff

theorem store_bounds {action : WG.M α} (frame : SameWGStore action) : Preserves Packets.Inv action :=
  (frame.of_factor (fun s => Packets.snapshot {dev := s.dev}) Packets.snapshot (fun _ => rfl)).wp Bounded

theorem modify_bounds (f : Device → Device)
    (next : ∀ d, (f d).nextSkb = d.nextSkb)
    (tx : ∀ d, (f d).txSkbs = d.txSkbs) (rx : ∀ d, (f d).rxSkbs = d.rxSkbs) :
    Preserves Packets.Inv (modifyDev f) := by
  apply hoare_modify
  intro w before
  cases device : w.dev <;>
    simpa only [Packets.Inv,Packets.snapshot,Packets.deviceStore,device,
      Option.map_none,Option.map_some,next,tx,rx] using before

theorem mark_bounds (skb : SkbId) (f : DataPacket → DataPacket) :
    Preserves Packets.Inv (setTxSkb skb f) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  exact ((Action.iff_run_ambient _ _ _).mp (Packets.setTxSkb_contract skb f) w a value v b before run).1

theorem before_bounds (pid : PeerId) (items : List SkbId) :
    Preserves Packets.Inv (beforeNative pid items) := by
  have read : Preserves Packets.Inv (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b before run
    simpa only [(Peers.getPeer_current pid w v p a b run).1] using before
  unfold beforeNative
  repeat' first
    | (allocation_release_head setTxSkb; exact mark_bounds _ _)
    | (allocation_release_head getPeer; exact read)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (allocation_release_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | allocation_release_step

theorem install_bounds (pid : PeerId) (p : Peer) (items : List SkbId) :
    Preserves Packets.Inv (setPeer pid {p with txQueue := p.txQueue.enqueue items}) :=
  modify_bounds _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem after_bounds (items : List SkbId) : Preserves Packets.Inv (RxCredits.enqueueTailItem items) := by
  unfold RxCredits.enqueueTailItem
  repeat' first
    | (allocation_release_head getDev; exact store_bounds getDev_sameWGStore)
    | (allocation_release_head cpumaskNextOnlineFrom; exact store_bounds (cpumaskNextOnlineFrom_sameStore _))
    | (allocation_release_head modifyDev; exact modify_bounds _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    | (allocation_release_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (allocation_release_head queueDeviceWork; exact hoare_liftAmbient (AmbientM.queueDeviceWork _) _)
    | allocation_release_step

/-- Bounds at a focused native component use its actual erasure and successful
native result. This helper adds no stopped-state or ownership assumption. -/
theorem focused_bounds {action : TxDisposition.Obs α} {source : WG.M α}
    (erases : ErasesPrefix action (liftWG source)) (keeps : Preserves Packets.Inv source)
    (before : Packets.Inv w.wg)
    (performed : runPrefix (focused action) w history = (.ok (value,v),last)) : Packets.Inv v.wg := by
  have full := (focusPrefix_erases _ _ erases w history).symm.trans (congrArg Prod.fst performed)
  rw [liftWG_run] at full
  cases native : (source.run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,a⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    exact (hoare_iff_run_ambient _ _ _).mp keeps w.wg w.ambient result g a before native

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Queue
