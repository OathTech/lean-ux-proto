import Leanux.Proofs.WG.RetirementSecurity.HolderDrainSource

/-! The actual bounded drain carries both ledgers. Peer work occurrences fund
their own payments; the independent slot anchors protect the key account from
final peer erasure. Key-reference counts are never inferred from peer credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderDrain
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders WorkReservations

def Ready (original : DurableHolders) (carriers : Ledger) (loans : Reservations)
    (temporary : Credits.Ledger) (w : WGWorld) : Prop :=
  DuringWork original carriers loans w ∧ HolderAccount temporary w ∧
    SlotPeerReferences original loans w

theorem initial (keys : HolderAccount temporary w)
    (peers : holders.Funded carriers loans w) (stable : StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) :
    Ready holders carriers loans temporary w :=
  ⟨duringWork_initial peers stable,keys,anchors⟩

theorem selected_send (before : Ready original carriers loans temporary w)
    (device : w.dev = some d) (member : pid ∈ d.sendWorkQueue) (a b : Ambient)
    (run : ((runFlushedSendWork pid).run w).run a = .ok (((),v),b)) :
    Ready original carriers loans temporary v := by
  obtain ⟨holders,remainder,funded,stable⟩ := before.1
  obtain ⟨o,rest,selected⟩ := select_exists holders.send pid ((funded.aligned.send d device) ▸ member)
  have anchors : SlotPeerReferences holders loans w := before.2.2.rename (by rw [remainder.base])
  exact ⟨(pinned_const _private.Leanux.Proofs.WG.Queues.HolderDrains.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.send_selected)
      before.1 device member a b run,
    before.2.1.flushed_send selected funded stable anchors a b run,
    (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.flushed_send pid) w a () v b before.2.2 run⟩

theorem selected_clear (before : Ready original carriers loans temporary w)
    (device : w.dev = some d) (member : pid ∈ d.clearWorkQueue) (a b : Ambient)
    (run : ((runFlushedClearWork pid).run w).run a = .ok (((),v),b)) :
    Ready original carriers loans temporary v :=
  ⟨(pinned_const _private.Leanux.Proofs.WG.Queues.HolderDrains.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.clear_selected)
      before.1 device member a b run,
    (hoare_iff_run_ambient _ _ _).mp (flushed_holders pid temporary) w a () v b before.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.flushed_clear pid) w a () v b before.2.2 run⟩

theorem drain (upTo : Option PeerId) :
    Preserves (Ready original carriers loans temporary) (drainHandshakeSendWq upTo) :=
  drain_rule upTo _
    (fun _ _ _ _ a b before device member run => selected_send before device member a b run)
    (fun _ _ _ _ a b before device member run => selected_clear before device member a b run)

theorem del_timer (pid : PeerId) (timer : PeerTimer) :
    Preserves (Ready original carriers loans temporary) (delTimer pid timer) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (DurableHolders.delTimer_preserves pid timer)
      w a result v b before.1 run,
    before.2.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp
      (delTimer_ownership pid timer) w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.del_timer pid timer)
      w a result v b before.2.2 run⟩

theorem keys_clear (pid : PeerId) :
    Preserves (Ready original carriers loans temporary) (keypairsClear pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (DurableHolders.keypairsClear_preserves pid)
      w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp (clear_holders pid temporary) w a result v b before.2.1 run,
    (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.clear pid) w a result v b before.2.2 run⟩

theorem timers_stop (pid : PeerId) :
    Preserves (Ready original carriers loans temporary) (timersStop pid) := by
  unfold timersStop
  apply preserves_bind
  · apply list_view_spec id (Ready original carriers loans temporary)
    intro timer u
    exact preserves_bind (del_timer pid timer) (fun _ => preserves_pure _)
  · intro _
    apply preserves_bind (show Preserves (Ready original carriers loans temporary) getDev from by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a d v b before run
      exact (DecryptCarrier.getDev_current a b run).1 ▸ before)
    intro d
    split
    · exact drain _
    · exact preserves_pure ()

end Leanux.Proofs.WG.RetirementSecurity.HolderDrain
