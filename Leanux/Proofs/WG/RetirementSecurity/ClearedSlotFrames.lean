import Leanux.Proofs.WG.RetirementSecurity.HolderDrains

/-! Once native removal clears a peer's slots, inline handshake-work drains
do not republish them. Final peer deletion is permitted throughout these
frames; no numeric peer-slot persistence is assumed. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem SlotsCleared.points (before : SlotsCleared pid w)
    (same : ownershipPointView v = ownershipPointView w) : SlotsCleared pid v := by
  intro p found
  change peerAt v pid = some p at found
  have point := congrFun (congrArg (fun s => s.2.2.1) same) pid
  have mapped : (peerAt w pid).map peerOwnership = some (peerOwnership p) := by
    simpa only [ownershipPointView,ownershipAt,found,Option.map_some] using point.symm
  obtain ⟨q,resident,fields⟩ := Option.map_eq_some_iff.mp mapped
  have empty := before q resident
  have slots := congrArg Prod.fst fields
  exact ⟨(congrArg Prod.fst slots).symm.trans empty.1,
    (congrArg (fun s => s.2.1) slots).symm.trans empty.2.1,
    (congrArg (fun s => s.2.2) slots).symm.trans empty.2.2⟩

namespace ClearedSlots

theorem frame {action : WG.M α} (points : SameView ownershipPointView action) :
    Preserves (SlotsCleared pid) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.points ((ProjectedAction.iff_run_ambient _ _ _).mp points w a result v b run)

theorem clear_perimeter (pid : PeerId) :
    SameView (holderPerimeter pid) (keypairsClear pid) := by
  intro initial
  change Preserves (fun w => holderPerimeter pid w = initial) _
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  repeat' first
    | (rx_retention_head getPeer; exact (getPeer_perimeter pid _).wp (· = initial))
    | (rx_retention_head setPeer; exact (setPeer_perimeter pid _).wp (· = initial))
    | (rx_retention_head keypairPut; exact (put_perimeter pid _ _).wp (· = initial))
    | rxstack_preserves_join
    | rx_retention_step

theorem clear (pid selected : PeerId) : Preserves (SlotsCleared selected) (keypairsClear pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  by_cases same : selected = pid
  · subst selected
    exact (hoare_iff_run_ambient _ _ _).mp (clear_slots pid) w a result v b True.intro run
  · have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp (clear_perimeter pid)
      w a result v b run
    have point := congrFun (congrArg Prod.fst perimeter) selected
    have equal : peerAt v selected = peerAt w selected := by
      simpa only [holderPerimeter,peersAt,peerAt,same,ite_false,Option.bind_map,
        Function.comp_def] using point
    intro p found
    exact before p (equal.symm.trans found)

theorem handshake_clear_points (pid : PeerId) :
    SameView ownershipPointView (handshakeClear pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold handshakeClear handshakeZero
  repeat' first
    | (allocation_release_lift_from IndexM; exact (HolderHandshake.index_points _).wp (· = initial))
    | (rx_retention_head liftIndex; exact (HolderHandshake.index_points _).wp (· = initial))
    | ownership_source_step initial

theorem send_worker (pid selected : PeerId) :
    Preserves (SlotsCleared selected) (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact preserves_bind (frame (HolderHandshake.initiation_points pid))
    (fun _ => peerPut_slots selected (some pid))

theorem zero_worker (pid selected : PeerId) :
    Preserves (SlotsCleared selected) (queuedExpiredZeroKeyMaterial pid) := by
  unfold queuedExpiredZeroKeyMaterial
  exact preserves_bind (frame (handshake_clear_points pid)) (fun _ =>
    preserves_bind (clear pid selected) (fun _ => peerPut_slots selected (some pid)))

/-- The native dequeue and saved-peer PENDING update before the send callback. -/
def sendPreparation (pid : PeerId) : WG.M Unit := do
  modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}
  let p ← getPeer pid
  if !p.handshakePending then invariant "queued work without a pending flag"
  setPeer pid {p with handshakePending := (← getDev).sendWorkQueue.contains pid}
  _ ← hidden (.sectionStart .sendWorker)

theorem send_factor (pid : PeerId) : runFlushedSendWork pid = (do
    sendPreparation pid
    handshakeSendWorker pid
    _ ← hidden (.sectionStop .sendWorker)) := by
  simp only [runFlushedSendWork,sendPreparation,bind_assoc,TxDisposition.bind_ite,pure_bind]

theorem send_preparation_points (pid : PeerId) : SameView ownershipPointView (sendPreparation pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold sendPreparation
  repeat' first
    | (rx_retention_head hidden; unfold hidden)
    | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | ownership_source_step initial

theorem flushed_send (pid selected : PeerId) :
    Preserves (SlotsCleared selected) (runFlushedSendWork pid) := by
  rw [send_factor]
  apply preserves_bind (frame (send_preparation_points pid))
  intro _
  apply preserves_bind (send_worker pid selected)
  intro _
  apply preserves_bind (hoare_liftAmbient _ (SlotsCleared selected))
  intro _
  exact preserves_pure ()

theorem flushed_clear (pid selected : PeerId) :
    Preserves (SlotsCleared selected) (runFlushedClearWork pid) := by
  unfold runFlushedClearWork
  apply preserves_bind (frame (ownership_modifyDev
    (fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)))
  intro _
  apply preserves_bind (hoare_liftAmbient _ (SlotsCleared selected))
  intro _
  apply preserves_bind (zero_worker pid selected)
  intro _
  apply preserves_bind (hoare_liftAmbient _ (SlotsCleared selected))
  intro _
  exact preserves_pure ()

theorem drain (upTo : Option PeerId) (selected : PeerId) :
    Preserves (SlotsCleared selected) (drainHandshakeSendWq upTo) :=
  HolderDrain.drain_rule upTo _
    (fun w v _ pid a b before _ _ run =>
      (hoare_iff_run_ambient _ _ _).mp (flushed_send pid selected) w a () v b before run)
    (fun w v _ pid a b before _ _ run =>
      (hoare_iff_run_ambient _ _ _).mp (flushed_clear pid selected) w a () v b before run)

theorem timers_stop (pid selected : PeerId) :
    Preserves (SlotsCleared selected) (timersStop pid) := by
  unfold timersStop
  apply preserves_bind
  · apply list_view_spec id (SlotsCleared selected)
    intro timer u
    exact preserves_bind (frame (delTimer_ownership pid timer)) (fun _ => preserves_pure _)
  · intro _
    apply preserves_bind (frame (ownershipPoints_kernel _ getDev_sameWGStore))
    intro d
    split
    · exact drain _ selected
    · exact preserves_pure ()

end ClearedSlots
end Leanux.Proofs.WG.RetirementSecurity
