import Leanux.Proofs.WG.RetirementSecurity.ClearedSlotFrames

/-! The actual post-dead removal tail clears publication slots, drains its
workqueue, and finally pays the detached peer occurrence. The key account
retains outstanding RX/TX holders; peer removal does not assert their expiry. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

theorem SlotPeerReferences.drop_cleared
    (before : SlotPeerReferences holders (o :: loans) w) (cleared : SlotsCleared o.slot w) :
    SlotPeerReferences holders loans w := by
  intro d pid p device stored slots
  have member := before d pid p device stored slots
  simp only [List.mem_append,List.mem_cons] at member ⊢
  rcases member with base | same | loan
  · exact Or.inl base
  · have selected : pid = o.slot := congrArg Owner.slot same
    subst pid
    have empty := cleared p (by simp [device,stored])
    rcases slots with next | previous | current
    · exact False.elim (next empty.1)
    · exact False.elim (previous empty.2.1)
    · exact False.elim (current empty.2.2)
  · exact Or.inr loan

namespace HolderRemoval

abbrev preparation := pinned_const _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.beforePayment

theorem decrement : Preserves (HolderDrain.Ready original carriers loans temporary)
    (modifyDev fun d => {d with numPeers := d.numPeers - 1}) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp
      (pinned_const _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.decrement_keeps)
      w a result v b before.1 run,
    before.2.1.points ((ProjectedAction.iff_run_ambient _ _ _).mp
      (ownership_modifyDev (fun d => {d with numPeers := d.numPeers - 1})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) w a result v b run),
    (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.modify
      (fun d => {d with numPeers := d.numPeers - 1}) (fun _ => rfl) (fun _ => rfl))
      w a result v b before.2.2 run⟩

theorem prepare (pid : PeerId) :
    Preserves (HolderDrain.Ready original carriers loans temporary) (preparation pid) := by
  unfold preparation
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.beforePayment
  repeat' first
    | (rx_retention_head getPeer; exact getPeer_preserves _ _)
    | (rx_retention_head getDev
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a d v b before run
       exact (DecryptCarrier.getDev_current a b run).1 ▸ before)
    | (rx_retention_head keypairsClear; exact HolderDrain.keys_clear _)
    | (rx_retention_head timersStop; exact HolderDrain.timers_stop _)
    | (rx_retention_head drainHandshakeSendWq; exact HolderDrain.drain _)
    | (rx_retention_head modifyDev; exact decrement)
    | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
    | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | rxstack_preserves_join
    | rx_retention_step

theorem prepare_clears (pid : PeerId) :
    Hoare (preparation pid) (fun _ => True) (fun _ => SlotsCleared pid) := by
  unfold preparation
  index_unfold _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.beforePayment
  apply hoare_bind _ _ (getPeer_preserves pid (fun _ => True))
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .peerRemoveNotDead (!p.isDead)) (fun _ => True))
  intro notDead
  apply hoare_bind _ _
    (show Preserves (fun _ => True) (if notDead then unsupported _ else pure ()) from by
      split
      · exact hoare_liftAmbient (AmbientM.unsupported _) _
      · exact preserves_pure ())
  intro _
  apply hoare_bind _ _ (clear_slots pid)
  intro _
  change Preserves (SlotsCleared pid) _
  repeat' first
    | (rx_retention_head getDev; exact ClearedSlots.frame (ownershipPoints_kernel _ getDev_sameWGStore))
    | (rx_retention_head timersStop; exact ClearedSlots.timers_stop _ pid)
    | (rx_retention_head drainHandshakeSendWq; exact ClearedSlots.drain _ pid)
    | (rx_retention_head modifyDev; exact ClearedSlots.frame (ownership_modifyDev
        (fun d => {d with numPeers := d.numPeers - 1})
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)))
    | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
    | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | rxstack_preserves_join
    | rx_retention_step

/-- The original removal tail itself establishes final-release readiness by
clearing its slots before either inline drain. The detached peer occurrence
is paid, while exact key credit remains attached to the physical survivors. -/
theorem after_dead (before : HolderDrain.Ready original carriers (o :: loans) temporary w)
    (a b : Ambient)
    (run : ((peerRemoveAfterDead o.slot).run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready original carriers loans temporary v ∧ SlotsCleared o.slot v := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.HolderRetirement.«0».Leanux.Proofs.WG.Queues.RxCredits.DurableHolders.afterDead_factor),
    MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨ignored,u,c,prefixRun,payment⟩ := run
  cases ignored
  have phaseReady := (hoare_iff_run_ambient _ _ _).mp (prepare o.slot) w a () u c before prefixRun
  have empty := (hoare_iff_run_ambient _ _ _).mp (prepare_clears o.slot) w a () u c True.intro prefixRun
  have finalEmpty := (hoare_iff_run_ambient _ _ _).mp (peerPut_slots o.slot (some o.slot))
    u c () v b empty payment
  have releaseReady : PeerReleaseReady o.slot u := fun p found _ => empty p found
  have anchors := (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.peer_put (some o.slot))
    u c () v b phaseReady.2.2 payment
  exact ⟨⟨work_payment_normal phaseReady.1 c b payment,
    phaseReady.2.1.peer_put releaseReady c b payment,anchors.drop_cleared finalEmpty⟩,finalEmpty⟩

end HolderRemoval
end Leanux.Proofs.WG.RetirementSecurity
