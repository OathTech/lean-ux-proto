import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionPeerFrames

/-! The shared staging-selection callback carries pending tickets through
its actual read, queue clear and current-key borrow. This callback observes
current selection but cannot manufacture or consume a pending ticket. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Origins

theorem modify_slot_fields (pid : PeerId) (f : Peer → Peer)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p) :
    SameView CurrentSlots.fields (do let p ← getPeer pid; setPeer pid (f p)) := by
  intro initial
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotFrames.«0».Leanux.Proofs.WG.CurrentSlots.fields_read) initial pid
  intro p saved
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotFrames.«0».Leanux.Proofs.WG.CurrentSlots.fields_set) initial pid (f p)
  simpa only [slots] using saved

theorem Carrier.modify_peer (confirmed : List Nat) (pid : PeerId) (f : Peer → Peer)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
    Preserves (Carrier confirmed) (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply Carrier.join confirmed
  · exact ConfiguredRemoval.frame (ConfiguredIdentity.modifyPeer_view pid f configured)
  · exact CurrentSlots.fields_preserves (modify_slot_fields pid f slots)
  · apply frame_preserves (PendingPromotion.modify_peer pid f ?_) confirmed
    intro p
    exact congrArg (fun cells => cells.2.2) (slots p)

theorem Carrier.write_saved (confirmed : List Nat) (pid : PeerId) (p : Peer) (f : Peer → Peer)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p) :
    Hoare (setPeer pid (f p))
      (fun w => Carrier confirmed w ∧ Responder.SavedNativePeer pid p w)
      (fun _ => Carrier confirmed) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  obtain ⟨d,device,resident⟩ := hi.2
  have getter : ((getPeer pid).run w).run a = .ok ((p,w),a) := by
    simp [getPeer,getDev,device,resident]
  have whole : (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run w).run a =
      .ok ((value,v),b) := by
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨p,w,a,getter,run⟩
  exact (hoare_iff_run_ambient _ _ _).mp
    (Carrier.modify_peer confirmed pid f slots configured) _ _ _ _ _ hi.1 whole

theorem Carrier.selection (confirmed : List Nat) (pid : PeerId) :
    Preserves (Carrier confirmed) (Responder.selectionPrefix pid) := by
  unfold Responder.selectionPrefix
  apply hoare_bind _ _ (Carrier.get_peer confirmed pid)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) _)
  intro empty
  cases empty with
  | true =>
    exact hoare_consequence (preserves_pure none)
      (fun _ hi => hi.1) (fun _ _ hi => hi)
  | false =>
    apply hoare_bind _ _ (Carrier.write_saved confirmed pid p (fun p => {p with staged := []})
      (fun _ => rfl) (fun _ => rfl))
    intro _
    exact preserves_bind (Carrier.key_get confirmed p.keypairCurrent)
      (fun key => preserves_pure (some (p,key)))

theorem selection_observed (pid : PeerId) : Observed (Responder.DriverCuts.selection pid) := by
  apply receipt _ (.selected pid)
  intro confirmed r valid hi
  simpa only [Responder.DriverCuts.Event.labels,List.append_nil] using
    (hoare_iff_run_ambient _ _ _).mp (Carrier.selection confirmed pid) _ _ _ _ _ hi valid

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
