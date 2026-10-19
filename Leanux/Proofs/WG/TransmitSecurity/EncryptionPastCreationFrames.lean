import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastAdmission

/-! Creation transports the historical exclusion through the original queue
choice and every actual refusal/cleanup arm. The bounded batch and physical
ring facts are the existing allocation discipline, not success assumptions. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity TxDisposition
set_option maxHeartbeats 600000
set_option pp.structureInstances false

def CreationReady (past : List (Option Nat × SkbId)) (active : List (List SkbId))
    (items : List SkbId) (w : WGWorld) : Prop :=
  LiveFrontier.Safe items w ∧ Inv past active (view w) ∧ Admissible past items (view w)

theorem creation_frame {action : WG.M α}
    (live : Preserves (LiveFrontier.Safe items) action) (same : SameView view action) :
    Preserves (CreationReady past active items) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have eq := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp live w a result v b before.1 run,
    eq ▸ before.2⟩

theorem enqueue_ready (pid : PeerId) (items : List SkbId) :
    Preserves (CreationReady past active items) (enqueuePerDeviceAndPeer pid items) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp (LiveFrontier.enqueue_safe pid items)
    w a result v b before.1 run,
    enqueue pid items before.1.1.2 before.2.1 before.2.2 a b run⟩

theorem publish_ready (items : List SkbId) (state : PacketState) :
    Preserves (CreationReady past active items) (enqueuePerPeerTx items state) := by
  apply creation_frame ?_ (publish items state)
  unfold enqueuePerPeerTx cpumaskChooseOnline
  simp only [Nat.mod_one,Std.Legacy.Range.forIn_eq_forIn_range',
    branch,invariant,peekQueuedUnit,recordQueued]
  repeat' live_safe_step items

theorem free_ready (items : List SkbId) (id : SkbId) :
    Preserves (CreationReady past active items) (freeTxSkb id) := by
  apply creation_frame ?_ (free_packet id)
  apply LiveFrontier.frame items
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact (freeTxSkb_retention id w v a b run).metadata
  · intro initial
    apply hoare_liftSkb
    intro w d entries before device
    simpa only [TxRing.nativeCell,device,Option.map_some] using before

macro "encryption_creation_step " items:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact getPeer_preserves _ _)
  | (rx_retention_head getTxSkb
     apply creation_frame ?_ (read_packet _)
     repeat' live_safe_step $items)
  | (rx_retention_head peerPut
     exact creation_frame (LiveFrontier.frame $items (peerPut_metadata _) (TxRing.peerPut_frame _)) (peer_put _))
  | (rx_retention_head keypairPut
     exact creation_frame (LiveFrontier.frame $items ((keypairPut_rest _ _).factor (fun s => s.2.2))
       (TxRing.keypairPut_frame _ _)) (key_put _ _))
  | (rx_retention_head freeTxSkb; exact free_ready $items _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id (CreationReady _ _ $items)
     intro x b
     change Preserves (CreationReady _ _ $items) _)
  | rx_retention_step)

theorem acquire_view (kid : KeypairId) : SameView view (Affiliation.sendAcquire kid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold Affiliation.sendAcquire
  repeat' encryption_past_passive initial

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
