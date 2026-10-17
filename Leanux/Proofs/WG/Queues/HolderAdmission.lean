import Leanux.Proofs.WG.Queues.HolderDecryptHistory

/-! Admission mutates receive queues and reference counts while retaining all
durable holder fields. Its accepted/rejected ledger comes from the actual
admission and enqueue cuts already established for consumeData. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderAdmission
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private theorem keypairGet_frame (kid : Option KeypairId) (initial) :
    Preserves (Frame initial) (keypairGet kid) := by
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' holder_prepare_step initial

private theorem peerMaybe_frame (pid : Option PeerId) (initial) :
    Preserves (Frame initial) (peerGetMaybeZero pid) := by
  unfold peerGetMaybeZero refcountIncNotZero
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,invariant,unsupported]
  repeat' holder_prepare_step initial

private theorem ownerStore_frame (owner : IndexOwner) (word : Option PeerId) (initial) :
    Preserves (Frame initial) (owner.setPeerWord word) := by
  cases owner <;> unfold IndexOwner.setPeerWord <;> repeat' holder_prepare_step initial

private theorem acquire_frame (owner : IndexOwner) (initial) :
    Preserves (Frame initial) (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  repeat' first
    | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ _)
    | (rx_retention_head peerGetMaybeZero; exact peerMaybe_frame _ initial)
    | (rx_retention_head IndexOwner.setPeerWord; exact ownerStore_frame _ _ initial)
    | holder_prepare_step initial

theorem index_frame (kinds : List IndexKind) (index : Nat) (initial) :
    Preserves (Frame initial) (indexLookup kinds index) := by
  rw [←Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  repeat' first
    | (rx_retention_head liftIndex
       apply hoare_liftIndex
       intro w d table hi hd
       exact hi.trans (by constructor <;> first | (simp [passiveView,sendView,hd]) |
         (intro q xs h; simpa [handoffTxView,hd] using h)))
    | (rx_retention_head Affiliation.acquireOwner; exact acquire_frame _ initial)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Frame initial)
       intro x b
       change Preserves (Frame initial) _)
    | holder_prepare_step initial

macro "holder_admission_step " initial:term : tactic => `(tactic| first
  | (rx_retention_head indexLookup; exact index_frame _ _ $initial)
  | (rx_retention_head peerGet; exact HolderDecrypt.peerGet_frame _ $initial)
  | (rx_retention_head peerPut; exact HolderWorkFrames.peerPut_frame _ $initial)
  | (rx_retention_head keypairGet; exact keypairGet_frame _ $initial)
  | (rx_retention_head keypairPut; exact HolderWorkFrames.keypairPut_frame _ _ $initial)
  | (rx_retention_head keypairGetNull; unfold keypairGetNull)
  | (rx_retention_head cpumaskNextOnlineFrom; unfold cpumaskNextOnlineFrom)
  | (rx_retention_head queueDeviceWork; unfold queueDeviceWork)
  | (rx_retention_head newRxSkb; unfold newRxSkb)
  | (rx_retention_head freeRxSkb; unfold freeRxSkb)
  | holder_prepare_step $initial)

theorem admit_frame (msg : List UInt8) (src : SkbSource) (ds : Nat) (initial) :
    Preserves (Frame initial) (RxOrigin.admitSource msg src ds) := by
  unfold RxOrigin.admitSource RxOrigin.admitWith
  material_lower
  repeat' holder_admission_step initial
  all_goals
    change Preserves (Frame initial) keypairGetNull
    unfold keypairGetNull
    repeat' holder_admission_step initial

theorem enqueue_frame (id : SkbId) (initial) :
    Preserves (Frame initial) (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRx
  repeat' holder_admission_step initial

theorem publication_frame (id : SkbId) (state : PacketState) (initial) :
    Preserves (Frame initial) (enqueuePerPeerRx (pure ()) id state : WG.M Unit) := by
  rw [publication_factor]
  unfold publicationMiddle
  repeat' holder_admission_step initial

theorem consume_frame (msg : List UInt8) (src : SkbSource) (ds : Nat) (initial) :
    Preserves (Frame initial) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact enqueue_frame _ initial)
    | (rx_retention_head enqueuePerPeerRx; exact publication_frame _ _ initial)
    | holder_admission_step initial

/-- The existing exact admission/enqueue receipt retains the same complete
holder account. No new funding is inferred from reference-count surplus. -/
theorem consume_funded {holders : DurableHolders}
    (hi : holders.Funded cs loans w) (stable : StableRx cs w) (fresh : Packets.Inv w)
    (physical : NativeRxInv epoch (PtrRing.init n) history w) (a b : Ambient)
    (run : ((consumeData msg src ds).run w).run a = .ok (((),v),b)) :
    holders.Aligned v ∧
      ∃ receipt, StableConsumption cs (holders.owners ++ loans) msg src ds w v a b receipt := by
  have frame := (hoare_iff_run_ambient _ _ _).mp (consume_frame msg src ds w)
    w a () v b (Frame.refl w) run
  exact ⟨hi.aligned.frame frame,consume_stable hi.carriers fresh stable physical a b run⟩

end Leanux.Proofs.WG.Queues.RxCredits.HolderAdmission
