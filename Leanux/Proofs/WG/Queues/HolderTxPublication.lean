import Leanux.Proofs.WG.Queues.HolderDecrypt
import Leanux.Proofs.WG.Queues.PassiveHolders

/-! Native TX publication keeps every existing durable holder and RX carrier.
Its temporary reference is acquired and repaid by the actual source; the
existing concrete protection theorem already accounts for that exchange. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

/-- Source publication preserves the lasting holder fields. The txWorkQueue
notification is an alias, not an additional batch/reference reservation. -/
theorem enqueuePerPeerTx_frame (item : List SkbId) (state : PacketState) (initial) :
    Preserves (Frame initial) (enqueuePerPeerTx item state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp
    (publication_protect item state) w a result v b run
  have passive := (hoare_iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.PassiveHolders.«0».Leanux.Proofs.WG.Queues.RxCredits.PassiveHolders.enqueuePeer_preserves)
      item state (passiveView w)) w a result v b rfl run
  have tx : handoffTxView v = handoffTxView w := congrArg (fun s => s.2.2.1) fields
  have send := congrArg (fun s => s.2.2.2) fields
  exact hi.trans ⟨passive,send,fun pid batches found => by rw [tx] at found; exact found⟩

/-- The source-acquired publication reference is repaid before this normal
endpoint. No externally supplied publication owner or extra loan is required. -/
theorem enqueuePerPeerTx_carrier (item : List SkbId) (state : PacketState)
    (hi : CarrierState cs loans w) (a b : Ambient)
    (run : ((enqueuePerPeerTx item state).run w).run a = .ok (((),v),b)) :
    CarrierState cs loans v := by
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp
    (publication_protect item state) w a () v b run
  have peer := congrArg Prod.fst fields
  have rx := congrArg (fun s => s.2.1) fields
  have keys := (KeyEffects.iff_run_ambient _ _).mp
    (publication_keyEffect (allowed := NoPromotion) item state) w a () v b run
  exact ⟨inventory_view hi.inventory rx,queueOwners_view hi.queues peer,
    protected_view hi.funded peer,keys.rxCompatible rx hi.keys.1,
    keys.currentsCompatible hi.keys.2 (fun _ _ h => h.elim)⟩

theorem enqueuePerPeerTx_stable (item : List SkbId) (state : PacketState)
    (hi : StableRx cs w) (a b : Ambient)
    (run : ((enqueuePerPeerTx item state).run w).run a = .ok (((),v),b)) :
    StableRx cs v := by
  apply hi.retains
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (RxRing.enqueuePerPeerTx_cell item state) w a () v b run
  · have fields := (ProjectedAction.iff_run_ambient _ _ _).mp
      (publication_protect item state) w a () v b run
    exact congrArg (fun s => s.2.1) fields
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (enqueuePerPeerTx_rxQueues item state) w a () v b run
  · exact (hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.NapiFrames.«0».Leanux.Proofs.WG.Queues.NapiFrames.enqueuePeer_preserves)
        item state (NapiFrames.napiView w)) w a () v b (NapiFrames.refl w) run

/-- Publication retains the same complete funded account, on every actual
normal return. Empty/missing items and source guards retain their Stops. -/
theorem enqueuePerPeerTx_funded (item : List SkbId) (state : PacketState)
    {holders : DurableHolders} (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (a b : Ambient)
    (run : ((enqueuePerPeerTx item state).run w).run a = .ok (((),v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v := by
  have frame := (hoare_iff_run_ambient _ _ _).mp
    (enqueuePerPeerTx_frame item state w) w a () v b (Frame.refl w) run
  exact ⟨⟨hi.aligned.frame frame,enqueuePerPeerTx_carrier item state hi.carriers a b run⟩,
    enqueuePerPeerTx_stable item state stable a b run⟩

theorem enqueuePerPeerTx_boundary (item : List SkbId) (state : PacketState) :
    Preserves (Boundary cs loans) (enqueuePerPeerTx item state) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  obtain ⟨holders,funded,stable⟩ := hi
  exact ⟨holders,enqueuePerPeerTx_funded item state funded stable a b run⟩

/-- The original lifetime observer reaches the same normal native state,
without constraining its incoming journal. -/
theorem enqueuePerPeerTx_observed (item : List SkbId) (state : PacketState)
    {holders : DurableHolders} (hi : holders.Funded cs loans w) (stable : StableRx cs w)
    (history : List LifetimeEvent) (a b : Ambient)
    (run : (runStatePrefix (enqueuePerPeerTxPrefix item state) w a history).1 = .ok (((),v),b)) :
    holders.Funded cs loans v ∧ StableRx cs v :=
  enqueuePerPeerTx_funded item state hi stable a b
    ((enqueuePerPeerTxPrefix_erases item state w a history).symm.trans run)

end Leanux.Proofs.WG.Queues.RxCredits.DurableHolders
