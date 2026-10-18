import Leanux.Proofs.WG.RetirementSecurity.RxPollOccurrenceFrames

/-! Full native RX polling preserves exclusive physical TX ownership and
pending encryption aliases, including authenticated staging and GRO stack
callbacks. Allocation freshness is derived independently from campaign 1. -/
namespace Leanux.Proofs.WG.RetirementSecurity.RxPollOccurrences
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open Queues.RxCredits OccurrenceStack

theorem join {observer : MixedM α} {native : WG.M α}
    (erases : ErasesStatePrefix observer native)
    (keeps : StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe observer)
    (occurrences : Preserves (TxOccurrences locals active) native) :
    Preserves (Ready locals active) native := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨Allocated.native erases keeps before.1 a b run,
    (hoare_iff_run_ambient _ _ _).mp occurrences w a result v b before.2 run⟩

theorem store {native : WG.M α} (same : SameWGStore native) :
    Preserves (Ready locals active) native := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ready_store ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run) before

theorem peek (pid : PeerId) : Preserves (Ready locals active) (peekRxQueue pid) :=
  join (RxJoint.peekAccess_erases pid) (RxJoint.peekAccess_allocation pid) (peek_occurrences pid)

theorem drop (pid : PeerId) : Preserves (Ready locals active) (dropRxQueue pid) :=
  join (rxDropPeekedPrefix_erases pid) (rxDropPeekedPrefix_preserves allocationAmbient pid) (drop_occurrences pid)

theorem complete (pid : PeerId) : Preserves (Ready locals active) (completeRxQueue pid) :=
  join (RxJoint.completeAccess_erases pid) (RxJoint.completeAccess_allocation pid) (complete_occurrences pid)

theorem counter (kid : KeypairId) (nonce : Nat) : Preserves (Ready locals active) (counterValidate kid nonce) :=
  join (counterValidatePrefix_erases kid nonce)
    (AmbientContracts.drop (counterValidatePrefix_spec allocationAmbient (fun _ => True) kid nonce))
    (counter_occurrences kid nonce)

theorem free_rx (id : SkbId) : Preserves (Ready locals active) (freeRxSkb id) :=
  join (freeRxSkbPrefix_erases id) (allocationRx.free id)
    (occurrence_passive (ReceiveOccurrences.free_rx_wire id) (ReceiveOccurrences.skb_queues _))

theorem key_put (id : Option KeypairId) (now : Bool) : Preserves (Ready locals active) (keypairPut id now) :=
  join (keypairPutPrefix_erases id now) (keypairPutPrefix_allocation id now)
    (occurrence_passive ((TxRing.keypairPut_frame id now).product (TxDisposition.keyPut_packets id now))
      ((keypairPut_protect id now).factor (fun s => s.2.2.1)))

theorem peer_put (id : Option PeerId) : Preserves (Ready locals active) (peerPut id) :=
  join (peerPutMixed_erases id) (peerPutMixed_allocation id) (ReceiveOccurrences.peer_put id)

theorem consume (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves (Ready locals active) (consumeDataDone pid pkt endpoint) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨Allocated.native (consumeDataDonePrefix_erases pid pkt endpoint)
      (consumeDataDonePrefix_preserves_ambient allocationAmbient allocationTx allocationRx pid pkt endpoint)
      before.1 a b run,
    receive_done_occurrences before.2 before.1.bounded pid pkt endpoint a b run⟩

/-- The original product callback remains arbitrary with its exact head and
allocation-state contract. All poll budgets and normal failure branches remain. -/
theorem poll (pid budget : Nat)
    (callback : List (List UInt8)→Leanux.M Unit)
    (hc : ∀xs,Preserves (fun w:World=>Ready locals active w.wg) (callback xs)) :
    Preserves (fun w:World=>Ready locals active w.wg) (rxPoll pid budget callback) := by
  rw [←rxPollGrouped_eq]
  unfold rxPollGrouped
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,invariant,unsupported,WG.andM]
  repeat' first
    | (rx_retention_head napiGroReceive
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
         _ callback hc _ _)
    | (rx_retention_head napiGroFlushAll
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
         _ callback hc _)
    | (allocation_release_lift_from WG.M
       apply PublicationPoll.native_product (Ready locals active)
       simp only [monadLift_self]
       repeat' first
         | (rx_retention_head peekRxQueue; exact peek _)
         | (rx_retention_head dropRxQueue; exact drop _)
         | (rx_retention_head completeRxQueue; exact complete _)
         | (rx_retention_head counterValidate; exact counter _ _)
         | (rx_retention_head WG.consumeDataDone; exact consume _ _ _)
         | (rx_retention_head getRxSkb; exact ReceiveOccurrences.get_rx _ _)
         | (rx_retention_head freeRxSkb; exact free_rx _)
         | (rx_retention_head WG.peerPut; exact peer_put _)
         | (rx_retention_head keypairPut; exact key_put _ _)
         | (rx_retention_head endpointFromSkb
            exact store (endpointFromSkb_sameWGStore _))
         | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
         | rx_retention_step)
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ hi=>hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w:World=>Ready locals active w.wg)
       intro x b
       change Preserves (fun w:World=>Ready locals active w.wg) _)
    | rx_retention_step

theorem stack (pid budget : Nat) :
    Preserves (fun w:World=>Ready locals active w.wg)
      (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) :=
  poll pid budget _ OccurrenceStack.stackForM_stack

theorem shared {E : Type}
    {ρ : E → Option TransmitSecurity.Nonce.Allocation}
    {hooks : TransmitSecurity.Driver.Hooks E}
    (projects : TransmitSecurity.Driver.HooksProjects ρ hooks TransmitSecurity.Driver.nonceHooks)
    (before : Ready locals active w.wg) (pid : PeerId) (budget : Nat) (h : List E)
    (run : (runPrefix (TransmitSecurity.Driver.nativePollObserved hooks pid budget) w h).1 = .ok (result,v)) :
    Ready locals active v.wg := by
  have projected := TransmitSecurity.Driver.nativePoll_projects projects pid budget
  rw [TransmitSecurity.Driver.nonce_nativePollObserved_eq] at projected
  exact (hoare_iff_run _ _ _).mp (stack pid budget) w result v before
    (DriverOwnership.product_native projected
      (TransmitSecurity.Nonce.nativePollObserved_erases pid budget) w v h run)

end Leanux.Proofs.WG.RetirementSecurity.RxPollOccurrences
