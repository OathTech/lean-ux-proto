import Leanux.Proofs.WG.Queues.CurrentSlotCompletion
import Leanux.Proofs.WG.Origins.OwnerPoll

/-! Three-slot compatibility through the actual native poll leaves and the
original product poll, retaining arbitrary callback actions and normal/Stop
behavior. No configured or full-affiliation premise is needed here. -/
namespace Leanux.Proofs.WG.CurrentSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

theorem store_preserves {α : Type} {action : WG.M α} (same : SameWGStore action) :
    Preserves Inv action := fields_preserves (project := id)
      (same.of_factor (fun s : WGStoreView => fields {dev:=s.dev}) fields (fun _ => rfl))

theorem product_store_preserves {α : Type} {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World => Inv w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  have dev : v.wg.dev = w.wg.dev := congrArg (fun s : ProductStore43 => s.2.2.2.dev)
    ((ProjectedAction.iff_run _ _ _).mp same w x v run)
  apply fields_transport hi
  unfold fields Queues.RxCredits.keyWords
  rw [dev]

theorem peekRxQueue_preserves (pid : PeerId) : Preserves Inv (peekRxQueue pid) := by
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact store_preserves (prevQueuePeek_sameWGStore _))
    | slot_traffic_step

theorem dropRxQueue_preserves (pid : PeerId) : Preserves Inv (dropRxQueue pid) := by
  apply fields_preserves (project := id)
  intro initial
  change Preserves (fun w => fields w = initial) _
  unfold dropRxQueue
  repeat' slot_fields_step initial

theorem completeRxQueue_preserves (pid : PeerId) : Preserves Inv (completeRxQueue pid) := by
  unfold completeRxQueue
  repeat' slot_traffic_step

private theorem counter_fields (kp : KeypairId) (nonce : Nat) : SameView fields (counterValidate kp nonce) := by
  intro initial
  let P := fun g => fields g = initial
  have getter : Hoare (getKeypair kp) P (fun k g => P g ∧ RxCredits.keyWords g kp = some k.peer) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient k v ambient' hi hr
    obtain ⟨hv,_,d,hd,hk⟩ := KeyTimes.getKeypair_return kp w v k ambient ambient' hr
    subst v
    exact ⟨hi,by simp [RxCredits.keyWords,hd,hk]⟩
  unfold counterValidate
  apply hoare_bind _ _ getter
  intro k
  let Q := fun g => P g ∧ RxCredits.keyWords g kp = some k.peer
  have setter (counter : ReplayCounter) : Preserves Q (setKeypair kp {k with receivingCounter := counter}) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hi hr
    cases hd : w.dev with
    | none => simp [Q,RxCredits.keyWords,hd] at hi
    | some d =>
      cases hr
      have keys : RxCredits.keyWords {w with dev := some {d with keypairs := d.keypairs.insert kp {k with receivingCounter := counter}}} = RxCredits.keyWords w := by
        funext q
        by_cases h : kp = q
        · subst q
          simpa [RxCredits.keyWords,hd] using hi.2.symm
        · simp [RxCredits.keyWords,hd,Std.TreeMap.getElem?_insert,h]
      have cv : fields {w with dev := some {d with keypairs := d.keypairs.insert kp {k with receivingCounter := counter}}} = fields w := by
        unfold fields
        simp only [hd,Option.map_some,Option.bind_some,keys]
      constructor
      · simpa only [P,hd,Option.map_some] using cv.trans hi.1
      · simpa only [hd,Option.map_some,keys] using hi.2
  apply hoare_consequence (P := Q) (Q := fun _ => Q) ?_ (fun _ h => h) (fun _ _ h => h.1)
  simp (config := {zeta := false}) only [WG.orM,Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head setKeypair; exact setter _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id Q)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match


theorem counterValidate_preserves (kid : KeypairId) (nonce : Nat) :
    Preserves Inv (counterValidate kid nonce) :=
  fields_preserves (project := id) (counter_fields kid nonce)

macro "slot_poll_native" : tactic => `(tactic| first
  | (rx_retention_head peekRxQueue; exact peekRxQueue_preserves _)
  | (rx_retention_head dropRxQueue; exact dropRxQueue_preserves _)
  | (rx_retention_head completeRxQueue; exact completeRxQueue_preserves _)
  | (rx_retention_head counterValidate; exact counterValidate_preserves _ _)
  | (rx_retention_head consumeDataDone; exact consumeDataDone_preserves _ _ _)
  | (rx_retention_head endpointFromSkb; exact store_preserves (endpointFromSkb_sameWGStore _))
  | (rx_retention_head getRxSkb; unfold getRxSkb)
  | (rx_retention_head freeRxSkb; unfold freeRxSkb)
  | slot_packet_step
  | slot_traffic_step)

/-- The original arbitrary product Stack callback supplies only its actual
slot-invariant preservation contract. The exact source poll keeps all budgets,
second getters, key/peer payments and ordinary failure results. -/
theorem poll_preserves (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, Preserves (fun w : World => Inv w.wg) (callback xs)) :
    Preserves (fun w : World => Inv w.wg) (rxPoll pid budget callback) := by
  rw [← rxPollGrouped_eq]
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
       apply PublicationPoll.native_product Inv
       simp only [monadLift_self]
       repeat' slot_poll_native)
    | (allocation_release_lift_from AmbientM
       exact productAmbient_spec _ _ (fun _ _ hi => hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => Inv w.wg)
       intro x b
       change Preserves (fun w : World => Inv w.wg) _)
    | rx_retention_step

end Leanux.Proofs.WG.CurrentSlots
