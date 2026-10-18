import Leanux.Proofs.WG.Noise.DriverTagConsumeFrames
import Leanux.Proofs.WG.Noise.DriverTagStackSource
import Leanux.Proofs.WG.Queues.PollPreservation
import Leanux.Proofs.WG.Queues.GroPreservation
import Leanux.Proofs.WG.Queues.NapiSource

/-! Normal tag retention for the original receive poll and its NAPI callers.
The existing stamped observers are proof vehicles only: their histories are
ignored by this invariant, and their unconditional erasure recovers the exact
original result, final state, or Stop. Peer deletion by reference release is
permitted. The actual Stack callback is instantiated without premises. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Poll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Silent

def ProductRetained (entry : TagMap) (w : World) : Prop := Retained entry w.wg

theorem peek_retained (entry : TagMap) (pid : PeerId) :
    Preserves (Retained entry) (peekRxQueue pid) := by
  unfold peekRxQueue
  apply preserves_bind (of_frame entry _ (getPeer_frame pid))
  intro p
  apply preserves_bind (of_frame entry _ (store_frame (prevQueuePeek_sameWGStore p.rxQueue)))
  intro result
  simpa only [bind_assoc] using preserves_bind
    (update entry pid (fun q => {q with rxQueue := result.2}) (fun _ => rfl))
    (fun _ => preserves_pure result.1)

theorem drop_retained (entry : TagMap) (pid : PeerId) :
    Preserves (Retained entry) (dropRxQueue pid) := by
  unfold dropRxQueue
  rw [getPeer_twice]
  exact update entry pid (fun p => {p with rxQueue := p.rxQueue.dropPeeked}) (fun _ => rfl)

theorem complete_retained (entry : TagMap) (pid : PeerId) :
    Preserves (Retained entry) (completeRxQueue pid) :=
  update entry pid (fun p => {p with napiScheduled := false}) (fun _ => rfl)

theorem counter_retained (entry : TagMap) (kid nonce : Nat) :
    Preserves (Retained entry) (counterValidate kid nonce) := by
  unfold counterValidate
  simp (config := {zeta := false}) only [WG.orM,Std.Legacy.Range.forIn_eq_forIn_range']
  material_lower
  repeat' first
    | (rx_retention_head setKeypair; exact of_frame entry _ (setKeypair_frame _ _))
    | silent_native_step entry
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head ForIn.forIn; apply list_view_spec id (Retained entry))
    | material_component
    | material_intro
    | material_reduce
    | material_match
  all_goals change Preserves (Retained entry) _
  all_goals repeat' silent_native_step entry

theorem ready_retained (entry : TagMap) (first : Option SkbId) :
    Preserves (Retained entry)
      (WG.andM (branch .rxPollPacket first.isSome) do
        let some f := first | invariant "unreachable"
        branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)) := by
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head getRxSkb; exact of_frame entry _ (packet_frame (SkbStore.getRx _)))
    | silent_native_step entry

theorem product_store (entry : TagMap) (w v : World)
    (same : productStoreView v = productStoreView w)
    (prior : ProductRetained entry w) : ProductRetained entry v := by
  have tags : tagView v.wg = tagView w.wg :=
    congrArg (fun s : ProductStore43 => responseTagMap s.2.2.2.dev) same
  change TagsRetained entry (tagView v.wg)
  rw [tags]
  exact prior

end Leanux.Proofs.WG.Noise.DriverTags.Poll
