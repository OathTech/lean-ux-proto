import Leanux.Proofs.WG.HandshakeSecurity.ResponderPollFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResponderFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Origins Origins.Retaining Lifetimes Queues

theorem native_store {a : WG.M α} (same : SameWGStore a) (confirmed : List Nat) :
    Preserves (History.Native confirmed) a :=
  native_fields
    (same.of_factor (fun store : WGStoreView => pool {dev := store.dev}) pool (fun _ => rfl))
    (same.of_factor (fun store : WGStoreView => CurrentSlots.fields {dev := store.dev}) CurrentSlots.fields (fun _ => rfl)) confirmed

theorem native_skb (a : SkbM α) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (liftSkb a) := by
  apply hoare_liftSkb
  intro w d store entry device
  have currentFrame : current {w with dev := some ({d with txSkbs := store.txSkbs, rxSkbs := store.rxSkbs, nextSkb := store.nextSkb})} = current w := by
    funext pid
    simp [current, device]
  have fieldFrame : CurrentSlots.fields {w with dev := some ({d with txSkbs := store.txSkbs, rxSkbs := store.rxSkbs, nextSkb := store.nextSkb})} = CurrentSlots.fields w := by
    unfold CurrentSlots.fields RxCredits.keyWords
    simp only [device, Option.map_some, Option.bind_some]
  exact ⟨Authorized.frame entry.1 currentFrame, CurrentSlots.fields_transport entry.2 fieldFrame⟩

theorem peek_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (peekRxQueue pid) := by
  apply native_fields
    (pool_of_material ((pinned_const _private.Leanux.Proofs.WG.Origins.RetainingTraffic.«0».Leanux.Proofs.WG.Origins.Retaining.peekRxQueue_material) pid))
  intro initial
  change Preserves (fun w => CurrentSlots.fields w = initial) _
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek
       exact ((prevQueuePeek_sameWGStore _).of_factor
         (fun store : WGStoreView => CurrentSlots.fields {dev := store.dev}) CurrentSlots.fields
         (fun _ => rfl)).wp (fun f => f = initial))
    | slot_fields_step initial

theorem drop_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (dropRxQueue pid) := by
  apply native_fields
    (pool_of_material ((pinned_const _private.Leanux.Proofs.WG.Origins.RetainingTraffic.«0».Leanux.Proofs.WG.Origins.Retaining.dropRxQueue_material) pid))
  intro initial
  change Preserves (fun w => CurrentSlots.fields w = initial) _
  unfold dropRxQueue
  repeat' slot_fields_step initial

theorem complete_native (pid : PeerId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (completeRxQueue pid) := by
  apply native_fields
    (pool_of_material ((pinned_const _private.Leanux.Proofs.WG.Origins.RetainingTraffic.«0».Leanux.Proofs.WG.Origins.Retaining.completeRxQueue_material) pid))
  intro initial
  change Preserves (fun w => CurrentSlots.fields w = initial) _
  unfold completeRxQueue
  repeat' slot_fields_step initial

end Leanux.Proofs.WG.HandshakeSecurity.Responder
