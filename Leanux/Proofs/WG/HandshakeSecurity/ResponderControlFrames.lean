import Leanux.Proofs.WG.HandshakeSecurity.ResponderHandshakeFrames
import Leanux.Proofs.WG.Queues.HandshakeReceiveSlots

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Queues.RxCredits Origins Origins.Retaining

abbrev SendState := (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State)
abbrev sendView := (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view)

def sendCurrent (s : Option SendState) (pid : PeerId) : Option KeyCore := do
  let d ← s
  let p ← (pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State.peers) d pid
  let kid ← p.2.2.2.2
  ((pinned_const _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.State.keys) d kid).map keyCore

theorem sendCurrent_factor (w : WGWorld) : sendCurrent (sendView w) = current w := by
  funext pid
  unfold sendCurrent current sendView
  index_unfold _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.view
  index_unfold _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.state
  index_unfold _private.Leanux.Proofs.WG.Queues.SendWork.«0».Leanux.Proofs.WG.Queues.RxCredits.SendWork.cell
  cases w.dev with
  | none => rfl
  | some d =>
    change ((d.peers[pid]?).map (fun p => (p.internalId, p.refcount, p.rxQueue, p.napiScheduled, p.keypairCurrent))).bind (fun p => p.2.2.2.2.bind (fun kid => (d.keypairs[kid]?).map keyCore)) = (d.peers[pid]?).bind (fun p => p.keypairCurrent.bind (fun kid => (d.keypairs[kid]?).map keyCore))
    simp only [Option.bind_map, Function.comp_def]

theorem sendView_authorized {a : WG.M α} (frame : SameView sendView a)
    (confirmed : List Nat) : Preserves (Authorized confirmed) a := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w amb result v b entry run
  apply entry.frame
  rw [← sendCurrent_factor v, ← sendCurrent_factor w]
  rw [(ProjectedAction.iff_run_ambient _ _ _).mp frame w amb result v b run]

theorem cookie_native {a : WG.M α} (frame : SameCookie a) (confirmed : List Nat) :
    Preserves (History.Native confirmed) a := by
  apply native_fields
  · apply frame.of_factor (fun s : WGOwnedView => pool {dev := s.dev})
    intro w
    funext kid
    simp [pool, cookieView, cookieDevice, wgOwnedView, wgStoreView, Option.bind_map, Function.comp_def]
  · apply frame.of_factor (fun s : WGOwnedView => CurrentSlots.fields {dev := s.dev})
    intro w
    unfold CurrentSlots.fields RxCredits.keyWords
    simp only [cookieView, cookieDevice, wgOwnedView, wgStoreView,
      Option.map_map, Option.bind_map, Function.comp_def]

theorem cookie_authorized {a : WG.M α} (frame : SameCookie a) (confirmed : List Nat) :
    Preserves (Authorized confirmed) a := by
  have same : SameView current a := by
    apply frame.of_factor (fun s : WGOwnedView => current {dev := s.dev})
    intro w
    funext pid
    unfold current
    simp only [cookieView, wgOwnedView, wgStoreView]
    cases w.dev <;> rfl
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w amb result v b entry run
  exact entry.frame ((ProjectedAction.iff_run_ambient _ _ _).mp same w amb result v b run)

theorem cookieConsume_native (msg : List UInt8) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (cookieMessageConsume msg) := by
  unfold cookieMessageConsume
  simp (config := {zeta := false}) only [branch, hiddenClock64, invariant]
  repeat' responder_handshake_step confirmed

theorem endpoint_native (pid : PeerId) (src : SkbSource) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (setPeerEndpointFromSkb pid src) := by
  unfold setPeerEndpointFromSkb
  simp (config := {zeta := false}) only [branch, invariant]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact native_store (endpointFromSkb_sameWGStore _) confirmed)
    | (rx_retention_head setPeerEndpoint
       exact native_fields (pool_of_material (setPeerEndpoint_material _ _))
         ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotCompletion.«0».Leanux.Proofs.WG.CurrentSlots.endpoint_fields) _ _) confirmed)
    | responder_handshake_step confirmed

end Leanux.Proofs.WG.HandshakeSecurity.Responder
