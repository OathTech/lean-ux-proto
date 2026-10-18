import Leanux.Proofs.WG.Noise.DriverTagTransmitSource
import Leanux.Proofs.WG.Noise.DriverTagProductFrames
import Leanux.Proofs.WG.Noise.PendingStackSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags.Stack
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Std.Do

/-! Reuse the existing actual Stack source and its exact erasure. Its sole
transmit callback is the original wgXmit, now supplied with concrete tag
retention. No Stack body or projection proof is duplicated. -/
theorem source_preserves (entry : TagMap) (bytes : List UInt8) :
    PrefixPreserves (fun (_ : List Empty) (w : World) => Silent.Retained entry w.wg)
      (fun _ => True) (PendingStack.stackSource bytes) := by
  have safe : ∀ (_ : List Empty) (w : World), Silent.Retained entry w.wg → True :=
    fun _ _ _ => True.intro
  have store : ∀ (_ : List Empty) (w v : World),
      productStoreView v = productStoreView w →
      Silent.Retained entry w.wg → Silent.Retained entry v.wg := by
    intro _ w v same prior
    exact (state_product_store entry [] w v same
      ⟨prior,by intro event member; cases member⟩).1
  unfold PendingStack.stackSource
  apply stackReceiveWith_preserves safe store
  intro packet
  apply receive4With_preserves safe store
  intro dst packet
  apply reply4With_preserves safe store
  intro family addr packets mtu
  unfold PendingStack.transmit
  apply PrefixEnsures.lift (Q := fun _ _ w => Silent.Retained entry w.wg) _ safe
  intro _ w result v prior run
  exact prior.trans (native_product_retained _
    (Transmit.retained family addr packets mtu) w result v run)

/-- Complete original Stack callback on normal return, including actual routed
IPv4 replies through wgXmit. Invalid and excluded paths retain their original
Stops; no readiness, residency or replacement-callback premise is needed. -/
theorem native (entry : TagMap) (bytes : List UInt8) :
    Preserves (fun w : World => Silent.Retained entry w.wg)
      (Env.deliverInner bytes) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v prior run
  obtain ⟨suffix,appended,safe,normal⟩ := source_preserves entry bytes w [] prior
  have erased := (PendingStack.stackSource_erases bytes w []).trans run
  simpa only [erased] using normal

theorem retained (bytes : List UInt8) (w : World) (value : Unit) (final : World)
    (run : (Env.deliverInner bytes).run w = .ok (value,final)) :
    TagsRetained (tagView w.wg) (tagView final.wg) :=
  (hoare_iff_run _ _ _).mp (native (tagView w.wg) bytes)
    w value final (TagsRetained.refl _) run

end Leanux.Proofs.WG.Noise.DriverTags.Stack
