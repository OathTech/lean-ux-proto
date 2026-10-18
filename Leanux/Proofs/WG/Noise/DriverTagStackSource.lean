import Leanux.Proofs.WG.Index.TransmitRuleSource
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
  apply Index.TransmitCore.stack_preserves_source
  · intro w v same prior
    have tags : tagView v.wg=tagView w.wg :=
      congrArg (fun s : ProductStore43=>responseTagMap s.2.2.2.dev) same
    change TagsRetained entry (tagView v.wg)
    rw [tags]
    exact prior
  · intro family addr packets mtu
    exact PublicationPoll.native_product _ _ (Transmit.native entry family addr packets mtu)
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
