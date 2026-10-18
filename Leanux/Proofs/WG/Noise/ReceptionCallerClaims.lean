import Leanux.Proofs.WG.Noise.ReceptionDispatchSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ReceptionCaller
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.WG.Origins

/-- Complete normal dispatch classification, using the actual preamble result.
A receipt list is nonempty exactly on an admitted consumer branch. Cookie
messages, cookie replies and MAC drops remain distinct. This does not assert
that either consumer accepts a peer, or that a later operation cannot Stop. -/
theorem original_reception_dispatch (msg : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (observeClassified msg src) (fun _ => True)
      (fun call _ =>
        EntryShape msg call ∧
        GateEntryValid msg src call.gate ∧
        dispatchKind msg call.gate ≠ .wrongType ∧
        (call.receipts ≠ [] ↔ dispatchKind msg call.gate = .initiation ∨
          dispatchKind msg call.gate = .response) ∧
        ∀ r ∈ call.receipts, ReceiptValid r ∧ TagReceiptEffect r) := by
  intro g ambient call final after pre run
  obtain ⟨shape,gateValid,valid⟩ :=
    observeClassified_native msg src g ambient call final after pre run
  have classified := shape.classifies
  exact ⟨shape,gateValid,classified.1,classified.2,valid⟩

/-- Erasure is exact even if a later timer, endpoint, sender or peer release
stops. Receipt collection neither catches a Stop nor replays any helper. -/
theorem original_reception_dispatch_erases (msg : List UInt8) (src : SkbSource) :
    Campaign2.AgreesOn (fun _ => True)
      (do let _ ← observeClassified msg src; pure ())
      (receiveHandshakePacket msg src) := by
  rw [observeClassified_discard]
  intro g ambient _
  rfl

end Leanux.Proofs.WG.Noise.ReceptionCaller
