import Leanux.Proofs.WG.Index.IncomingIndexSource
import Leanux.Proofs.WG.Index.ReachedIndexModel
import Leanux.Proofs.WG.Index.ConsumeSource
import Leanux.Proofs.WG.Index.OwnerCoherenceInitiationClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceResponseClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do
open Queues.RxCredits

/-- Original initiation consumption preserves supplied hashed-slot coverage and
retirement on every normal return. Lookup success supplies the extra reference
used by each failed-authentication cleanup; no coherence or readiness premise
is required for these two predicates. -/
theorem consumeInitiation_hashSlots_retirement (retired : Reservations) (msg : List UInt8) :
    Campaign2.Ensures (consumeInitiation msg)
      (fun s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s) := by
  intro g a result out b pre run
  have post := consumeInitiation_incomingIndex retired msg g a result out b
    (fun d device => ⟨pre.1 d device,pre.2 d device⟩) run
  exact ⟨fun d device => (post d device).1,fun d device => (post d device).2⟩

/-- The actual handshake-mask response lookup retains both invariants even on
its owner-word-clear failure cases. Rejected authentication pays only the
source-acquired reference; successful consumption retains that reference. -/
theorem consumeResponse_hashSlots_retirement (retired : Reservations) (msg : List UInt8) :
    Campaign2.Ensures (consumeResponse msg)
      (fun s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s)
      (fun _ s => View.HashSlotsSafe s ∧ View.RetirementSafe retired s) := by
  intro g a result out b pre run
  have post := consumeResponse_incomingIndex retired msg g a result out b
    (fun d device => ⟨pre.1 d device,pre.2 d device⟩) run
  exact ⟨fun d device => (post d device).1,fun d device => (post d device).2⟩
/-- All four index components concern the same original consumer run. This
retains the existing table and owner contracts alongside the new slot relation. -/
theorem consumeInitiation_indexCore (msg : List UInt8) :
    Campaign2.Ensures (consumeInitiation msg) View.IndexCore
      (fun _ => View.IndexCore) := by
  intro w a result v b pre run
  have tables := consumeInitiation_tables msg w a result v b
    (fun d device => (pre d device).1) run
  have owners := consumeInitiation_owner_coherent msg w a result v b
    (fun d device => (pre d device).2.2.1) run
  have retained := consumeInitiation_hashSlots_retirement [] msg w a result v b
    ⟨fun d device => (pre d device).2.1,fun d device => (pre d device).2.2.2⟩ run
  exact fun d device => ⟨tables d device,retained.1 d device,
    owners d device,retained.2 d device⟩

/-- The complete response consumer preserves the full local index package.
Its original failure-side owner-word store and acquired-reference payment remain. -/
theorem consumeResponse_indexCore (msg : List UInt8) :
    Campaign2.Ensures (consumeResponse msg) View.IndexCore
      (fun _ => View.IndexCore) := by
  intro w a result v b pre run
  have tables := consumeResponse_tables msg w a result v b
    (fun d device => (pre d device).1) run
  have owners := consumeResponse_owner_coherent msg w a result v b
    (fun d device => (pre d device).2.2.1) run
  have retained := consumeResponse_hashSlots_retirement [] msg w a result v b
    ⟨fun d device => (pre d device).2.1,fun d device => (pre d device).2.2.2⟩ run
  exact fun d device => ⟨tables d device,retained.1 d device,
    owners d device,retained.2 d device⟩

end Leanux.Proofs.WG.Index
