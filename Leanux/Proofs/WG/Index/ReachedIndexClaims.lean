import Leanux.Proofs.WG.Index.ReachedIndexModel
import Leanux.Proofs.WG.Index.BoundedSessionClaims
import Leanux.Proofs.WG.Index.RetirementSessionClaims
import Leanux.Proofs.WG.Index.TablePreservationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

namespace Reached
open Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits
open DurableHolders

/-- The original session preserves the complete index component from bounds
at its actual entry, including normal false/refusal returns. -/
theorem session_core (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s => InitializedBounds.EndpointSafe s ∧ View.IndexCore s)
      (fun _ s => View.IndexCore s) := by
  intro w a result v b entry run
  have tables := (hoare_iff_run_ambient _ _ _).mp (beginSession_tables pid)
    w a result v b (fun d device => (entry.2 d device).1) run
  have state := beginSession_endpoint_hashSlots pid w a result v b
    ⟨entry.1,fun d device => (entry.2 d device).2.2.1,
      fun d device => (entry.2 d device).2.1⟩ run
  have retired := beginSession_endpoint_retirement [] pid w a result v b
    ⟨entry.1,fun d device => (entry.2 d device).2.2.1,
      fun d device => (entry.2 d device).2.2.2⟩ run
  intro d device
  exact ⟨tables d device,state.2 d device,state.1 d device,retired d device⟩
end Reached
end Leanux.Proofs.WG.Index
