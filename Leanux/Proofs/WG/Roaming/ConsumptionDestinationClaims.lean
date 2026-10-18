import Leanux.Proofs.WG.Roaming.ConsumptionDestinationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise
open Noise.ConfirmationOrder Noise.ConsumeConfirmation

/-- Complete native data consumption retains the selected destination update
through the original continuation. Removed destinations are allowed; no
authentication or peer-survival premise is inferred for a raw native call. -/
theorem consumeDataDone_final_remotes (entry : Campaign2.Snapshot)
    (pid : PeerId) (pkt : RxPacket) (endpoint : Endpoint)
    (valid : endpoint.family = AF_INET ∨ endpoint.family = AF_INET6) :
    Campaign2.Ensures (consumeDataDone pid pkt endpoint)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (updateRemote (remoteMap entry) pid (destination endpoint))
        (remoteMap s)) :=
  RemoteCompletion.consumeDataDone_remotes (remoteMap entry) pid pkt endpoint valid

/-- The complete ordered initialized list of finished data consumptions has
earlier AEAD provenance and source-selected remote destinations retained
through each whole call. The list includes nondelivery and calls before a
later outer Stop; no failed consume prefix or peer survival is asserted. -/
theorem initialized_consumptions_authenticated_final (trace : Runner.Trace) (placeholders : Bool) :
    ∃ qs,
      observations trace placeholders = .ok qs ∧
      qs.Pairwise (fun a b => a.position < b.position) ∧
      qs.length = consumedCount (history trace placeholders) ∧
      (∀ q, q ∈ qs ↔ OccursAt trace placeholders q) ∧
      ∀ q ∈ qs, ∃ e : ConsumptionAuthentication,
        e.Valid trace placeholders q ∧ e.Facts q ∧ ConsumptionFinalRemotes q := by
  obtain ⟨qs,run,ordered,count,complete,authenticated⟩ :=
    initialized_consumptions_authenticated trace placeholders
  refine ⟨qs,run,ordered,count,complete,?_⟩
  intro q member
  obtain ⟨e,valid,facts⟩ := authenticated q member
  exact ⟨e,valid,facts,consumption_final_remotes trace placeholders q ((complete q).mp member)⟩

end Leanux.Proofs.WG.Roaming

