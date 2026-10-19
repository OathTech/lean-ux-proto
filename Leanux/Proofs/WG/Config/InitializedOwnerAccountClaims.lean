import Leanux.Proofs.WG.Config.ConfiguredBoundaryClaims
import Leanux.Proofs.WG.Config.InitializedRoutingClaims
import Leanux.Proofs.WG.Config.ConfiguredLifecycleSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Lean Leanux Leanux.WG AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Logged

/-- The exact initialized account joins optional configured ownership to any
representation of that same endpoint. This lemma does not supply the ownership
transport; the whole-driver proof must establish its first premise. -/
theorem initialized_account_owners (trace : Runner.Trace) (placeholders : Bool)
    (json : Json) (final : Campaign2.Product.Snapshot)
    (ready : ProjectedOptionalReady final.toSnapshot)
    (account : Index.ReachedInitialized.ActualAccount trace placeholders json final) :
    ∀ d t4 t6, final.wg.device=some d → RoutingInvariant d t4 t6 →
      ConfiguredOwners d t4 t6 ∧ ResidentOwnerLists d t4 t6 := by
  obtain ⟨w,history,ledger,run,rfl,certificate,holders⟩ := account
  obtain ⟨other,entry⟩ := Index.ReachedTraffic.initialized trace placeholders json w history run
  have index := Index.ReachedControls.entry_configuration
    (cs:=ledger) (loans:=[]) (h:=history) (w:=w) ⟨holders,entry.2⟩
  intro d t4 t6 device routing
  apply projected_entry_resident ledger [] (Campaign2.snapshot w.wg w.ambient) d t4 t6
  · apply (entry_snapshot ledger [] w.wg w.ambient).mpr
    exact ⟨index,d,device,ready d device⟩
  · exact device
  · exact routing

end Leanux.Proofs.WG.Config.OwnerConfiguration
