import Leanux.Proofs.WG.Config.InitializedOwnerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.InitializedOwner
open Lean Leanux Leanux.WG AllowedIps

/-- Ownership and the reference account refer to one actual endpoint of the
initialized paired runner; neither is supplied as a premise. -/
theorem normal (trace : Runner.Trace) (shape : Configuration.TraceAddressShape trace)
    (placeholders : Bool) (json : Json) (final : Campaign2.Product.Snapshot)
    (run : (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final)) :
    OwnershipAt final := by
  have ready := OwnerDriver.inspection_ready trace shape placeholders json final run
  have owners := OwnerConfiguration.initialized_account_owners trace placeholders json final
    ready (InitializedRouting.normal trace shape placeholders json final run).2.2.2.2.2
  intro d device
  obtain ⟨t4,t6,routing,_⟩ := ready d device
  exact ⟨⟨t4,t6,routing⟩,fun a b invariant=>owners d a b device invariant⟩

theorem accepted (trace : Runner.Trace) (shape : Configuration.TraceAddressShape trace)
    (placeholders : Bool) (json : Json)
    (run : Runner.executeTrace trace placeholders=.ok json) :
    ∃ final, (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final) ∧
      OwnershipAt final := by
  obtain ⟨final,actual,_⟩ := InitializedRouting.accepted trace shape placeholders json run
  exact ⟨final,actual,normal trace shape placeholders json final actual⟩

/-- Successful parsing supplies every actual configuration address bound.
Both placeholder modes and arbitrary mixed traces are included. -/
theorem parsed_accepted (input : Json) (trace : Runner.Trace)
    (parsed : Runner.parseTrace input=.ok trace) (placeholders : Bool) (json : Json)
    (run : Runner.executeTrace trace placeholders=.ok json) :
    ∃ final, (InitializedRouting.inspection trace placeholders).outcome=.ok (json,final) ∧
      OwnershipAt final :=
  accepted trace (Configuration.parseTrace_shape input trace parsed) placeholders json run

end Leanux.Proofs.WG.Config.InitializedOwner
