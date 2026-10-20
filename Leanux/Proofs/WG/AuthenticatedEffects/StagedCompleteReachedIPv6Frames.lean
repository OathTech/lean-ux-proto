import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIPv6Source

/-! IPv6 predicate checks and the fixture inbox write preserve the packet
account. This frame refers to the fixed source, including its refusals. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.IPv6
open Leanux Leanux.Proofs.Logged TransmitSecurity CausalJournal

/-- Every declared IPv6 receive source point retains the current packet
account. All refusal paths remain explicit, and the source has no nested
transmit or packet-disposal callback. -/
theorem Point.carrier (point : Point bytes w h u middle)
    (before : Napi.Points.Carrier h w) : Napi.Points.Carrier middle u := by
  obtain ⟨site,point⟩:=point
  exact Napi.Points.boundary_carrier point before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.IPv6
