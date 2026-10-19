import Leanux.Proofs.WG.Progress.RoutingIPv4SuffixSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Native WG-facing projected suffix effects of the actual IPv4 routing queries. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing
theorem routeLookup4_record_suffix (records : List HiddenRecord) (src dst : Nat) :
    Campaign2.Ensures (liftRouting (Net.routeLookup 4 src dst))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp
    (native_liftRouting records _ (net_routeLookup4 records src dst) g)
    a (value,after) b (pre ▸ tail_self records) run
theorem routeInput4_record_suffix (records : List HiddenRecord) (src dst : Nat) :
    Campaign2.Ensures (liftRouting (Net.routeInput4 src dst))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp
    (native_liftRouting records _ (net_routeInput4 records src dst) g)
    a (value,after) b (pre ▸ tail_self records) run
end Leanux.Proofs.WG.Progress.RecordSuffix
