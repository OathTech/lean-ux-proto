import Leanux.Proofs.WG.Config.RequestCommandBridge
import Leanux.Proofs.WG.Config.CommandOrderInspectionSource

/-! Extraction from actual completed peer receipts. Both snapshots and the normal result are those of the original witnessed call. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.AllowedIps Configuration Noise

theorem valid_peer_command (attrs : DeviceAttrs) (r : Receipt) (p : PeerAttrs)
    (valid : Valid attrs r) (kind : r.kind=.peer p) :
    ∃nested,PeerCommandFacts r p nested := by
  obtain ⟨native,run,same⟩:=valid
  rw [kind] at run same
  let nested:=CommandOrder.inspection p native.before native.ambientBefore
  refine ⟨nested,⟨native,run,same,rfl⟩,?_,?_⟩
  · have agreement:=CommandOrder.inspection_outcome p native.before native.ambientBefore
    change ((setPeerCmd p).run native.before).run native.ambientBefore=
      .ok ((native.value,native.after),native.ambientAfter) at run
    rw [run] at agreement
    simpa only [nested,←same,receipt,Campaign2.observeResult,Except.map] using agreement
  · have order:=CommandOrder.inspection_facts p native.before native.ambientBefore
    simpa only [nested,←same,receipt] using order

theorem PeerCommandMatches.routed (r : Receipt) (p : PeerAttrs)
    (nested : AllowedOrder.Inspection) (matched : PeerCommandMatches r p nested)
    (tables : FlatTable×FlatTable) (shape : PeerAddressShape p)
    (entry : RoutedView (r.before.wg.device.map routingState) tables) :
    AllowedOrder.RoutedFacts tables nested := by
  obtain ⟨native,_,same,rfl⟩:=matched
  exact CommandOrder.inspection_routed tables p shape native.before native.ambientBefore
    (by simpa only [←same,receipt] using entry)

end Leanux.Proofs.WG.Config.RequestOrder
