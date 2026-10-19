import Leanux.Proofs.WG.Config.RequestFundedCommandsSource
import Leanux.Proofs.WG.Config.RequestCommandClaims

/-! Every completed peer command in the original arbitrary device request receives its account and represented routing state from the outer entry. Later Stops retain those completed certificates; interrupted peer internals are outside this completion claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
open Leanux Leanux.WG Queues Queues.RxCredits AllowedIps Configuration
open Leanux.Proofs.WG.Config.OwnerConfiguration

theorem certificate_peer_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result) (pre : ProjectedEntry cs loans initial)
    (i : Nat) (r : Receipt) (selected : (peerReceipts result.receipts)[i]?=some r) :
    ProjectedEntry cs loans r.before ∧ ProjectedEntry cs loans r.after :=
  certificate_entries cs loans attrs shape initial result certificate pre r
    (List.mem_of_getElem? selected)

theorem certificate_peer_routed (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result) (pre : ProjectedEntry cs loans initial)
    (i : Nat) (r : Receipt) (p : PeerAttrs)
    (selected : (peerReceipts result.receipts)[i]?=some r) (kind : r.kind=.peer p) :
    (attrs.peers.getD [])[i]?=some (.attrs p) ∧
      ProjectedEntry cs loans r.before ∧ ProjectedEntry cs loans r.after ∧
      ∃tables nested,PeerCommandFacts r p nested ∧ AccountMatches cs loans r p nested ∧
        RoutedView (r.before.wg.device.map routingState) tables ∧
        AllowedOrder.RoutedFacts tables nested := by
  have entries:=certificate_peer_entry cs loans attrs shape initial result certificate pre i r selected
  have position:=certificate_peer_position attrs initial result certificate i r p selected kind
  have wellformed:=shape p (List.mem_of_getElem? position)
  obtain ⟨tables,routed⟩:=entry_routed cs loans r.before entries.1
  obtain ⟨_,nested,point,semantics⟩:=certificate_peer_command_routed attrs initial result certificate
    i r p selected kind tables wellformed routed
  exact ⟨position,entries.1,entries.2,tables,nested,point,
    account_matches cs loans r p nested point.1 entries.1 entries.2,routed,semantics⟩

theorem certificate_routed_commands (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs)
    (shape : DeviceAddressShape attrs) (initial : Campaign2.Snapshot) (result : Inspection)
    (certificate : Certificate attrs initial result) (pre : ProjectedEntry cs loans initial) :
    RoutedCommands cs loans attrs result :=
  fun i r p selected kind=>certificate_peer_routed cs loans attrs shape initial result certificate pre
    i r p selected kind

theorem original_request_funded_routing (cs : Ledger) (loans : Reservations)
    (attrs : DeviceAttrs) (shape : DeviceAddressShape attrs) :
    Campaign2.Observes (wgSetDevice attrs) (ProjectedEntry cs loans)
      (fun initial outcome=>∃result:Inspection,result.outcome=outcome ∧
        Certificate attrs initial result ∧ Entries cs loans result.receipts ∧
        RoutedCommands cs loans attrs result) := by
  intro g a pre
  have certificate:=inspection_certificate attrs g a
  exact ⟨inspection attrs g a,inspection_outcome attrs g a,certificate,
    certificate_entries cs loans attrs shape _ _ certificate pre,
    certificate_routed_commands cs loans attrs shape _ _ certificate pre⟩

end Leanux.Proofs.WG.Config.RequestOrder.FundedCommands
