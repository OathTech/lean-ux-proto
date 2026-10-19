import Leanux.Proofs.WG.Config.ConfiguredCommandSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

/-- Projected selected-update contract, retaining exact normal cleanup. -/
theorem original_update (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) (paid : Owner) (flags : UInt32) (psk : Option Key) :
    Campaign2.Ensures (Configuration.peerConfigUpdateSource attrs (some paid.slot) flags psk paid.slot)
      (ProjectedSelected cs (paid::loans) paid.slot) (fun _=>ProjectedEntry cs loans) := by
  intro g a result v b pre run
  exact (entry_snapshot cs loans v b).mpr
    (update_entry cs loans attrs shape paid flags psk g a result v b
      ((selected_snapshot cs (paid::loans) paid.slot g a).mp pre) run)

/-- Every normal original peer-command result retains its same-run account,
index package and configured routing ownership. This includes refusals. -/
theorem original_command (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs)
    (shape : PeerAddressShape attrs) :
    Campaign2.Ensures (setPeerCmd attrs) (ProjectedEntry cs loans) (fun _=>ProjectedEntry cs loans) := by
  intro g a result v b pre run
  exact (entry_snapshot cs loans v b).mpr
    ((hoare_iff_run_ambient _ _ _).mp (command_entry cs loans attrs shape)
      g a result v b ((entry_snapshot cs loans g a).mp pre) run)

end Leanux.Proofs.WG.Config.OwnerConfiguration
