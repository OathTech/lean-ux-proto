import Leanux.Proofs.WG.Config.ScalarCommandSource
import Leanux.Proofs.WG.Config.ConfiguredBoundaryBridge

/-! Projected normal scalar result for an existing target of the public peer command. The initial account derives residency and reference funding. Malformed or negative allowed-IP exits retain earlier scalar writes and bypass keepalive; completed finish applies the optional interval. This is not a totality or stopped-state claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarCommand
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration
open PeerScalarRetention
theorem original_existing_command (cs : Ledger) (loans : Reservations)
    (attrs : PeerAttrs) (key : Key) (pid : PeerId) (before : Device)
    (pubkey : attrs.publicKey=some key)
    (valid : attrs.flags.getD 0 &&& ~~~WGPEER_F_ALL=0)
    (protocol : attrs.protocolVersion=none ∨ attrs.protocolVersion=some 1)
    (keep : attrs.flags.getD 0 &&& WGPEER_F_REMOVE_ME=0)
    (found : before.peerHashtable.find? (·.1 == key)=some (key,pid)) :
    Campaign2.Ensures (setPeerCmd attrs)
      (fun s=>OwnerConfiguration.ProjectedEntry cs loans s ∧ s.wg.device=some before)
      (fun ret s=>Index.View.ConfigurationInput cs loans s ∧
        ∃ p,before.peers[pid]?=some p ∧
          observation s pid=some (ScalarTail.tailCell attrs ret
            (ScalarTail.prefixCell p attrs.presharedKey attrs.endpoint))) := by
  intro g a result v b pre run
  have done := existing_command cs loans attrs key pid before pubkey valid protocol keep found
    g a result v b ⟨(OwnerConfiguration.entry_snapshot cs loans g a).mp pre.1,pre.2⟩ run
  exact ⟨(Index.configurationInput_snapshot cs loans v b).mpr done.1,done.2⟩

end Leanux.Proofs.WG.Config.ScalarCommand
