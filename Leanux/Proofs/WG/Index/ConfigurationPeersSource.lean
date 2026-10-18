import Leanux.Proofs.WG.Index.ConfigurationCommandSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

theorem command_entry (cs : Ledger) (loans : Reservations) (attrs : PeerAttrs) :
    Preserves (Entry cs loans) (setPeerCmd attrs) := by
  rw [←setPeerCmd_source,setPeerCmdSource_factor]
  unfold setPeerCmdWith WG.andM
  simp (config:={zeta:=false}) only [branch,invariant]
  repeat' first
    | contradiction
    | (env_bind_head pubkeyLookup
       apply hoare_bind _ _ ((ensures_iff _ _ _).mp (lookup cs loans _))
       intro peer
       exact acquired_entry cs loans attrs _ _ _ peer)
    | (env_bind_head peerPut; exact noneOut_entry cs loans attrs _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | rx_retention_step

theorem peers_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    Preserves (Entry cs loans) (devicePeersSource attrs) := by
  rw [devicePeersSource_factor]
  unfold devicePeersWith
  simp (config:={zeta:=false}) only [branch]
  repeat' first
    | (rx_retention_head setPeerCmd; exact command_entry cs loans _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Entry cs loans)
       intro x b
       change Preserves (Entry cs loans) _)
    | rx_retention_step

theorem privateKey_entry (cs : Ledger) (loans : Reservations) (attrs : DeviceAttrs) :
    Preserves (Entry cs loans) (deviceKeySource attrs) :=
  key_entry cs loans attrs (peers_entry cs loans attrs)

end Leanux.Proofs.WG.Index.ConfigurationIndex
