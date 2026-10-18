import Leanux.Proofs.WG.Index.ConfigurationAllowedFrames
import Leanux.Proofs.WG.Index.ConfigurationStageSource
import Leanux.Proofs.WG.Queues.SlotConfiguration

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Queues.RxCredits.DurableHolders

theorem accounted_fields_entry {α : Type} (cs : Ledger) (loans : Reservations)
    (action : WG.M α) (account : Preserves (Boundary cs loans) action)
    (base : SameView BaseCoherence.view action)
    (configured : SameView ConfiguredIdentity.view action)
    (slots : Preserves CurrentSlots.Inv action) (same : SameView fields action) :
    Preserves (Entry cs loans) action := by
  refine join_entry cs loans action ?_ slots ?_
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b pre run
    have identity := (ProjectedAction.iff_run_ambient _ _ _).mp configured w a result v b run
    exact ⟨(hoare_iff_run_ambient _ _ _).mp account w a result v b pre.1 run,
      BaseCoherence.transport pre.2.1
        ((ProjectedAction.iff_run_ambient _ _ _).mp base w a result v b run),
      fun s hs=>pre.2.2 s (identity ▸ hs)⟩
  · intro w a result v b pre run
    exact (hoare_iff_run_ambient _ _ _).mp (frame_core same) w a result v b pre.2 run

theorem setAllowedip_entry (cs : Ledger) (loans : Reservations)
    (pid : PeerId) (ip : AllowedIpAttrs) :
    Preserves (Entry cs loans) (setAllowedip pid ip) :=
  accounted_fields_entry cs loans _ (HolderAllowedIps.setAllowedip_boundary pid ip)
    (BaseCoherence.setAllowedip_view pid ip) (CurrentConfiguration.setAllowedip_view pid ip)
    (CurrentSlots.Configuration.allowedip pid ip) (setAllowedip_fields pid ip)

theorem removeByPeer_entry (cs : Ledger) (loans : Reservations) (pid : PeerId) :
    Preserves (Entry cs loans) (removeByPeer pid) :=
  accounted_fields_entry cs loans _ (HolderConfigUpdate.removeByPeer_boundary pid)
    (BaseCoherence.removeByPeer_view pid) (ConfiguredIdentity.removeByPeer_view pid)
    (CurrentSlots.Removal.removeByPeer_preserves pid) (removeByPeer_fields pid)
end Leanux.Proofs.WG.Index.ConfigurationIndex
