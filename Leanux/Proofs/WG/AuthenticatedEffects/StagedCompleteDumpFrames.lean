import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteLifecycleSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseDumpErasure
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteNativeCalls

/-! Dump metadata and cursor acquisition retain the full packet entry view.
Cursor repayment is deliberately absent: it uses the counted release source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDump
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal NetlinkDump

theorem frame {action : WG.M α} (same : SameDump action) : SameView StagedEntry.view action :=
  same.of_factor (fun s : WGStoreView => StagedEntry.view {dev := s.dev}) StagedEntry.view
    (fun _ => rfl)

macro "complete_dump_frame" : tactic => `(tactic| (
  intro initial
  change Preserves (fun w => StagedEntry.view w = initial) _
  repeat' first
    | (rx_retention_head RxCredits.DumpReservation.walkSource
       exact ((RxCredits.DumpReservation.walk_frame _ _ _).factor StagedEntry.view) initial)
    | (rx_retention_head deviceDumpHeaderSource
       exact TimerFrames.store (deviceDumpHeader_sameWGStore _ _ _ _) initial)
    | (rx_retention_head getNlSock
       exact ((getNlSock_sameWGWorld _).factor StagedEntry.view) initial)
    | (rx_retention_head setNlSock; exact frame (setNlSock_sameDump _ _) initial)
    | (rx_retention_head lookupInterface
       exact ((lookupInterface_sameWGWorld _).factor StagedEntry.view) initial)
    | (rx_retention_head coalesce
       exact ((coalesce_sameWGWorld _).factor StagedEntry.view) initial)
    | (rx_retention_head peerGet; exact Queued.acquire _ initial)
    | (rx_retention_head unsupported; exact hoare_liftAmbient (AmbientM.unsupported _) _)
    | (rx_retention_head WG.andM; unfold WG.andM)
    | (rx_retention_head WG.orM; unfold WG.orM)
    | entry_handshake_native_step initial))

theorem ops_erases : NestedPeerRelease.Ops.Erases (Driver.nestedOps hooks) where
  step := fun _ => erasesStatePrefix_lift _
  release := CompleteNative.release_erases

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteDump
