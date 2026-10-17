import Leanux.Proofs.WG.Origins.ConfiguredMaintenance
import Leanux.Proofs.WG.Origins.CurrentIdentity

/-! Native clear and invalidation calls retain the same-receipt current peer
identity. The concrete source contracts keep nullable owners and absent peers;
no affiliation or successful-allocation premise is added. -/
namespace Leanux.Proofs.WG.ConfiguredMaintenance
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Lifetimes

theorem keypairsClear_current (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (CurrentIdentity.Inv history) (keypairsClear pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  apply hi.retain
  apply CurrentIdentity.retains_of_configured_view
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (Origins.Retaining.keypairsClear_material pid) w ambient result v ambient' hr
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (keypairsClear_view pid) w ambient result v ambient' hr

theorem handshakeClear_current (pid : PeerId) (history : List SessionOrigin.Receipt) :
    Preserves (CurrentIdentity.Inv history) (handshakeClear pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  apply hi.retain
  apply CurrentIdentity.retains_of_configured_view
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (Origins.Retaining.of_view (Origins.Retaining.handshakeClear_material pid))
      w ambient result v ambient' hr
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (handshakeClear_view pid) w ambient result v ambient' hr

theorem expireCurrentPeerKeypairs_current (pid : PeerId)
    (history : List SessionOrigin.Receipt) :
    Preserves (CurrentIdentity.Inv history) (expireCurrentPeerKeypairs pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  apply hi.retain
  apply CurrentIdentity.retains_of_configured_view
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (Origins.Retaining.expireCurrentPeerKeypairs_material pid)
      w ambient result v ambient' hr
  · exact (ProjectedAction.iff_run_ambient _ _ _).mp
      (expireCurrentPeerKeypairs_view pid) w ambient result v ambient' hr

end Leanux.Proofs.WG.ConfiguredMaintenance
