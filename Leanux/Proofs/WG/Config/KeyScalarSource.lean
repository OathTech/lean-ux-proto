import Leanux.Proofs.WG.Config.KeyScalarFrames
import Leanux.Proofs.WG.Config.KeyStagePreservationSource

/-! Actual collision cleanup and private-key stage instantiated from the existing source spine. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration
theorem conflict (entry : Map) (key : Key) :
    Preserves (Retained entry) (do
      let peer ← pubkeyLookup key
      if ← branch .setDevOldPeer peer.isSome then
        peerPut peer
        peerRemove peer : WG.M Unit) := by
  repeat' first
    | (rx_retention_head pubkeyLookup; exact (ensures_iff _ _ _).mp (of_frame entry _ (lookup _)))
    | (rx_retention_head peerPut; exact (ensures_iff _ _ _).mp (peer_put entry _))
    | (rx_retention_head peerRemove; exact (ensures_iff _ _ _).mp (remove entry _))
    | (rx_retention_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | rx_retention_step

theorem key_contracts (entry : Map) :
    Index.ConfigurationKeyRules.Contracts (Retained entry) where
  read := (ensures_iff _ _ _).mp (of_frame entry _ read_device)
  identity key := (ensures_iff _ _ _).mp (of_frame entry _ (identity key))
  cookie := (ensures_iff _ _ _).mp (of_frame entry _ cookie)
  precompute pid := (ensures_iff _ _ _).mp (of_frame entry _ (precompute pid))
  expire pid := (ensures_iff _ _ _).mp (of_frame entry _ (expire pid))
  staged pid := (ensures_iff _ _ _).mp (staged entry pid)
  conflict key := conflict entry key

theorem key_stage (entry : Map) (attrs : DeviceAttrs) :
    Ensures (RequestOrder.keyStage attrs) (Retained entry) (fun _=>Retained entry) :=
  (ensures_iff _ _ _).mpr (KeyStage.stage_preserves _ (key_contracts entry) attrs)

end Leanux.Proofs.WG.Config.GetterScalar
