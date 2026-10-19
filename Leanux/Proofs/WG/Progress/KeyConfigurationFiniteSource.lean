import Leanux.Proofs.WG.Progress.PeerInitializationFiniteSource
import Leanux.Proofs.WG.Progress.MaintenanceFiniteSource
import Leanux.Proofs.WG.Config.KeyStageFactors

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.KeyConfigurationFinite
open Leanux Leanux.WG

/-- Actual peer update with finite guarded curve precomputation. Expiry and
staging only traverse bounded native data and queue later work. -/
def peer (pid : PeerId) (sendStaged : Bool) : WG.M Unit :=
  Config.keyPeerSourceWith PeerFinite.precompute pid sendStaged

theorem peer_source (pid : PeerId) (sendStaged : Bool) :
    Config.keyPeerSource pid sendStaged = peer pid sendStaged := by
  change Config.keyPeerSourceWith WG.precomputeStaticStatic pid sendStaged = _
  unfold peer
  rw [funext PeerFinite.precompute_source]

/-- The original saved-list traversal, with the finite concrete peer callback. -/
def peers (pids : List PeerId) (sendStaged : Bool) : WG.M Unit :=
  Config.keyPeerLoopSourceWith PeerFinite.precompute pids sendStaged

theorem peers_source (pids : List PeerId) (sendStaged : Bool) :
    Config.keyPeerLoopSource pids sendStaged = peers pids sendStaged := by
  change Config.keyPeerLoopSourceWith WG.precomputeStaticStatic pids sendStaged = _
  unfold peers
  rw [funext PeerFinite.precompute_source]

/-- Original identity/cookie installation and its captured peer traversal,
with finite identity generation and peer precomputation. -/
def install (key : Key) : WG.M Unit :=
  Config.keyInstallSourceWith PeerFinite.setPrivate PeerFinite.precompute key

theorem install_source (key : Key) :
    Config.keyInstallSource key = install key := by
  change Config.keyInstallSourceWith WG.setStaticIdentityPrivateKey WG.precomputeStaticStatic key = _
  unfold install
  rw [funext PeerFinite.setPrivate_source,funext PeerFinite.precompute_source]

/-- Actual generated-key collision path, including acquisition, payment,
and queued removal; all source refusals and failed drains remain exact. -/
def collision (key : Key) : WG.M Unit :=
  Config.keyCollisionSourceWith HandshakeFinite.generatePublic MaintenanceFinite.remove key

theorem collision_source (key : Key) :
    Config.keyCollisionSource key = collision key := by
  change Config.keyCollisionSourceWith WG.generatePublic WG.peerRemove key = _
  unfold collision
  rw [funext HandshakeFinite.generatePublic_source,funext MaintenanceFinite.remove_source]

/-- The complete original private-key stage. Missing and unchanged keys retain
their early exits; the changed-key branch uses concrete finite callbacks. -/
def stage (attrs : DeviceAttrs) : WG.M Int :=
  Config.devicePrivateSourceWith collision install (pure 0) attrs

theorem stage_source (attrs : DeviceAttrs) :
    Config.RequestOrder.keyStage attrs = stage attrs := by
  rw [Config.KeyStage.stage_factor]
  change Config.devicePrivateSourceWith Config.keyCollisionSource Config.keyInstallSource (pure 0) attrs = _
  unfold stage
  rw [funext collision_source,funext install_source]

end Leanux.Proofs.WG.Progress.KeyConfigurationFinite
