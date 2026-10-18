import Leanux.Proofs.WG.Packets.PublicationPeerConfiguration
import Leanux.Proofs.WG.Packets.PublicationJoint

/-! The original peer-command observer carries the same packet and owner
journal, including failed prefixes and negative errno after partial updates. -/
namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues

theorem setAllowedip (pid : PeerId) (ip : AllowedIpAttrs) :
    Preserves (RxHistory.mixed (liftWGObserver (setAllowedipPrefix pid ip))) := by
  apply native_mixed _ _ ?_ (setAllowedipPrefix_erases pid ip)
    (PublicationFrontier.setAllowedip_preserves pid ip)
  apply OwnerChecks.native_mixed _ _ (setAllowedipPrefix_erases pid ip)
    (ConfigurationCall.allocation (.allowedIp pid ip))
    (Origins.Retaining.of_view (Origins.Retaining.setAllowedip_material pid ip))
    (CurrentConfiguration.setAllowedip_preserves pid ip)
  intro history
  exact hoare_consequence (OwnerAllowedIps.setAllowedip_preserves pid ip)
    (fun _ hi => hi.2) (fun _ _ hi => hi)

theorem setPeerCmd (a : PeerAttrs) :
    Preserves (RxHistory.mixed (liftWGObserver (setPeerCmdPrefix a))) :=
  native_mixed _ _ (JointOwnerConfiguration.setPeerCmd_checked a)
    (ConfigurationCall.erases (.peer a)) (PublicationFrontier.setPeerCmd_preserves a)

end Leanux.Proofs.WG.PublicationJoint
