import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeSocketSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryHandshakeFrames

/-! Native route and cache points preserve the complete TX projection.
The sole datagram append changes only the sent observation; its fixed native
suffix returns before the original protocol receipt. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeSocket
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity

theorem action_frame (args : ProtocolSocket.Args) : SameView StagedEntry.view args.action := by
  unfold ProtocolSocket.Args.action
  cases args.ipv4 with
  | false=>exact HandshakeFrames.socket6 _ _ _ _ _
  | true=>exact HandshakeFrames.socket4 _ _ _ _ _

theorem Point.frame (point : Point args w a v b) : StagedEntry.view v=StagedEntry.view w := by
  cases point with
  | source point=>exact point.view (SocketFront.canonical_framed _ _ _ _ _ _ [])
  | returned performed=>exact (ProjectedAction.iff_run_ambient _ _ _).mp (action_frame args) _ _ _ _ _ performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeSocket
