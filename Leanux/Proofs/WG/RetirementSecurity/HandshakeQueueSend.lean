import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueSocket
import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueNapi

/-! Native TX completion and scheduling leaves retain the handshake ring.
These frames allow actual packet disposal and final reference releases. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do

theorem sendSkbToPeer_cell pid bytes ds : SameView view (sendSkbToPeer pid bytes ds) := by
  handshake_cell_source [sendSkbToPeer] using [send4_cell, send6_cell]

theorem timersDataSent_cell pid : SameView view (timersDataSent pid) := by
  have clock : SameView view (callerJiffies .timerJiffiesDataSent) :=
    (callerJiffies_sameWGWorld .timerJiffiesDataSent).factor view
  have jitter : SameView view (jitterBelowRekeyTimeout .newHandshakeJitter) :=
    (jitterBelowRekeyTimeout_sameWGWorld .newHandshakeJitter).factor view
  have arm (delay : Nat) (jc : Option UInt64) :
      SameView view (armTimer pid .newHandshake delay jc) := armTimer_cell pid _ delay jc
  handshake_cell_source [timersDataSent] using [clock, jitter, modPeerTimerGuard_cell, arm]

theorem timersAnyAuthenticatedPacketSent_cell pid : SameView view (timersAnyAuthenticatedPacketSent pid) :=
  delTimer_cell pid .sendKeepalive

theorem keepKeyFresh_cell pid : SameView view (keepKeyFresh pid) := by
  have expired (d : Decision) (birth : Int64) (age : Nat) :
      SameView view (branchExpired d birth age) :=
    (branchExpired_sameWGWorld d birth age).factor view
  handshake_cell_source [keepKeyFresh] using [expired, sendQueuedHandshakeInitiation_cell]

theorem createDataDone_cell pid item : SameView view (createDataDone pid item) := by
  handshake_cell_source [createDataDone] using [timersTraversal_cell,
    timersAnyAuthenticatedPacketSent_cell, sendSkbToPeer_cell, timersDataSent_cell, keepKeyFresh_cell]

theorem txStep_cell pid : SameView view (txStep pid) := by
  have peek := fun (q : PrevQueue (List SkbId)) => kernel (prevQueuePeek_sameWGStore q)
  handshake_cell_source [txStep] using [peek, createDataDone_cell, keypairPut_frame, peerPut_frame]

theorem txIter_cell (pid : PeerId) (resched : Leanux.M Bool)
    (hr : SameView productView resched) : SameView productView (txIter pid resched) := by
  handshake_poll_source [txIter, workerIter] using [hr] with [txStep_cell]


end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
