import Leanux.Proofs.WG.Roaming.RemoteSessionFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Lifetimes Leanux.Proofs.Framing TimerDiscipline Std.Do

/-- Normal session setup preserves every remote destination. -/
theorem beginSession_remotes (pid : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (beginSession pid) (fun s => remoteMap s = remoteMap entry)
      (fun _ s => remoteMap s = remoteMap entry) := by
  intro g ambient result final after pre run
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp (beginSession_endpoints pid)
    g ambient result final after run).trans pre

/-- Releasing a peer can remove it; every surviving remote destination is retained. -/
theorem peerPut_retains_remotes (peer : Option PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (peerPut peer) (fun s => RemoteRetained (remoteMap entry) (remoteMap s))
      (fun _ s => RemoteRetained (remoteMap entry) (remoteMap s)) :=
  peerPut_remotes peer (remoteMap entry)

end Leanux.Proofs.WG.Roaming
