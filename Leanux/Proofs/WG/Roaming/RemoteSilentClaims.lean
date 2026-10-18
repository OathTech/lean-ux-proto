import Leanux.Proofs.WG.Roaming.RemoteSilentSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG

theorem timerCallback_retains_remotes (entry : Campaign2.Snapshot)
    (pid : PeerId) (timer : PeerTimer) :
    Campaign2.Ensures (timerCallback pid timer)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (remoteMap entry) (remoteMap s)) := by
  intro g a result final b pre run
  exact RemoteSilent.callback (remoteMap entry) pid timer g a result final b
    (RemoteRetained.of_eq pre) run

theorem clearWorker_retains_remotes (entry : Campaign2.Snapshot) (pid : PeerId) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (remoteMap entry) (remoteMap s)) := by
  intro g a result final b pre run
  exact RemoteSilent.clearWorker (remoteMap entry) pid g a result final b
    (RemoteRetained.of_eq pre) run

theorem sendWorker_retains_remotes (entry : Campaign2.Snapshot) (pid : PeerId) :
    Campaign2.Ensures (handshakeSendWorker pid)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (remoteMap entry) (remoteMap s)) := by
  intro g a result final b pre run
  exact RemoteSilent.sendWorker (remoteMap entry) pid g a result final b
    (RemoteRetained.of_eq pre) run

theorem dataCompletion_retains_remotes (entry : Campaign2.Snapshot)
    (pid : PeerId) (item : List SkbId) :
    Campaign2.Ensures (createDataDone pid item)
      (fun s => remoteMap s = remoteMap entry)
      (fun _ s => RemoteRetained (remoteMap entry) (remoteMap s)) := by
  intro g a result final b pre run
  exact RemoteSilent.dataCompletion (remoteMap entry) pid item g a result final b
    (RemoteRetained.of_eq pre) run

end Leanux.Proofs.WG.Roaming
