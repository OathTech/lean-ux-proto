import Leanux.Proofs.WG.Config.GetterScalarSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
theorem sender_keeps (entry : Campaign2.Snapshot) (pid : PeerId) :
    Campaign2.Ensures (handshakeSendWorker pid) (Keeps entry) (fun _=>Keeps entry) :=
  worker (observation entry) pid

theorem clear_keeps (entry : Campaign2.Snapshot) (pid : PeerId) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid) (Keeps entry) (fun _=>Keeps entry) :=
  clear_worker (observation entry) pid

theorem drain_keeps (entry : Campaign2.Snapshot) (upTo : Option PeerId) :
    Campaign2.Ensures (drainHandshakeSendWq upTo) (Keeps entry) (fun _=>Keeps entry) :=
  drain (observation entry) upTo

theorem timers_keeps (entry : Campaign2.Snapshot) (pid : PeerId) :
    Campaign2.Ensures (timersStop pid) (Keeps entry) (fun _=>Keeps entry) :=
  timers_stop (observation entry) pid

theorem remove_keeps (entry : Campaign2.Snapshot) (peer : Option PeerId) :
    Campaign2.Ensures (peerRemove peer) (Keeps entry) (fun _=>Keeps entry) :=
  remove (observation entry) peer

theorem remove_all_keeps (entry : Campaign2.Snapshot) :
    Campaign2.Ensures peerRemoveAll (Keeps entry) (fun _=>Keeps entry) :=
  remove_all (observation entry)

end Leanux.Proofs.WG.Config.GetterScalar
