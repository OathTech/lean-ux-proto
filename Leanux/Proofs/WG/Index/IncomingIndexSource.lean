import Leanux.Proofs.WG.Index.IncomingIndexFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do
open Queues.RxCredits

theorem consumeInitiation_incomingIndex (retired : Reservations) (msg : List UInt8) :
    Ensures (consumeInitiation msg) (IncomingIndexSafe retired)
      (fun _ => IncomingIndexSafe retired) :=
  consumeInitiation_preserves_held_source msg (IncomingIndexSafe retired)
    (IncomingIndexHeld retired) (fun _ _ h => h.1)
    (pubkeyLookup_incomingIndexHeld retired) (peerPut_incomingIndexHeld retired)
    (fun pid f _ count slots stamp dead =>
      modifyPeer_incomingIndexHeld retired pid f count slots stamp dead)

theorem consumeResponse_incomingIndex (retired : Reservations) (msg : List UInt8) :
    Ensures (consumeResponse msg) (IncomingIndexSafe retired)
      (fun _ => IncomingIndexSafe retired) :=
  consumeResponse_preserves_held_source msg (IncomingIndexSafe retired)
    (IncomingIndexHeld retired) (fun _ _ h => h.1)
    (indexLookup_handshake_incomingIndexHeld retired) (peerPut_incomingIndexHeld retired)
    (fun pid f _ count slots stamp dead =>
      modifyPeer_incomingIndexHeld retired pid f count slots stamp dead)
end Leanux.Proofs.WG.Index
