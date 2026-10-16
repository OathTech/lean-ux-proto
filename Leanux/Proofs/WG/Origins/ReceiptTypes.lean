import Leanux.Proofs.Logged.NativeCapture

/-! Receipt data only. Operational validity and source contracts remain in the
session and RX origin modules; keeping these types low avoids a caller cycle. -/
namespace Leanux.Proofs.WG
open Leanux Leanux.WG Leanux.Proofs.Logged

namespace SessionOrigin
structure Context where
  slot : KeypairId
  state : Nat
  word : Option PeerId
  peer : Peer
  initiator : Bool

inductive Receipt where
  | allocation (word : Option PeerId) (run : WGRunWitness (Option KeypairId))
  | material (pid : PeerId) (run : WGRunWitness (Option Context))

end SessionOrigin

namespace RxOrigin
structure Admission where
  packet : RxPacket
  slot : SkbId

inductive Receipt where
  | allocation (packet : RxPacket) (run : WGRunWitness SkbId)
  | admission (msg : List UInt8) (src : SkbSource) (ds : Nat) (run : WGRunWitness (Option Admission))
  | decrypt (id : SkbId) (run : WGRunWitness (RxPacket × Option RxPacket))

end RxOrigin

end Leanux.Proofs.WG
