import Leanux.Proofs.WG.Index.TransmitRuleSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TransmitCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

def richView (w : WGWorld) :=
  (w.dev.map TimerDiscipline.tableCursor,StagingRich.peerMap w,StagingRich.keyMap w,w.keypairCounter)

end Leanux.Proofs.WG.Index.TransmitCore
