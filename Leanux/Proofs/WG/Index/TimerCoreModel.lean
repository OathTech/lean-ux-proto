import Leanux.Proofs.WG.Index.StagingIndexModel
import Leanux.Proofs.WG.Index.ReachedIndexBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.TimerCore
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

def Ready (w : WGWorld) : Prop := CurrentSlots.Inv w ∧ Reached.Core w

def Held (pid : PeerId) (w : WGWorld) : Prop :=
  Ready w ∧ ∃ d p, w.dev=some d ∧ d.peers[pid]?=some p ∧ 1<p.refcount

end Leanux.Proofs.WG.Index.TimerCore
