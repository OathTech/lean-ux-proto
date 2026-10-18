import Leanux.Proofs.WG.Index.ConfigurationIndexModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits Queues.RxCredits.DurableHolders

def IncomingCoreHeld (pid : PeerId) (g : WGWorld) : Prop :=
  Reached.Core g ∧ ∃ d p,g.dev=some d ∧ d.peers[pid]?=some p ∧ 1<p.refcount


end Leanux.Proofs.WG.Index
