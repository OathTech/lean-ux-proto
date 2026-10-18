import Leanux.Proofs.WG.Index.OwnerReferenceFrames
import Leanux.Proofs.WG.Index.RxQueueOwnerFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.DataIngress
open Leanux Leanux.WG Noise Std.Do Leanux.Proofs.Framing Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits

def Held (P : WGWorld → Prop) (kid : KeypairId) (pid : PeerId) (w : WGWorld) : Prop :=
  P w ∧ ∃d p k,w.dev=some d ∧ d.peers[pid]?=some p ∧ 1<p.refcount ∧
    d.keypairs[kid]?=some k ∧ 1<k.refcount

def Credit (P : WGWorld → Prop) (peer : Option PeerId) (w : WGWorld) : Prop :=
  P w ∧ ∀pid,peer=some pid → ∃d p,w.dev=some d ∧ d.peers[pid]?=some p ∧ 1<p.refcount

abbrev DeviceSafe (predicate : Device → Prop) (w : WGWorld) : Prop :=
  ∀d,w.dev=some d → predicate d

end Leanux.Proofs.WG.Index.DataIngress
