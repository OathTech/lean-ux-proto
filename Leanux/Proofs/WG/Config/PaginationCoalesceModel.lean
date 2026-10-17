import Leanux.Proofs.WG.Config.SocketReadbackModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- Actual continuation DATA messages followed by DONE. Split bits describe
whether another continuation follows, without restricting the IP values. -/
def paginationTailMessages (d : Device) (p : Peer) (nodes : NodeId → AipNode) :
    List (List NodeId) → List NlMessage
  | [] => [.done 2 0]
  | ids :: rest =>
    .data 2 (deviceFixedAttrs d) (some [{suffixLast p nodes ids with split := !rest.isEmpty}]) ::
      paginationTailMessages d p nodes rest

def paginationMessages (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (rest : List (List NodeId)) : List NlMessage :=
  .data 2 (deviceFixedAttrs d) (some [{socketFirstPeer p nodes front with split := !rest.isEmpty}]) ::
    paginationTailMessages d p nodes rest

end Leanux.Proofs.WG.Config
