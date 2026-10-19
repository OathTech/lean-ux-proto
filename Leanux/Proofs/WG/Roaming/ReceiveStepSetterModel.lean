import Leanux.Proofs.WG.Roaming.ReceiveStepRemoteModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.ReceiveStepRemote
open Leanux Leanux.WG

/-- The single successful handshake prefix selected by a completed receive
call. Rejection and non-handshake messages select no setter. -/
def Call.setter (call : Call) : Option (PeerId × (Nat × Nat × Nat × Nat)) :=
  match call.receipt with
  | .initiation (.ok (some cut,_)) =>
    some (cut.consumed.pid,destination (sourceEndpoint call.source))
  | .response (.ok (some cut,_)) =>
    some (cut.consumed.input.pid,destination (sourceEndpoint call.source))
  | _ => none

def Observation.setter (q : Observation) : Option (PeerId × (Nat × Nat × Nat × Nat)) :=
  q.call.bind Call.setter

/-- Apply a selected caller's destination; no selected caller leaves the
map alone. Later deletion is expressed separately by RemoteRetained. -/
def setterMap (entry : RemoteMap) :
    Option (PeerId × (Nat × Nat × Nat × Nat)) → RemoteMap
  | none => entry
  | some (pid,remote) => updateRemote entry pid remote

end Leanux.Proofs.WG.Roaming.ReceiveStepRemote
