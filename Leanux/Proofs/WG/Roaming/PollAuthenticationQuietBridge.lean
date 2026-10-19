import Leanux.Proofs.WG.Roaming.PollAuthenticationCertificateBridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.PollAuthentication
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Queues Lifetimes
variable {α : Type}

def PublicSafe (h : List RxHistory.Event) : Prop :=
  PublicationJoint.Safe h ∧ Safe h

def endpointSensitive : RxHistory.Event → Option Unit
  | .checkedEndpoint .. => some ()
  | _ => none

end Leanux.Proofs.WG.Roaming.PollAuthentication
