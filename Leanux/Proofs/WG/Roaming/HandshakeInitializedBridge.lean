import Leanux.Proofs.WG.Roaming.HandshakeInitializedModel
import Leanux.Proofs.WG.Roaming.HandshakeOverlayTransportSource
import Leanux.Proofs.WG.Roaming.HandshakeAttemptInitializedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.HandshakeOverlay
open Leanux Leanux.Proofs.Logged

/-- The concrete original-source observer with the authenticated receive callback. -/
def initializedHistory (trace : Runner.Trace) (placeholders : Bool) : List RxEvent :=
  HandshakeAttemptTransport.Initialized.history receiver trace placeholders

def extractOccurrence : RxEvent × Nat → Option Occurrence
  | (.inr r,position) => some ⟨position,r⟩
  | _ => none

def initializedAttempts (trace : Runner.Trace) (placeholders : Bool) : List Occurrence :=
  (initializedHistory trace placeholders).zipIdx.filterMap extractOccurrence

/-- Actual emitted event at its exact index, also when a later operation stops. -/
def Occurrence.Occurs (trace : Runner.Trace) (placeholders : Bool) (q : Occurrence) : Prop :=
  ∃ pre post, initializedHistory trace placeholders = pre ++ .inr q.attempt :: post ∧
    q.position = pre.length

/-- A single run supplies both the original outcome and its emitted attempts. -/
def initializedInspection (trace : Runner.Trace) (placeholders : Bool) : InitializedInspection :=
  let run := runPrefixOuter (HandshakeAttemptTransport.Initialized.observed receiver trace placeholders) []
  ⟨run.1,run.2.zipIdx.filterMap extractOccurrence⟩

end Leanux.Proofs.WG.Roaming.HandshakeOverlay
