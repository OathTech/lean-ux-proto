import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationLabels

namespace Leanux.Proofs.WG.HandshakeSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes

/-- The precise completed-consume projection needed from campaign 2 H1.
`distinct` is `Noise.ConfirmationOrder.initialized_distinct`, transported by
`initialized_confirmationIds_labels`. `complete` is
`Noise.CounterConsume.initialized_event_label`, with its native confirmation
cut identified by `Noise.ConfirmationOrder.cut_unique`.

Both fields concern campaign 1's actual initialized completed-consume journal.
They include earlier completed events before a later outer Stop, but do not
cover a consumer that itself Stops after confirmation. No campaign-2 file is
imported, and no uniqueness of those stronger inner receipts is assumed. -/
structure H1InitializedCompletedConfirmation : Prop where
  distinct : ∀ (trace : Runner.Trace) (placeholders : Bool),
    (Confirmation.completedLabels (Confirmation.initializedHistory trace placeholders)).Nodup
  complete : ∀ (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool),
    Confirmation.initializedHistory trace placeholders =
      pre ++ .consumed occurrence id stamp r :: post →
    Confirmation.SourceCut r c →
    ∃ allocation,
      Confirmation.keyIdentityAt r.run.before r.packet.keypair = some allocation ∧
      Confirmation.completedLabel r = (if c.value then some allocation else none)

end Leanux.Proofs.WG.HandshakeSecurity
