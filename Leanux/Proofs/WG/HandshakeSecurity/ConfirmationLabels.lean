import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationInitialized

namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes

/-- Allocation identity at a particular native state, not a numeric slot. -/
def keyIdentityAt (w : WGWorld) (kid : KeypairId) : Option Nat := do
  let d ← w.dev
  (d.keypairs[kid]?).map Keypair.internalId

/-- H1's optional pending-key label, projected directly from the original
completed consumer's entry. A missing key supplies no allocation identity. -/
def completedLabel (r : RxDisposition.ConsumeReceipt) : Option Nat := do
  let d ← r.run.before.dev
  let p ← d.peers[r.peer]?
  if p.keypairNext == some r.packet.keypair then
    (d.keypairs[r.packet.keypair]?).map Keypair.internalId
  else none

def eventLabel : RxHistory.Event → Option Nat
  | .consumed _ _ _ r => completedLabel r
  | _ => none

def completedLabels (h : List RxHistory.Event) : List Nat := h.filterMap eventLabel

def initializedHistory (trace : Runner.Trace) (placeholders : Bool) : List RxHistory.Event :=
  (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2

theorem completedLabels_at (pre post : List RxHistory.Event) (n id : Nat)
    (stamp : PacketStamp) (r : RxDisposition.ConsumeReceipt) :
    completedLabels (pre ++ .consumed n id stamp r :: post) =
      completedLabels pre ++ (completedLabel r).toList ++ completedLabels post := by
  simp only [completedLabels, List.filterMap_append, List.filterMap_cons, eventLabel]
  cases completedLabel r <;> simp

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation
