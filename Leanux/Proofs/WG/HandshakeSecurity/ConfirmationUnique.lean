import Leanux.Proofs.WG.HandshakeSecurity.ConfirmationH1Initialized

namespace Leanux.Proofs.WG.HandshakeSecurity.Confirmation
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues Lifetimes

/-- The received packet has earlier native authentication, and its actual
confirmation contributes its allocation identity at most once to the completed
consumer journal. The stopped-consumer inner journal is a separate scope. -/
def AuthenticatedUnique (pre post : List RxHistory.Event) (id : SkbId)
    (r : RxDisposition.ConsumeReceipt) : Prop :=
  AuthenticatedSource pre id r ∧
  ∃ (c : WGRunWitness Bool) (allocation : Nat),
    SourceCut r c ∧ keyIdentityAt r.run.before r.packet.keypair = some allocation ∧
    completedLabel r = (if c.value then some allocation else none) ∧
    (c.value = true → allocation ∉ completedLabels pre ∧ allocation ∉ completedLabels post)

theorem initialized_authenticated_unique (H1 : H1InitializedCompletedConfirmation)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : initializedHistory trace placeholders =
      pre ++ .consumed occurrence id stamp r :: post) :
    AuthenticatedUnique pre post id r := by
  have authenticated := initialized_authenticated trace placeholders pre post occurrence id stamp r position
  refine ⟨authenticated, ?_⟩
  obtain ⟨_, _, _, _, _, _, c, _, _, _, _, _, _, _, _, _, cut⟩ := authenticated
  obtain ⟨allocation, resident, label⟩ :=
    H1.complete trace placeholders pre post occurrence id stamp r c position cut
  refine ⟨c, allocation, cut, resident, label, ?_⟩
  intro confirmed
  have distinct := H1.distinct trace placeholders
  rw [position, completedLabels_at] at distinct
  rw [confirmed] at label
  rw [label] at distinct
  simp only [List.append_assoc] at distinct
  obtain ⟨_, right, apart⟩ := List.nodup_append.mp distinct
  refine ⟨?_, (List.nodup_cons.mp right).1⟩
  intro member
  exact apart allocation member allocation (by simp) rfl

end Leanux.Proofs.WG.HandshakeSecurity.Confirmation
