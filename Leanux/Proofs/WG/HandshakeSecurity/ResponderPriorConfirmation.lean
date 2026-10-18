import Leanux.Proofs.WG.HandshakeSecurity.ResponderInitialized

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.Initialized
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- A concrete earlier authenticated receive whose native confirmation returned
true for this allocation. The event position gives strict temporal precedence. -/
def PriorConfirmation (pre : List RxHistory.Event) (allocation : Nat) : Prop :=
  ∃ left right occurrence id stamp, ∃ (r : RxDisposition.ConsumeReceipt) (c : WGRunWitness Bool),
    pre = left ++ .consumed occurrence id stamp r :: right ∧
    Confirmation.AuthenticatedSource left id r ∧ Confirmation.SourceCut r c ∧
    c.value = true ∧ Confirmation.keyIdentityAt c.before r.packet.keypair = some allocation

theorem earlier_authentication (slots : H1ConfirmationEdges)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (event : RxHistory.Event)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 = pre ++ event :: post)
    (allocation : Nat) (member : allocation ∈ Confirmation.completedLabels pre) :
    PriorConfirmation pre allocation := by
  obtain ⟨prior, inside, label⟩ := List.mem_filterMap.mp member
  cases prior <;> try cases label
  case consumed occurrence id stamp r =>
    change Confirmation.completedLabel r = some allocation at label
    obtain ⟨left,right,split⟩ := List.mem_iff_append.mp inside
    have oldPosition : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
        left ++ .consumed occurrence id stamp r :: (right ++ event :: post) := by
      rw [position,split]
      simp only [List.append_assoc,List.cons_append]
    have authenticated := Confirmation.initialized_authenticated trace placeholders
      left (right ++ event :: post) occurrence id stamp r oldPosition
    have authenticatedCopy := authenticated
    obtain ⟨_,_,_,_,_,_,c,_,_,_,_,_,_,_,_,_,cut⟩ := authenticated
    have sourceLabel := completed_label_cut slots r c cut
    rw [label,confirmedAt_identity] at sourceLabel
    cases accepted : c.value with
    | false => simp [accepted] at sourceLabel
    | true =>
      cases identity : Confirmation.keyIdentityAt c.before r.packet.keypair with
      | none => simp [accepted,identity] at sourceLabel
      | some value =>
        have equal : value = allocation := by simpa [accepted,identity] using sourceLabel.symm
        subst value
        exact ⟨left,right,occurrence,id,stamp,r,c,split,authenticatedCopy,cut,accepted,identity⟩

/-- Every current responder at a captured initialized consumer entry has a
strictly earlier authenticated receive that really confirmed that allocation.
This derives the history premise from execution; it makes no packet-encryption
claim and does not require H1's separate completed-label uniqueness hypothesis. -/
theorem current_has_earlier_authenticated_confirmation
    (H1 : H1ResponderCurrentEdges) (slots : H1ConfirmationEdges)
    (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RxHistory.Event) (occurrence : Nat) (id : SkbId) (stamp : PacketStamp)
    (r : RxDisposition.ConsumeReceipt)
    (position : (runPrefixOuter (RxHistory.executeTraceHistory trace placeholders) []).2 =
      pre ++ .consumed occurrence id stamp r :: post)
    (pid : PeerId) (core : KeyCore) (resident : current r.run.before pid = some core)
    (responder : core.initiator = false) : PriorConfirmation pre core.allocation :=
  earlier_authentication slots trace placeholders pre post _ position core.allocation
    (current_has_prior_confirmation H1 slots trace placeholders pre post occurrence id stamp r
      position pid core resident responder)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.Initialized
