import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionInitialized
import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialFinal
import Leanux.Proofs.WG.TransmitSecurity.JournalResponderProjection

/-! Exact final-observer transport for consumed pending allocation tickets.
The projection preserves each inner confirmation even if its receive later
stops; endpoint erasure is not used to join histories. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity AuthenticatedEffects

abbrev finalHistory (trace : Runner.Trace) (placeholders : Bool) :=
  (runPrefixOuter (CausalJournal.execute trace placeholders) []).2.filterMap CausalJournal.old?

theorem journal (facts : H1DriverFrames) (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((runPrefixOuter (Journal.execute trace placeholders) []).2.filterMap Journal.responder?) := by
  have projected := congrArg Prod.snd (Journal.ResponderProjection.execute trace placeholders [])
  simp only [List.filterMap_nil] at projected
  rw [←projected]
  exact initialized facts trace placeholders

theorem final (facts : H1DriverFrames) (trace : Runner.Trace) (placeholders : Bool) :
    Safe ((finalHistory trace placeholders).filterMap Journal.responder?) := by
  have projected := congrArg Prod.snd (CausalJournal.execute_projects trace placeholders [])
  simp only [List.filterMap_nil] at projected
  unfold finalHistory
  rw [←projected]
  exact journal facts trace placeholders

theorem confirmation_label (pid : PeerId) (kid : KeypairId) (r : WGRunWitness Bool) (allocation : Nat)
    (accepted : r.value = true) (resident : keypairResidents r.before kid = some allocation) :
    (Responder.DriverCuts.Event.confirmed pid kid r).labels = [allocation] := by
  change Responder.confirmedAt r.before kid r.value = [allocation]
  rw [←label_matches]
  simp only [label,accepted,↓reduceIte,resident,Option.toList_some]

/-- Two successful inner native promotions in source order consume distinct
allocation identities, including promotions whose enclosing consumer stops. -/
theorem once (facts : H1DriverFrames) (trace : Runner.Trace) (placeholders : Bool)
    (pre between post : List Journal.Event) (pid other : PeerId) (kid next : KeypairId)
    (r s : WGRunWitness Bool) (first second : Nat)
    (position : finalHistory trace placeholders = pre ++ Journal.Event.responder (.confirmed pid kid r) ::
      between ++ Journal.Event.responder (.confirmed other next s) :: post)
    (accepted₁ : r.value = true) (accepted₂ : s.value = true)
    (resident₁ : keypairResidents r.before kid = some first)
    (resident₂ : keypairResidents s.before next = some second) : first ≠ second := by
  have distinct := final facts trace placeholders
  change (Responder.DriverCuts.labels ((finalHistory trace placeholders).filterMap Journal.responder?)).Nodup at distinct
  rw [position] at distinct
  simp only [List.filterMap_append,List.filterMap_cons,Journal.responder?,
    Responder.DriverCuts.labels, List.flatMap_append,List.flatMap_cons,
    confirmation_label pid kid r first accepted₁ resident₁,
    confirmation_label other next s second accepted₂ resident₂,List.singleton_append] at distinct
  simp only [List.append_assoc,List.cons_append] at distinct
  have rest := (List.nodup_append.mp distinct).2.1
  have absent := (List.nodup_cons.mp rest).1
  intro equal
  apply absent
  apply List.mem_append.mpr
  right
  exact List.mem_cons.mpr (Or.inl equal)


/-- Full responder-key discipline on one exact source journal. Distinct labels
state per-allocation promotion uniqueness; positional receive certificates
supply authenticated causes; each actual responder AEAD requires an earlier
successful confirmation of its own allocation. -/
def Discipline (history : List Journal.Event) : Prop :=
  Safe (history.filterMap Journal.responder?) ∧
  ReceiveMaterial.Confirmation.Safe history ∧
  ∀ pre post r, history = pre ++ Journal.Event.encrypted r :: post →
    r.cipher.keyRead.value.iAmTheInitiator = false →
    r.Valid ∧ ReceiveMaterial.PriorAllocationConfirmation pre r.cipher.keyRead.value.internalId

/-- All three clauses use the same initialized final observer and retain inner
confirmation receipts through later Stop. Only the explicitly named native C2
frame and rotation contracts remain hypotheses. -/
theorem discipline (facts : H1DriverFrames) (rotation : H1ResponderCurrentEdges)
    (trace : Runner.Trace) (placeholders : Bool) : Discipline (finalHistory trace placeholders) := by
  refine ⟨final facts trace placeholders,(ReceiveMaterial.final_history trace placeholders).2,?_⟩
  intro pre post r position responder
  exact ReceiveMaterial.final_encryption rotation trace placeholders pre post r position responder

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
