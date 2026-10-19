import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationCompletionFrontier
import Leanux.Proofs.WG.TransmitSecurity.StagedOrigins

/-! The stopped completion frontier partitions one fixed incoming ticket
list. The current ticket is retained separately because its iteration may
already contain a socket handoff before a later stop. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.CompletionFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
open TransmitSecurity.Staged.Origins

theorem aligned_split (R : α → β → Prop) (done : List β) (current : β) (remaining : List β)
    (tickets : List α) (aligned : Aligned R tickets (done ++ current :: remaining)) :
    ∃ prior ticket later, tickets = prior ++ ticket :: later ∧
      Aligned R prior done ∧ R ticket current ∧ Aligned R later remaining := by
  induction done generalizing tickets with
  | nil =>
    cases aligned with
    | cons relation rest => exact ⟨[],_,_,rfl,.nil,relation,rest⟩
  | cons first rest ih =>
    cases aligned with
    | cons relation aligned =>
      obtain ⟨prior,ticket,later,split,alignedPrior,current,remaining⟩ := ih _ aligned
      exact ⟨_ :: prior,ticket,later,by simp only [split,List.cons_append],
        .cons relation alignedPrior,current,remaining⟩

/-- The earlier/current/later tickets form a disjoint partition of the
original incoming list. This proves no disappearance at a stopped traversal;
the current ticket's actual send history still decides its terminal status. -/
theorem stopped_tickets (o : CompletionEffects.Ops E) (pid : PeerId) (item : List SkbId)
    (flag : Bool) (w : World) (h tail : List E) (stop : Stop)
    (run : runPrefix (walk o pid item flag) w h = (.error stop,tail))
    (R : α → SkbId → Prop) (tickets : List α)
    (aligned : Aligned R tickets item) (unique : tickets.Nodup) :
    ∃ done id remaining current middle history prior ticket later,
      item = done ++ id :: remaining ∧
      tickets = prior ++ ticket :: later ∧
      Aligned R prior done ∧ R ticket id ∧ Aligned R later remaining ∧
      prior.Nodup ∧ later.Nodup ∧ ticket ∉ prior ∧ ticket ∉ later ∧
      (∀ token ∈ prior, token ∉ later) ∧
      Steps o pid done flag w h current middle history ∧
      runPrefix (iteration o pid id current) middle history = (.error stop,tail) := by
  obtain ⟨done,id,remaining,current,middle,history,split,steps,failed⟩ :=
    walk_stopped o pid item flag w h tail stop run
  obtain ⟨prior,ticket,later,ticketSplit,alignedPrior,relation,suffix⟩ :=
    aligned_split R done id remaining tickets (split ▸ aligned)
  have disjoint := List.nodup_append.mp (ticketSplit ▸ unique)
  have tailUnique := List.nodup_cons.mp disjoint.2.1
  refine ⟨done,id,remaining,current,middle,history,prior,ticket,later,split,ticketSplit,
    alignedPrior,relation,suffix,disjoint.1,tailUnique.2,?_,tailUnique.1,?_,steps,failed⟩
  · intro member
    exact disjoint.2.2 ticket member ticket (List.mem_cons_self ..) rfl
  · intro token member other
    exact disjoint.2.2 token member token (List.mem_cons_of_mem _ other) rfl

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.CompletionFrontier
