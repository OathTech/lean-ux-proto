import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationFreeFrontier
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationCompletionTickets

/-! Fixed incoming ticket partition for the exact stopped native free walk. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.FreeFrontier
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity.Staged.Origins

theorem stopped_tickets (free : SkbId → PrefixM E Unit) (item : List SkbId)
    (w : World) (h tail : List E) (stop : Stop)
    (run : runPrefix (walk free item) w h = (.error stop,tail))
    (R : α → SkbId → Prop) (tickets : List α)
    (aligned : Aligned R tickets item) (unique : tickets.Nodup) :
    ∃ done skb remaining middle history prior ticket later,
      item = done ++ skb :: remaining ∧ tickets = prior ++ ticket :: later ∧
      Aligned R prior done ∧ R ticket skb ∧ Aligned R later remaining ∧
      prior.Nodup ∧ later.Nodup ∧ ticket ∉ prior ∧ ticket ∉ later ∧
      (∀ token ∈ prior, token ∉ later) ∧ Steps free done w h middle history ∧
      runPrefix (free skb) middle history = (.error stop,tail) := by
  obtain ⟨done,skb,remaining,middle,history,split,steps,failed⟩ :=
    walk_stopped free item w h tail stop run
  obtain ⟨prior,ticket,later,ticketSplit,alignedPrior,relation,suffix⟩ :=
    CompletionFrontier.aligned_split R done skb remaining tickets (split ▸ aligned)
  have disjoint := List.nodup_append.mp (ticketSplit ▸ unique)
  have tailUnique := List.nodup_cons.mp disjoint.2.1
  refine ⟨done,skb,remaining,middle,history,prior,ticket,later,split,ticketSplit,
    alignedPrior,relation,suffix,disjoint.1,tailUnique.2,?_,tailUnique.1,?_,steps,failed⟩
  · intro member
    exact disjoint.2.2 ticket member ticket (List.mem_cons_self ..) rfl
  · intro token member other
    exact disjoint.2.2 token member token (List.mem_cons_of_mem _ other) rfl

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.FreeFrontier
