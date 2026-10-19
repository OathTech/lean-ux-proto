import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleasePollSource

/-! Projection-specific history frames for the complete poll source. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem poll_choice (ρ : E → Option F) (p : Prop) [Decidable p]
    (g t : PrefixM E α) (hg : HistoryFrame ρ g) (ht : HistoryFrame ρ t) :
    HistoryFrame ρ (if p then g else t) := by split <;> assumption

private theorem poll_range (ρ : E → Option F) (r : Std.Legacy.Range) (b : β)
    (f : Nat → β → PrefixM E (ForInStep β)) (h : ∀ n b, HistoryFrame ρ (f n b)) :
    HistoryFrame ρ (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact HistoryFrame.forIn _ _ _ h

theorem poll_frame (ρ : E → Option F)
    (step : {α : Type} → WG.M α → PrefixM E α) (release : Option PeerId → PrefixM E Unit)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (counter : SkbId → RxPacket → PrefixM E Bool)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option Key))
    (receive : GroOccurrence.Buffer → GroOccurrence.Entry → PrefixM E GroOccurrence.Buffer)
    (flush : GroOccurrence.Buffer → PrefixM E Unit)
    (hs : ∀ {α} (a : WG.M α), HistoryFrame ρ (step a))
    (hp : ∀ peer, HistoryFrame ρ (release peer))
    (he : ∀ skb pkt, HistoryFrame ρ (enter skb pkt))
    (hl : ∀ scope, HistoryFrame ρ (leave scope))
    (hc : ∀ skb pkt, HistoryFrame ρ (counter skb pkt))
    (hu : ∀ pid pkt ep, HistoryFrame ρ (consume pid pkt ep))
    (hr : ∀ gro entry, HistoryFrame ρ (receive gro entry))
    (hf : ∀ gro, HistoryFrame ρ (flush gro)) (pid : PeerId) (budget : Nat) :
    HistoryFrame ρ (pollWith step release enter leave counter consume receive flush pid budget) := by
  unfold pollWith
  repeat' first
    | with_reducible exact hs _
    | with_reducible exact hp _
    | with_reducible exact he _ _
    | with_reducible exact hl _
    | with_reducible exact hc _ _
    | with_reducible exact hu _ _ _
    | with_reducible exact hr _ _
    | with_reducible exact hf _
    | with_reducible exact HistoryFrame.pure ρ _
    | with_reducible apply HistoryFrame.bind
    | with_reducible apply HistoryFrame.forIn
    | with_reducible apply poll_range ρ
    | with_reducible apply poll_choice ρ
    | split
    | contradiction
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
