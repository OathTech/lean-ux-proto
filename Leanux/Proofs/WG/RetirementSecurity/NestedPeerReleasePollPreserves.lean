import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleasePollSource
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames

/-! The actual native poll transports its invariant through the exposed
peer release as well as the original packet and GRO callbacks. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects AuthenticatedEffects.GroOccurrencePoll
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem poll_preserves
    (I : List E → World → Prop) (S : List E → Prop) (safe : ∀ h w, I h w → S h)
    (step : {α : Type} → WG.M α → PrefixM E α)
    (release : Option PeerId → PrefixM E Unit)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (counter : SkbId → RxPacket → PrefixM E Bool)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : GroOccurrence.Buffer → GroOccurrence.Entry → PrefixM E GroOccurrence.Buffer)
    (flush : GroOccurrence.Buffer → PrefixM E Unit)
    (hs : ∀ {α} (action : WG.M α), PrefixPreserves I S (step action))
    (hp : ∀ peer, PrefixPreserves I S (release peer))
    (he : ∀ skb pkt, PrefixPreserves I S (enter skb pkt))
    (hl : ∀ token, PrefixPreserves I S (leave token))
    (hc : ∀ skb pkt, PrefixPreserves I S (counter skb pkt))
    (hu : ∀ pid pkt ep, PrefixPreserves I S (consume pid pkt ep))
    (hr : ∀ gro entry, PrefixPreserves I S (receive gro entry))
    (hf : ∀ gro, PrefixPreserves I S (flush gro))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves I S (pollWith step release enter leave counter consume receive flush pid budget) := by
  unfold pollWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | exact hs _
    | exact hp _
    | exact he _ _
    | exact hl _
    | exact hc _ _
    | exact hu _ _ _
    | exact hr _ _
    | exact hf _
    | exact PrefixPreserves.pure safe _
    | (gro_frame_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ safe)
    | (gro_frame_head Bind.bind; apply PrefixPreserves.bind)
    | (gro_frame_head ite; apply PrefixPreserves.ite)
    | (maintenance_intro; try dsimp only)
    | (split; all_goals try simp_all only [])

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
