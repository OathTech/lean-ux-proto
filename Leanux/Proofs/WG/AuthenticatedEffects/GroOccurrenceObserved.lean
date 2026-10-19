import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceCallback

/-! The native per-packet stack callback is the only new observation boundary.
Arbitrary batch callbacks retain their existing source; this wrapper is for the
actual stackFlush list traversal. Its neutral law recovers that whole source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll
open Leanux Leanux.WG Leanux.Proofs.Logged

def observed
    (step : {α : Type} → WG.M α → PrefixM E α)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (counter : SkbId → RxPacket → PrefixM E Bool)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (scope : GroOccurrence.Entry → PrefixM E Unit → PrefixM E Unit)
    (stack : List UInt8 → PrefixM E Unit) (pid : PeerId) (budget : Nat) : PrefixM E Nat :=
  sourceWith step enter leave counter consume
    (GroOccurrence.receiveWith liftPrefix (GroOccurrence.stackWith scope stack))
    (GroOccurrence.flushAllWith (GroOccurrence.stackWith scope stack)) pid budget

theorem observed_neutral
    (step : {α : Type} → WG.M α → PrefixM E α)
    (enter : SkbId → RxPacket → PrefixM E Nat) (leave : Nat → PrefixM E Unit)
    (counter : SkbId → RxPacket → PrefixM E Bool)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (stack : List UInt8 → PrefixM E Unit) (pid : PeerId) (budget : Nat) :
    observed step enter leave counter consume (fun _ body => body) stack pid budget =
      CandidatePoll.sourceWith step enter leave counter consume
        (napiGroReceivePrefix (fun bytes => bytes.forM stack))
        (napiGroFlushAllPrefix (fun bytes => bytes.forM stack)) pid budget := by
  have callback : GroOccurrence.stackWith (fun _ body => body) stack =
      fun entries => (entries.map GroOccurrence.Entry.bytes).forM stack :=
    funext (GroOccurrence.stack_neutral stack)
  unfold observed
  rw [callback]
  exact neutral step enter leave counter consume (fun bytes => bytes.forM stack) pid budget

theorem observed_matching (ρ : E → Option F) (scopeMap : Nat → Nat)
    (eg : SkbId → RxPacket → PrefixM E Nat)
    (ea : SkbId → RxPacket → PrefixM F Nat)
    (lg : Nat → PrefixM E Unit) (la : Nat → PrefixM F Unit)
    (sg : {α : Type} → WG.M α → PrefixM E α)
    (sa : {α : Type} → WG.M α → PrefixM F α)
    (cg : SkbId → RxPacket → PrefixM E Bool)
    (ca : SkbId → RxPacket → PrefixM F Bool)
    (ug : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (ua : PeerId → RxPacket → Endpoint → PrefixM F (Option (List UInt8)))
    (scope : GroOccurrence.Entry → PrefixM E Unit → PrefixM E Unit)
    (targetScope : GroOccurrence.Entry → PrefixM F Unit → PrefixM F Unit)
    (stack : List UInt8 → PrefixM E Unit) (targetStack : List UInt8 → PrefixM F Unit)
    (he : ∀ skb pkt, ProjectsPrefix ρ scopeMap (eg skb pkt) (ea skb pkt))
    (hl : ∀ token, ProjectsPrefix ρ id (lg token) (la (scopeMap token)))
    (hs : ∀ {α} (action : WG.M α), ProjectsPrefix ρ id (sg action) (sa action))
    (hc : ∀ skb pkt, ProjectsPrefix ρ id (cg skb pkt) (ca skb pkt))
    (hu : ∀ pid pkt ep, ProjectsPrefix ρ id (ug pid pkt ep) (ua pid pkt ep))
    (ht : ∀ bytes, ProjectsPrefix ρ id (stack bytes) (targetStack bytes))
    (hw : ∀ entry body targetBody, ProjectsPrefix ρ id body targetBody →
      ProjectsPrefix ρ id (scope entry body) (targetScope (entry.map scopeMap) targetBody))
    (pid : PeerId) (budget : Nat) :
    ProjectsPrefix ρ id (observed sg eg lg cg ug scope stack pid budget)
      (observed sa ea la ca ua targetScope targetStack pid budget) := by
  have callback := GroOccurrence.stack_matching ρ scopeMap scope targetScope stack targetStack ht hw
  exact matching ρ scopeMap eg ea lg la sg sa cg ca ug ua _ _ _ _ he hl hs hc hu
    (GroOccurrence.receive_matching ρ scopeMap _ _ callback)
    (GroOccurrence.flushAll_matching ρ scopeMap _ _ callback) pid budget

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll
