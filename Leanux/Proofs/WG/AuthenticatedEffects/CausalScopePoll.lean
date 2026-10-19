import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeSplit
import Leanux.Proofs.WG.AuthenticatedEffects.CausalScopeReceive
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames

/-! The native poll brackets each candidate with the returned scope token. A
candidate is not thereby authenticated: this proves only well-formed nesting. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem poll_source
    (release : Option PeerId → PrefixM Event Unit)
    (counter : SkbId → RxPacket → PrefixM Event Bool)
    (consumer : PeerId → RxPacket → Endpoint → PrefixM Event (Option (List UInt8)))
    (receive : GroOccurrence.Buffer → GroOccurrence.Entry → PrefixM Event GroOccurrence.Buffer)
    (flush : GroOccurrence.Buffer → PrefixM Event Unit)
    (hl : ∀ peer, ProductSafe (release peer))
    (hc : ∀ skb pkt, ProductSafe (counter skb pkt))
    (hu : ∀ pid pkt ep, ProductSafe (consumer pid pkt ep))
    (hr : ∀ gro entry, ProductSafe (receive gro entry))
    (hf : ∀ gro, ProductSafe (flush gro))
    (pid : PeerId) (budget : Nat) :
    ProductSafe (RetirementSecurity.NestedPeerRelease.pollWith (fun action => liftWGObserver (liftWGPrefix action)) release
      (CausalSources.candidateEnter Event.scope) (CausalScope.leavePrefix Event.scope)
      counter consumer receive flush pid budget) := by
  unfold RetirementSecurity.NestedPeerRelease.pollWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | exact hl _
    | exact hc _ _
    | exact hu _ _ _
    | exact hr _ _
    | exact hf _
    | (scope_first_head CausalSources.candidateEnter; apply universal; intro frames; apply enter_bind)
    | scope_flow_step
    | scope_product_step

private theorem batch_stack (entries : List GroOccurrence.Entry) :
    ProductSafe (GroOccurrence.stackWith hooks.stackInput (Driver.stackObserved hooks) entries) := by
  unfold GroOccurrence.stackWith
  induction entries with
  | nil => exact product_pure ()
  | cons entry entries ih =>
    exact product_bind (product_scope (.stackInput entry) _ (fun _ => stack_input entry.bytes))
      (fun _ => ih)

theorem native_poll (pid : PeerId) (budget : Nat) : ProductSafe (Driver.nativePollObserved hooks pid budget) := by
  unfold Driver.nativePollObserved
  apply poll_source
  · intro peer; exact product_state _ (peer_release peer)
  · intro skb packet; exact old_product _
  · intro peer packet endpoint; exact product_state _ (consume peer packet endpoint)
  · intro gro entry frames
    exact GroOccurrence.receive_preserves
      (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
      (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
      _ (fun entries => batch_stack entries frames) gro entry
  · intro gro frames
    exact GroOccurrence.flushAll_preserves
      (I := fun h _ => CausalScope.stack (h.filterMap scope?) = .ok frames)
      (S := CausalScope.WellFormed scope?) (fun _ _ ready => ⟨frames,ready⟩)
      _ (fun entries => batch_stack entries frames) gro

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.ScopeBalance
