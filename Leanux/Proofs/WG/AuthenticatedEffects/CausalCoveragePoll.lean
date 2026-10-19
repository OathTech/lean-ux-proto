import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageSplit
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageReceive
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames

/-! The actual candidate source supplies a nonempty context to consume, and
the actual GRO callback establishes its inherited packet scope. The native
replay branches remain unchanged; scope presence alone is not authentication. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Lifetimes
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem poll_source
    (counter : SkbId → RxPacket → PrefixM Event Bool)
    (consumer : PeerId → RxPacket → Endpoint → PrefixM Event (Option (List UInt8)))
    (receive : GroOccurrence.Buffer → GroOccurrence.Entry → PrefixM Event GroOccurrence.Buffer)
    (flush : GroOccurrence.Buffer → PrefixM Event Unit)
    (hc : ∀ skb pkt, ProductClosed (counter skb pkt))
    (hu : ∀ pid pkt ep, ProductGuarded (consumer pid pkt ep))
    (hr : ∀ gro entry, ProductClosed (receive gro entry))
    (hf : ∀ gro, ProductClosed (flush gro))
    (pid : PeerId) (budget : Nat) :
    ProductAt frames (GroOccurrencePoll.sourceWith (fun action => liftWGObserver (liftWGPrefix action))
      (CausalSources.candidateEnter Event.scope) (CausalScope.leavePrefix Event.scope)
      counter consumer receive flush pid budget) := by
  unfold GroOccurrencePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | exact hc _ _ _
    | exact hu _ _ _ _ (by simp)
    | exact hr _ _ _
    | exact hf _ _
    | (coverage_first_head CausalSources.candidateEnter; apply enter_bind)
    | coverage_flow_step
    | coverage_product_step

private theorem batch_stack (entries : List GroOccurrence.Entry) :
    ProductAt frames (GroOccurrence.stackWith hooks.stackInput (Driver.stackObserved hooks) entries) := by
  unfold GroOccurrence.stackWith
  induction entries with
  | nil => exact product_pure ()
  | cons entry entries ih =>
    exact product_bind (product_scope (.stackInput entry) _ (fun _ _ live => stack_input entry.bytes live) frames)
      (fun _ => ih)

theorem native_poll (pid : PeerId) (budget : Nat) : ProductAt frames (Driver.nativePollObserved hooks pid budget) := by
  unfold Driver.nativePollObserved GroOccurrencePoll.observed
  apply poll_source
  · intro skb packet frames; exact counter skb packet
  · intro peer packet endpoint frames live; exact product_state _ (consume peer packet endpoint live)
  · intro gro entry frames
    exact GroOccurrence.receive_preserves (I := fun h _ => Inv frames h) (S := Safe)
      (fun _ _ ready => ready.1) _ batch_stack gro entry
  · intro gro frames
    exact GroOccurrence.flushAll_preserves (I := fun h _ => Inv frames h) (S := Safe)
      (fun _ _ ready => ready.1) _ batch_stack gro

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
