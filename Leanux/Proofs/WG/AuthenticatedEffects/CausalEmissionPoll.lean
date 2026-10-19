import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionReceive
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionProductSource
import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceFrames

/-! The actual poll loop preserves ordered append receipts. Its arbitrary
stack callback retains an explicit emission contract; native tagged delivery
uses the same loop and scopes, including buffered GRO entries. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes TransmitSecurity
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem candidate_enter (skb : SkbId) (packet : RxPacket) : ProductSafe (hooks.candidateEnter skb packet) := by
  intro w h hi
  exact ⟨[.scope (.entered ⟨h.length,.candidate skb packet⟩)],rfl,True.intro,hi.quiet _ rfl⟩

theorem candidate_leave (token : Nat) : ProductSafe (hooks.candidateLeave token) := product_emit _ rfl

private theorem peek_spec (P : List SentDatagram → Prop) {α : Type} (queue : PrevQueue α) :
    Preserves (fun w => P w.sent) queue.peek := (EmissionFrames.peek queue).wp P

open Lean Meta Elab Tactic in
elab "emission_poll_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``ProductSafe do throwError "not a product emission contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back!.consumeMData else action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do throwError "different source head"

macro "emission_poll_native" : tactic => `(tactic| (
  apply product_state
  apply state_native
  try simp only [getRxSkb,freeRxSkb,WG.andM,endpointFromSkb]
  sent_frame []
    using [skb_sent_spec,peek_spec,getPeer_sent_spec,setPeer_sent_spec,getKeypair_sent_spec,
      setKeypair_sent_spec,EmissionFrames.keypair_put_spec,peerPut_sent_spec]))

theorem receive_poll (pid : PeerId) (budget : Nat)
    (callback : List (List UInt8) → PrefixM Event Unit)
    (safe : ∀ packets, ProductSafe (callback packets)) :
    ProductSafe (Driver.pollObserved hooks pid budget callback) := by
  unfold Driver.pollObserved CandidatePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (emission_head Driver.Hooks.candidateEnter; exact candidate_enter _ _)
    | (emission_head Driver.Hooks.candidateLeave; exact candidate_leave _)
    | (emission_head Driver.Hooks.counterCheck; exact counter _ _)
    | (emission_poll_head Driver.consumeObserved; exact product_state (consume _ _ _))
    | (emission_head napiGroReceivePrefix; exact napiGroReceivePrefix_preserves callback
        (fun _ _ _ => True.intro) safe _ _)
    | (emission_head napiGroFlushAllPrefix; exact napiGroFlushAllPrefix_preserves callback
        (fun _ _ _ => True.intro) safe _)
    | (emission_poll_head liftWGPrefix; solve | emission_poll_native)
    | emission_product_step

theorem tagged_poll (pid : PeerId) (budget : Nat)
    (safe : ∀ bytes, ProductSafe (Driver.stackObserved hooks bytes)) :
    ProductSafe (Driver.nativePollObserved hooks pid budget) := by
  have callback := GroOccurrence.stack_preserves (fun h w => Inv h w.wg) (fun _ => True)
    (fun _ _ _ => True.intro) hooks.stackInput (Driver.stackObserved hooks) safe
    (fun entry _ bodySafe => product_scope (.stackInput entry) _ (fun _ => bodySafe))
  unfold Driver.nativePollObserved GroOccurrencePoll.observed GroOccurrencePoll.sourceWith
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (emission_head Driver.Hooks.candidateEnter; exact candidate_enter _ _)
    | (emission_head Driver.Hooks.candidateLeave; exact candidate_leave _)
    | (emission_head Driver.Hooks.counterCheck; exact counter _ _)
    | (emission_poll_head Driver.consumeObserved; exact product_state (consume _ _ _))
    | (emission_head GroOccurrence.receiveWith; exact GroOccurrence.receive_preserves
        (fun h w => Inv h w.wg) (fun _ => True) (fun _ _ _ => True.intro) _ callback _ _)
    | (emission_head GroOccurrence.flushAllWith; exact GroOccurrence.flushAll_preserves
        (fun h w => Inv h w.wg) (fun _ => True) (fun _ _ _ => True.intro) _ callback _)
    | (emission_poll_head liftWGPrefix; solve | emission_poll_native)
    | emission_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
