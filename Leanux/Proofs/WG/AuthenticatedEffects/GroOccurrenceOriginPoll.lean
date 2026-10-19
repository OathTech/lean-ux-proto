import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrenceOrigins

/-! The actual tagged native poll opens inherited stack scopes only for its
own accepted buffered occurrences. Authentication remains a same-journal join;
no packet is classified as a fixture operation by this source wrapper. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem observed_checked
    (candidate : Nat → SkbId → RxPacket → E) (replay : TransportDriver.Replay → E)
    (stack : E → Option Entry) (record : CausalScope.Event Cause → E) (cause : Entry → Cause)
    (entered : ∀ position entry, stack (record (.entered ⟨position,cause entry⟩)) = some entry)
    (exited : ∀ position, stack (record (.exited position)) = none)
    (candidateQuiet : ∀ position skb packet, stack (candidate position skb packet) = none)
    (replayQuiet : ∀ receipt, stack (replay receipt) = none)
    (leave : Nat → PrefixM E Unit)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (callback : List UInt8 → PrefixM E Unit)
    (hl : ∀ token, PrefixPreserves (fun h (_ : World) => Safe candidate replay stack h)
      (Safe candidate replay stack) (leave token))
    (hc : ∀ pid packet endpoint, PrefixPreserves (fun h (_ : World) => Safe candidate replay stack h)
      (Safe candidate replay stack) (consume pid packet endpoint))
    (hs : ∀ bytes, PrefixPreserves (fun h (_ : World) => Safe candidate replay stack h)
      (Safe candidate replay stack) (callback bytes))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h (_ : World) => Safe candidate replay stack h) (Safe candidate replay stack)
      (GroOccurrencePoll.observed (fun action => liftPrefix (liftWG action)) (GroOccurrence.enter candidate) leave
        (TransportDriver.counter replay) consume
        (fun entry body => CausalScope.prefixScope record (cause entry) (fun _ => body)) callback pid budget) := by
  have batch := stack_checked candidate replay stack
    (fun entry body => CausalScope.prefixScope record (cause entry) (fun _ => body)) callback
    (fun entry => scope_checked candidate replay stack record cause entered exited entry _ (hs entry.bytes))
  apply GroOccurrencePoll.Witness.checked candidate replay (Safe candidate replay stack)
  · intro history skb packet safe
    exact safe.quiet (by
      intro event member
      obtain rfl := List.mem_singleton.mp member
      exact candidateQuiet history.length skb packet)
  · intro history receipt safe
    exact safe.quiet (by
      intro event member
      obtain rfl := List.mem_singleton.mp member
      exact replayQuiet receipt)
  · exact hl
  · exact hc
  · exact receive_checked (Accepted candidate replay) (accepted_monotone candidate replay)
      (Safe candidate replay stack) _ batch
  · exact flushAll_checked (Accepted candidate replay) (accepted_monotone candidate replay)
      (Safe candidate replay stack) _ batch

theorem stack_authenticated
    (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E)
    (stack : E → Option Entry)
    (origin : E → Option TransportDriver.OriginEvent) (replay : E → Option TransportDriver.Replay)
    (inverse : ∀ receipt, replay (record receipt) = some receipt)
    {history before after : List E} {event : E} {entry : Entry}
    (origins : Safe candidate record stack history)
    (authenticated : TransportReplay.Safe origin replay history)
    (position : history = before ++ event :: after) (entered : stack event = some entry) :
    ∃ start receipt rest,
      before = start ++ [candidate entry.scope entry.skb entry.packet,record receipt] ++ rest ∧
      entry.scope = start.length ∧ receipt.skb = entry.skb ∧ receipt.packet = entry.packet ∧
      receipt.run.value = true ∧
      TransportReplay.Certified
        ((start ++ [candidate entry.scope entry.skb entry.packet]).filterMap origin) receipt := by
  have accepted := origins before event after position entry entered
  have prefixSafe : TransportReplay.Safe origin replay before := by
    intro pre value post decomposition
    apply authenticated pre value (post ++ event :: after)
    simp only [position,decomposition,List.append_assoc,List.cons_append]
  exact accepted.authenticated origin replay inverse prefixSafe

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrence.Origins
