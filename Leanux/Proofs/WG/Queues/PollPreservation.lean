import Leanux.Proofs.WG.Queues.PollSource
import Leanux.Proofs.WG.Queues.RxPollStampPhase

/-! Preservation for the literal poll source. The hypotheses name only the
old atoms and decision records that this source actually executes. The old
embedding and the two GRO callbacks retain their arbitrary product domains. -/
namespace Leanux.Proofs.WG.Queues.RxJoint.PollSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes

variable {E α : Type} {I : List E → World → Prop} {S : List E → Prop}

theorem invariant_preserves (safe : ∀ h w, I h w → S h) (why : String) :
    PrefixPreserves I S (liftPrefix (invariant why : Leanux.M α)) := by
  intro w h hi
  exact ⟨[],by change h = h ++ []; simp,safe h w hi,True.intro⟩

theorem unsupported_preserves (safe : ∀ h w, I h w → S h) (why : String) :
    PrefixPreserves I S (liftPrefix (unsupported why : Leanux.M α)) := by
  intro w h hi
  exact ⟨[],by change h = h ++ []; simp,safe h w hi,True.intro⟩

/-- A source-head guard only selects a checked composition rule. It neither
changes the target nor constructs a proof. -/
elab "poll_preserve_head " name:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``PrefixPreserves do Lean.throwError "not a preservation contract"
  let args := target.getAppArgs
  unless args.size > 0 do Lean.throwError "missing observer"
  let head := args.back!.consumeMData.getAppFn
  let actual ← match head with
    | .const n _ => pure n.toString
    | .fvar f => pure (← f.getDecl).userName.eraseMacroScopes.toString
    | _ => Lean.throwError "not a named observer head"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual == expected || actual.endsWith ("." ++ expected) do
    Lean.throwError "different observer head"

/-- Actual poll composition, including every stopped prefix. There is no
contract for an arbitrary old observer: the twelve atom hypotheses below are
the precise old source calls, including their real captured receipts. -/
theorem poll_preserves
    (old : {α : Type} → Obs α → PrefixM E α)
    (receive : Gro → Entry → PrefixM E Gro) (flushAll : Gro → PrefixM E Unit)
    (safe : ∀ h w, I h w → S h)
    (peek : ∀ pid, PrefixPreserves I S (old (access (liftWGObserver (peekAccess pid)))))
    (ready : ∀ first, PrefixPreserves I S (old (access (liftWGObserver (readyAccess first)))))
    (captured : ∀ id, PrefixPreserves I S (old (capture id)))
    (dropped : ∀ pid n id stamp, PrefixPreserves I S (old (drop pid n id stamp)))
    (state : ∀ n id stamp (pkt : RxPacket), PrefixPreserves I S
      (old (receiptObserved (liftPrefix (branch .rxPollNotCrypted (pkt.state != .crypted)))
        (Event.checkedState n id stamp pkt))))
    (counter : ∀ n id stamp (pkt : RxPacket), PrefixPreserves I S
      (old (receiptObserved (access (liftWGObserver (counterValidatePrefix pkt.keypair pkt.nonce)))
        (Event.checkedCounter n id stamp pkt))))
    (endpoint : ∀ n id stamp (pkt : RxPacket), PrefixPreserves I S
      (old (receiptObserved (liftPrefix (liftWG (endpointFromSkb pkt.source)))
        (Event.checkedEndpoint n id stamp pkt))))
    (consumed : ∀ pid n id stamp pkt ep,
      PrefixPreserves I S (old (consume pid n id stamp pkt ep)))
    (keypair : ∀ id, PrefixPreserves I S
      (old (access (liftWGObserver (keypairPutPrefix (some id) false)))))
    (peer : ∀ pid, PrefixPreserves I S
      (old (access (liftWGObserver (peerPutMixed (some pid))))))
    (free : ∀ id, PrefixPreserves I S (old (access (liftWGObserver (freeRxSkbPrefix id)))))
    (complete : ∀ pid, PrefixPreserves I S (old (access (liftWGObserver (completeAccess pid)))))
    (noBudget : ∀ b, PrefixPreserves I S (liftPrefix (branch .rxPollNoBudget b)))
    (counterInvalid : ∀ b, PrefixPreserves I S (liftPrefix (branch .rxPollCounterInvalid b)))
    (endpointFailed : ∀ b, PrefixPreserves I S (liftPrefix (branch .rxPollEndpointFailed b)))
    (freeDecision : ∀ b, PrefixPreserves I S (liftPrefix (branch .rxPollFree b)))
    (budgetDone : ∀ b, PrefixPreserves I S (liftPrefix (branch .rxPollBudgetDone b)))
    (completeDecision : ∀ b, PrefixPreserves I S (liftPrefix (branch .rxPollComplete b)))
    (received : ∀ g e, PrefixPreserves I S (receive g e))
    (flushed : ∀ g, PrefixPreserves I S (flushAll g))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves I S (pollWith old receive flushAll pid budget) := by
  unfold pollWith
  repeat' first
    | (poll_preserve_head old
       first
       | with_reducible exact peek _
       | with_reducible exact ready _
       | with_reducible exact captured _
       | with_reducible exact dropped _ _ _ _
       | with_reducible exact state _ _ _ _
       | with_reducible exact counter _ _ _ _
       | with_reducible exact endpoint _ _ _ _
       | with_reducible exact consumed _ _ _ _ _ _
       | with_reducible exact keypair _
       | with_reducible exact peer _
       | with_reducible exact free _
       | with_reducible exact complete _)
    | (poll_preserve_head receive; exact received _ _)
    | (poll_preserve_head flushAll; exact flushed _)
    | (poll_preserve_head liftPrefix
       first
       | with_reducible exact noBudget _
       | with_reducible exact counterInvalid _
       | with_reducible exact endpointFailed _
       | with_reducible exact freeDecision _
       | with_reducible exact budgetDone _
       | with_reducible exact completeDecision _
       | with_reducible exact invariant_preserves safe _
       | with_reducible exact unsupported_preserves safe _)
    | (poll_preserve_head Pure.pure; exact PrefixPreserves.pure safe _)
    | (poll_preserve_head Bind.bind; apply PrefixPreserves.bind)
    | (poll_preserve_head ForIn.forIn
       first | apply PrefixPreserves.range | apply PrefixPreserves.forIn)
    | (poll_preserve_head ite; apply PrefixPreserves.ite)
    | exact safe
    | rx_phase_reduce
    | rx_phase_intro
    | rx_phase_match

end Leanux.Proofs.WG.Queues.RxJoint.PollSource
