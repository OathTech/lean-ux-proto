import Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePollWitness
import Leanux.Proofs.WG.AuthenticatedEffects.TransportReplayAuthorizedPoll

/-! Actual native poll guards create the buffered occurrence witness. The
consumer and GRO callbacks operate on this same journal; a stopped execution
retains all earlier checked stack entries. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll.Witness
open Leanux Leanux.WG Leanux.Proofs.Logged GroOccurrence
open Lifetimes Queues RxJoint TransportReplay
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem checked
    (candidate : Nat → SkbId → RxPacket → E) (record : TransportDriver.Replay → E)
    (Safe : List E → Prop)
    (candidate_quiet : ∀ history skb packet, Safe history → Safe (history ++ [candidate history.length skb packet]))
    (replay_quiet : ∀ history receipt, Safe history → Safe (history ++ [record receipt]))
    (leave : Nat → PrefixM E Unit)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (receive : Buffer → GroOccurrence.Entry → PrefixM E Buffer) (flush : Buffer → PrefixM E Unit)
    (hl : ∀ token, PrefixPreserves (fun h (_ : World) => Safe h) Safe (leave token))
    (hc : ∀ pid packet endpoint, PrefixPreserves (fun h (_ : World) => Safe h) Safe (consume pid packet endpoint))
    (hr : ∀ gro entry, PrefixEnsures
      (fun h w => Base (Good candidate record) Safe gro h w ∧ Good candidate record entry h)
      Safe (receive gro entry) (fun output => Base (Good candidate record) Safe output))
    (hf : ∀ gro, PrefixEnsures (Base (Good candidate record) Safe gro) Safe (flush gro)
      (fun _ h _ => Safe h))
    (pid : PeerId) (budget : Nat) :
    PrefixPreserves (fun h (_ : World) => Safe h) Safe
      (sourceWith (fun action => liftPrefix (liftWG action)) (GroOccurrence.enter candidate) leave
        (TransportDriver.counter record) consume receive flush pid budget) := by
  apply PrefixEnsures.preserves
  unfold sourceWith
  apply branch_bind
  · intro _ input; exact input
  intro noBudget equal
  split
  · exact PrefixEnsures.pure (fun _ _ input => input) (fun _ _ input => input)
  · apply PrefixEnsures.bind
      (Q := fun acc : Nat × Buffer × Bool => Base (Good candidate record) Safe acc.2.1)
    · apply PrefixEnsures.consequence (P := Base (Good candidate record) Safe {})
        (Q := fun acc : Nat × Buffer × Bool => Base (Good candidate record) Safe acc.2.1)
      · apply PrefixEnsures.rangeInvariant _ (0,({} : Buffer),false) _
          (fun acc : Nat × Buffer × Bool => Base (Good candidate record) Safe acc.2.1) Safe
          (fun _ _ _ input => input.1)
        intro index acc
        repeat' first
          | (rx_phase_head plain GroOccurrence.enter
             apply PrefixEnsures.bind (GroOccurrence.enter_checked candidate record Safe candidate_quiet _ _ _))
          | (rx_phase_head plain TransportDriver.counter
             apply PrefixEnsures.bind (GroOccurrence.counter_checked candidate record Safe replay_quiet _ _ _ _))
          | (replay_callback consume
             apply consume_bind candidate record Safe consume hc (success := by simp_all))
          | (replay_callback leave
             apply leave_bind (Good candidate record) (accepted_monotone candidate record) Safe leave hl
             · intro h w input; first | exact input | exact input.1)
          | (rx_phase_head plain ForIn.forIn
             apply PrefixEnsures.bind (receive_option candidate record Safe receive hr _ _ _ _ _))
          | (replay_head ForIn.forIn
             exact receive_option candidate record Safe receive hr _ _ _ _ _)
          | (replay_native_head invariant
             apply stopped
             intro h w input; first | exact input.1 | exact input.1.1)
          | (replay_native_head branch
             apply branch_bind
             · intro h input; first | exact input.1 | exact input.1.1
             intro result result_eq)
          | (replay_head liftPrefix
             apply native
             intro h input; first | exact input.1 | exact input.1.1)
          | (replay_head Bind.bind; apply flow_bind)
          | (replay_head Pure.pure; apply PrefixEnsures.pure
             · intro h w input; first | exact input.1 | exact input.1.1
             · intro h w input; first | exact input | exact input.1)
          | (replay_head ite; apply PrefixEnsures.ite)
          | rx_phase_reduce
          | rx_phase_match
          | (rx_phase_intro; try dsimp only [Base])
          | assumption
      · intro h _ input; exact ⟨input,Buffer.Ready.empty _ h⟩
      · intro _ _ _ output; exact output
    · intro acc
      repeat' first
        | (replay_callback flush; apply PrefixEnsures.bind (hf _))
        | (replay_native_head invariant
           apply stopped
           intro h w input; first | exact input | exact input.1)
        | (replay_head liftPrefix
           apply native
           intro h input; first | exact input | exact input.1)
        | (replay_head Bind.bind; apply flow_bind)
        | (replay_head Pure.pure; apply PrefixEnsures.pure
           · intro h w input; first | exact input | exact input.1
           · intro h w input; first | exact input | exact input.1)
        | (replay_head ite; apply PrefixEnsures.ite)
        | rx_phase_reduce
        | rx_phase_match
        | (rx_phase_intro; try dsimp only [Base])
        | assumption

end Leanux.Proofs.WG.AuthenticatedEffects.GroOccurrencePoll.Witness
