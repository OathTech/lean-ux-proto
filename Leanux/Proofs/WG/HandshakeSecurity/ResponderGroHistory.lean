import Leanux.Proofs.WG.HandshakeSecurity.ResponderPollObservers

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.History
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues RxJoint

theorem enter_rule (e : Entry) (base : List Nat)
    (stack : ∀ bytes confirmed, Preserves (fun w : World => Native confirmed w.wg) (Leanux.Env.deliverInner bytes)) :
    PrefixPreserves (State base) (Checks base) (enter e) := by
  unfold enter
  apply PrefixPreserves.bind (emit_rule _ base rfl)
  intro _
  exact receipt_rule _ _ base
    (access_rule _ _ base (stackReceivePrefix_erases e.tag.bytes)
      (stack e.tag.bytes)) (fun _ => rfl)

theorem flush_rule (es : List Entry) (base : List Nat)
    (stack : ∀ bytes confirmed, Preserves (fun w : World => Native confirmed w.wg) (Leanux.Env.deliverInner bytes)) :
    PrefixPreserves (State base) (Checks base) (flush es) :=
  PrefixPreserves.forM es enter (fun _ _ hi => hi.2) (fun e => enter_rule e base stack)

theorem normalList_rule (g : Gro) (base : List Nat)
    (stack : ∀ bytes confirmed, Preserves (fun w : World => Native confirmed w.wg) (Leanux.Env.deliverInner bytes)) :
    PrefixPreserves (State base) (Checks base) (normalList g) := by
  unfold normalList
  split
  · exact PrefixPreserves.pure (fun _ _ hi => hi.2) _
  · exact (flush_rule _ base stack).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _)

theorem normalOne_rule (g : Gro) (e : Entry) (n : Nat) (base : List Nat)
    (stack : ∀ bytes confirmed, Preserves (fun w : World => Native confirmed w.wg) (Leanux.Env.deliverInner bytes)) :
    PrefixPreserves (State base) (Checks base) (normalOne g e n) := by
  unfold normalOne
  dsimp only
  split
  · exact normalList_rule _ base stack
  · exact PrefixPreserves.pure (fun _ _ hi => hi.2) _

theorem receive_rule (g : Gro) (e : Entry) (base : List Nat)
    (stack : ∀ bytes confirmed, Preserves (fun w : World => Native confirmed w.wg) (Leanux.Env.deliverInner bytes)) :
    PrefixPreserves (State base) (Checks base) (receive g e) := by
  have safe : ∀ h w, State base h w → Checks base h := fun _ _ hi => hi.2
  have stopped {α : Type} (message : String) :
      PrefixPreserves (State base) (Checks base) (liftPrefix (unsupported message : Leanux.M α)) := by
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ safe
    intro h w x v hi hr
    change (Except.error _ : Except Stop _) = _ at hr
    cases hr
  unfold receive
  repeat' first
    | exact normalOne_rule _ _ _ base stack
    | exact stopped _
    | exact PrefixPreserves.pure safe _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem flushAll_rule (g : Gro) (base : List Nat)
    (stack : ∀ bytes confirmed, Preserves (fun w : World => Native confirmed w.wg) (Leanux.Env.deliverInner bytes)) :
    PrefixPreserves (State base) (Checks base) (flushAll g) := by
  unfold flushAll
  apply PrefixPreserves.bind
  · apply PrefixPreserves.forIn
    · exact fun _ _ hi => hi.2
    · intro e g
      exact (normalOne_rule g e 1 base stack).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _)
  · intro g
    exact (normalList_rule {g with held := []} base stack).bind (fun _ => PrefixPreserves.pure (fun _ _ hi => hi.2) _)


end Leanux.Proofs.WG.HandshakeSecurity.Responder.History
