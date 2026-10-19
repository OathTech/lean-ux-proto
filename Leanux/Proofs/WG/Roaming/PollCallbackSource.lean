import Leanux.Proofs.WG.Roaming.PollEndpointModel
import Leanux.Proofs.Logged.PrefixGro
import Leanux.Proofs.WG.Queues.PollPreservation
import Leanux.Proofs.WG.TimerDiscipline.PollCounterFrames
set_option autoImplicit false
/-! The owned native poll spine with explicit consume and GRO callbacks.
The original PollEndpointSource functions are native instances. -/
namespace Leanux.Proofs.WG.Roaming.PollHookRules
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
variable {m : Type → Type} [Monad m]

def stepWith (lift : ∀ {α : Type}, Leanux.M α → m α)
    (consume : PeerId → RxPacket → Endpoint → m (Option (List UInt8)))
    (receive : GroState → List UInt8 → m GroState)
    (pid : PeerId) (budget : Nat) (_ : Nat) (state : PollState) : m (ForInStep PollState) := do
  let mut workDone := state.1
  let mut gro := state.2.1
  let drained := state.2.2
  let (first, q) ← lift (do (← getPeer pid).rxQueue.peek)
  lift (do setPeer pid { (← getPeer pid) with rxQueue := q })
  let go ← lift (liftWG (WG.andM (branch .rxPollPacket first.isSome) do
    let some f := first | invariant "unreachable"
    branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)))
  if !go then return .done (workDone, gro, true)
  let some id := first | lift (invariant "unreachable")
  let pkt ← lift (getRxSkb id)
  if pkt.peer != pid then lift (invariant "a packet on another peer's rx_queue")
  lift (do setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked })
  let mut free := true
  if !(← lift (branch .rxPollNotCrypted (pkt.state != .crypted))) then
    if !(← lift (do branch .rxPollCounterInvalid !(← counterValidate pkt.keypair pkt.nonce))) then
      let endpoint ← lift (endpointFromSkb pkt.source)
      if !(← lift (branch .rxPollEndpointFailed endpoint.isNone)) then
        let some e := endpoint | lift (invariant "unreachable")
        for inner in (← consume pid pkt e).toList do
          gro ← receive gro inner
        free := false
  lift (keypairPut (some pkt.keypair) false)
  lift (peerPut (some pid))
  _ ← lift (branch .rxPollFree free)
  lift (freeRxSkb id)
  workDone := workDone + 1
  if ← lift (branch .rxPollBudgetDone (workDone ≥ budget)) then
    return .done (workDone, gro, drained)
  return .yield (workDone, gro, drained)

def finishWith (lift : ∀ {α : Type}, Leanux.M α → m α)
    (flush : GroState → m Unit) (pid : PeerId) (budget : Nat) (state : PollState) : m Nat := do
  let workDone := state.1
  let gro := state.2.1
  let drained := state.2.2
  if !drained && workDone < budget then lift (invariant "the rx_queue did not drain")
  if ← lift (branch .rxPollComplete (workDone < budget)) then
    lift (do setPeer pid { (← getPeer pid) with napiScheduled := false })
    flush gro
  else lift (unsupported "a NAPI poll that used its whole budget (a repoll)")
  return workDone

def pollWith (lift : ∀ {α : Type}, Leanux.M α → m α)
    (consume : PeerId → RxPacket → Endpoint → m (Option (List UInt8)))
    (receive : GroState → List UInt8 → m GroState)
    (flush : GroState → m Unit) (pid : PeerId) (budget : Nat) : m Nat := do
  if ← lift (branch .rxPollNoBudget (budget == 0)) then return 0
  let state ← forIn ([:MAX_QUEUED_PACKETS + 1] : Std.Legacy.Range)
    ((0, {}, false) : PollState) (stepWith lift consume receive pid budget)
  finishWith lift flush pid budget state

end Leanux.Proofs.WG.Roaming.PollHookRules

namespace Leanux.Proofs.WG.Roaming.PollHookRules
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {E : Type}

elab "hook_poll_head " name:ident : tactic => Lean.Elab.Tactic.withMainContext do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := target.getAppArgs
  let action ←
    if target.isAppOf ``ErasesPrefix then pure args[args.size - 2]!
    else if target.isAppOf ``PrefixPreserves || target.isAppOf ``Appends then pure args.back!
    else Lean.throwError "not a poll contract"
  let head := action.consumeMData.getAppFn
  let actual ← match head with
    | .const n _ => pure n.toString
    | .fvar f => pure (← f.getDecl).userName.eraseMacroScopes.toString
    | _ => Lean.throwError "not a named source head"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual == expected || actual.endsWith ("." ++ expected) do
    Lean.throwError "different source head"

theorem step_erases
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (original : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ p pkt ep, ErasesPrefix (consume p pkt ep) (liftWG (consumeDataDone p pkt ep)))
    (hs : ∀ packets, ErasesPrefix (toStack packets) (original packets))
    (pid budget n state) :
    ErasesPrefix
      (stepWith (fun {_} a=>liftPrefix a) consume (napiGroReceivePrefix toStack) pid budget n state)
      (stepWith (fun {_} a=>a) (fun p pkt ep=>liftWG (consumeDataDone p pkt ep))
        (napiGroReceive original) pid budget n state) := by
  unfold stepWith
  dsimp only
  repeat' first
    | (hook_poll_head consume; exact hc _ _ _)
    | (hook_poll_head napiGroReceivePrefix; exact napiGroReceivePrefix_erases toStack original hs _ _)
    | (hook_poll_head liftPrefix; exact erasesPrefix_lift _)
    | (hook_poll_head Pure.pure; exact erasesPrefix_pure _)
    | (hook_poll_head ForIn.forIn; apply erasesPrefix_forIn)
    | (hook_poll_head Bind.bind; apply erasesPrefix_bind)
    | (hook_poll_head ite; split)
    | (hook_poll_head dite; split)
    | maintenance_intro
    | (with_reducible split)

theorem finish_erases
    (toStack : List (List UInt8) → PrefixM E Unit)
    (original : List (List UInt8) → Leanux.M Unit)
    (hs : ∀ packets, ErasesPrefix (toStack packets) (original packets))
    (pid budget state) :
    ErasesPrefix
      (finishWith (fun {_} a=>liftPrefix a) (napiGroFlushAllPrefix toStack) pid budget state)
      (finishWith (fun {_} a=>a) (napiGroFlushAll original) pid budget state) := by
  unfold finishWith
  dsimp only
  repeat' first
    | (hook_poll_head napiGroFlushAllPrefix; exact napiGroFlushAllPrefix_erases toStack original hs _)
    | (hook_poll_head liftPrefix; exact erasesPrefix_lift _)
    | (hook_poll_head Pure.pure; exact erasesPrefix_pure _)
    | (hook_poll_head Bind.bind; apply erasesPrefix_bind)
    | (hook_poll_head ite; split)
    | (hook_poll_head dite; split)
    | maintenance_intro
    | (with_reducible split)

theorem poll_erases
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (original : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ p pkt ep, ErasesPrefix (consume p pkt ep) (liftWG (consumeDataDone p pkt ep)))
    (hs : ∀ packets, ErasesPrefix (toStack packets) (original packets))
    (pid budget) :
    ErasesPrefix
      (pollWith (fun {_} a=>liftPrefix a) consume
        (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget)
      (pollWith (fun {_} a=>a) (fun p pkt ep=>liftWG (consumeDataDone p pkt ep))
        (napiGroReceive original) (napiGroFlushAll original) pid budget) := by
  unfold pollWith
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro noBudget
  split
  · exact erasesPrefix_pure _
  · apply erasesPrefix_bind
    · apply erasesPrefix_range
      intro n state
      exact step_erases consume toStack original hc hs pid budget n state
    · intro state
      exact finish_erases toStack original hs pid budget state

theorem lift_safe (S : List E → Prop) {α : Type} (action : Leanux.M α) :
    PrefixPreserves (fun h _=>S h) S (liftPrefix action) :=
  PrefixEnsures.preserves (PrefixEnsures.lift action
    (fun (h : List E) (_ : World) (pre : S h)=>pre) (fun _ _ _ _ pre _=>pre))

section StatePreservation
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open TimerDiscipline.HandshakeJournal Lifetimes TimerDiscipline.PollCounterFrames
macro "poll_counter_lift" : tactic => `(tactic|
 (apply counter_product_frame
  first
  | (snapshot_head liftWG; exact ready _)
  | env_operation_source [] using
    [peer,writePeer,packet,freePacket,peek,endpoint,key,release,counter,branch_counter,invariant_counter,unsupported_counter,ambient]))
variable {I : List E→World→Prop} {S : List E→Prop}
theorem step_preserves_state
    (safe : ∀h w,I h w→S h)
    (native : ∀{α : Type} (action : Leanux.M α), ProductCounterMono action→PrefixPreserves I S (liftPrefix action))
    (consume : PeerId→RxPacket→Endpoint→PrefixM E (Option (List UInt8)))
    (toStack : List (List UInt8)→PrefixM E Unit)
    (hc : ∀p pkt ep,PrefixPreserves I S (consume p pkt ep))
    (hs : ∀packets,PrefixPreserves I S (toStack packets)) (pid budget n state) :
    PrefixPreserves I S
      (stepWith (fun {_} a=>liftPrefix a) consume (napiGroReceivePrefix toStack) pid budget n state) := by
  unfold stepWith
  dsimp only
  repeat' first
    | (hook_poll_head consume; exact hc _ _ _)
    | (hook_poll_head napiGroReceivePrefix; exact napiGroReceivePrefix_preserves toStack safe hs _ _)
    | (hook_poll_head liftPrefix; apply native; poll_counter_lift)
    | (hook_poll_head Pure.pure; exact PrefixPreserves.pure safe _)
    | (hook_poll_head ForIn.forIn; apply PrefixPreserves.forIn _ _ _ safe)
    | (hook_poll_head Bind.bind; apply PrefixPreserves.bind)
    | (hook_poll_head ite; split)
    | (hook_poll_head dite; split)
    | maintenance_intro
    | (with_reducible split)

theorem finish_preserves_state
    (safe : ∀h w,I h w→S h)
    (native : ∀{α : Type} (action : Leanux.M α), ProductCounterMono action→PrefixPreserves I S (liftPrefix action))
    (toStack : List (List UInt8)→PrefixM E Unit)
    (hs : ∀packets,PrefixPreserves I S (toStack packets)) (pid budget state) :
    PrefixPreserves I S
      (finishWith (fun {_} a=>liftPrefix a) (napiGroFlushAllPrefix toStack) pid budget state) := by
  unfold finishWith
  dsimp only
  repeat' first
    | (hook_poll_head napiGroFlushAllPrefix; exact napiGroFlushAllPrefix_preserves toStack safe hs _)
    | (hook_poll_head liftPrefix; apply native; poll_counter_lift)
    | (hook_poll_head Pure.pure; exact PrefixPreserves.pure safe _)
    | (hook_poll_head Bind.bind; apply PrefixPreserves.bind)
    | (hook_poll_head ite; split)
    | (hook_poll_head dite; split)
    | maintenance_intro
    | (with_reducible split)

theorem poll_preserves_state
    (safe : ∀h w,I h w→S h)
    (native : ∀{α : Type} (action : Leanux.M α), ProductCounterMono action→PrefixPreserves I S (liftPrefix action))
    (consume : PeerId→RxPacket→Endpoint→PrefixM E (Option (List UInt8)))
    (toStack : List (List UInt8)→PrefixM E Unit)
    (hc : ∀p pkt ep,PrefixPreserves I S (consume p pkt ep))
    (hs : ∀packets,PrefixPreserves I S (toStack packets)) (pid budget) :
    PrefixPreserves I S
      (pollWith (fun {_} a=>liftPrefix a) consume
        (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget) := by
  unfold pollWith
  apply PrefixPreserves.bind (native _ (counter_product_frame (branch_counter _ _)))
  intro noBudget
  split
  · exact PrefixPreserves.pure safe _
  · apply PrefixPreserves.bind
    · apply PrefixPreserves.range _ _ _ safe
      intro n state
      exact step_preserves_state safe native consume toStack hc hs pid budget n state
    · intro state
      exact finish_preserves_state safe native toStack hs pid budget state
end StatePreservation

theorem step_preserves (S : List E → Prop)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ p pkt ep, PrefixPreserves (fun h _=>S h) S (consume p pkt ep))
    (hs : ∀ packets, PrefixPreserves (fun h _=>S h) S (toStack packets))
    (pid budget n state) :
    PrefixPreserves (fun h _=>S h) S
      (stepWith (fun {_} a=>liftPrefix a) consume (napiGroReceivePrefix toStack) pid budget n state) :=
  step_preserves_state (I:=fun h _=>S h) (S:=S) (fun _ _ prior=>prior)
    (fun action _=>lift_safe S action) consume toStack hc hs pid budget n state

theorem finish_preserves (S : List E → Prop)
    (toStack : List (List UInt8) → PrefixM E Unit)
    (hs : ∀ packets, PrefixPreserves (fun h _=>S h) S (toStack packets))
    (pid budget state) :
    PrefixPreserves (fun h _=>S h) S
      (finishWith (fun {_} a=>liftPrefix a) (napiGroFlushAllPrefix toStack) pid budget state) :=
  finish_preserves_state (I:=fun h _=>S h) (S:=S) (fun _ _ prior=>prior)
    (fun action _=>lift_safe S action) toStack hs pid budget state

theorem poll_preserves (S : List E → Prop)
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ p pkt ep, PrefixPreserves (fun h _=>S h) S (consume p pkt ep))
    (hs : ∀ packets, PrefixPreserves (fun h _=>S h) S (toStack packets))
    (pid budget) :
    PrefixPreserves (fun h _=>S h) S
      (pollWith (fun {_} a=>liftPrefix a) consume
        (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget) :=
  poll_preserves_state (I:=fun h _=>S h) (S:=S) (fun _ _ prior=>prior)
    (fun action _=>lift_safe S action) consume toStack hc hs pid budget

end Leanux.Proofs.WG.Roaming.PollHookRules

namespace Leanux.Proofs.WG.Roaming.PollHookRules
open Leanux Leanux.WG Leanux.Proofs.Logged
variable {E α : Type}
theorem appends_true (action : PrefixM E α) (ha : Appends action) :
    PrefixPreserves (fun _ _=>True) (fun _=>True) action := by
  intro w h _
  obtain ⟨suffix,eq⟩ := ha w h
  refine ⟨suffix,eq,True.intro,?_⟩
  cases (runPrefix action w h).1 <;> trivial
theorem poll_appends
    (consume : PeerId → RxPacket → Endpoint → PrefixM E (Option (List UInt8)))
    (toStack : List (List UInt8) → PrefixM E Unit)
    (hc : ∀ p pkt ep, Appends (consume p pkt ep))
    (hs : ∀ packets, Appends (toStack packets))
    (pid budget) :
    Appends (pollWith (fun {_} a=>liftPrefix a) consume
      (napiGroReceivePrefix toStack) (napiGroFlushAllPrefix toStack) pid budget) := by
  intro w h
  obtain ⟨suffix,eq,_⟩ := poll_preserves (fun _=>True) consume toStack
    (fun p pkt ep=>appends_true _ (hc p pkt ep))
    (fun packets=>appends_true _ (hs packets)) pid budget w h True.intro
  exact ⟨suffix,eq⟩
end Leanux.Proofs.WG.Roaming.PollHookRules

