import Leanux.Proofs.WG.Packets.RoutingCuts
import Leanux.Proofs.Logged.NativeCapture

/-! Plain receipts of the original consume call. Validity and named outcomes
are theorems about the captured execution, never fields supplied by callers. -/
namespace Leanux.Proofs.WG.Queues.RxDisposition
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Leanux.Proofs.WG.Packets Leanux.Proofs.WG.CounterWindow Std.Do

structure ConsumeReceipt where
  peer : PeerId
  packet : RxPacket
  endpoint : Endpoint
  run : WGRunWitness (Option (List UInt8))

def ConsumeReceipt.Valid (r : ConsumeReceipt) : Prop :=
  r.run.Valid (consumeDataDone r.peer r.packet r.endpoint)

/-- The two real normal-return source routes. The second includes repayment
before the peer-mismatch decision; a Stop in repayment is not a None receipt. -/
theorem none_route (r : ConsumeReceipt) (hv : r.Valid) (hn : r.run.value = none) :
    ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore = .ok ((none, r.run.after), r.run.ambientAfter) ∨
    ∃ ready u q routed paid middle afterLookup afterPaid,
      ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore = .ok ((some ready, u), middle) ∧
      ((lookupSrc ready.protocol ready.bytes).run u).run middle = .ok ((routed, q), afterLookup) ∧
      ((peerPut routed).run q).run afterLookup = .ok (((), paid), afterPaid) ∧ routed ≠ some r.peer ∧
      ((rxAfterLookup r.peer ready routed).run q).run afterLookup = .ok ((none, r.run.after), r.run.ambientAfter) := by
  have hr := hv
  unfold ConsumeReceipt.Valid WGRunWitness.Valid at hr
  rw [hn, consumeDataDone_factor] at hr
  simp only [StateT.run_bind] at hr
  cases hp : ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore with
  | error e => simp [hp] at hr
  | ok out =>
    rcases out with ⟨⟨ready, u⟩, middle⟩
    cases ready with
    | none =>
      simp only [hp, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
      cases hr
      exact Or.inl rfl
    | some ready =>
      simp only [hp, Leanux.Proofs.WG.CounterWindow.except_ok_bind, rxFinish, StateT.run_bind] at hr
      cases hq : ((lookupSrc ready.protocol ready.bytes).run u).run middle with
      | error e => simp [hq] at hr
      | ok out =>
        rcases out with ⟨⟨routed, q⟩, afterLookup⟩
        simp only [hq, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
        have tail := hr
        unfold rxAfterLookup at hr
        simp only [StateT.run_bind] at hr
        cases hput : ((peerPut routed).run q).run afterLookup with
        | error e => simp [hput] at hr
        | ok out =>
          rcases out with ⟨⟨returned, paid⟩, afterPaid⟩
          cases returned
          have different : routed ≠ some r.peer := by
            intro he
            subst routed
            simp only [hput, except_ok_bind, branch, bne_self_eq_false] at hr
            cases hs : ((updateRxStats r.peer (ready.originalLen + MESSAGE_DATA_LEN_0)).run paid).run
                (record afterPaid .doneDishonestPeer false) <;> simp_all
          exact Or.inr ⟨ready, u, q, routed, paid, middle, afterLookup, afterPaid, rfl, hq, hput, different, tail⟩

theorem some_route (r : ConsumeReceipt) (hv : r.Valid) (bytes : List UInt8)
    (hb : r.run.value = some bytes) :
    ∃ ready u q middle afterLookup,
      ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore = .ok ((some ready, u), middle) ∧
      ((lookupSrc ready.protocol ready.bytes).run u).run middle = .ok ((some r.peer, q), afterLookup) ∧
      ((rxAfterLookup r.peer ready (some r.peer)).run q).run afterLookup = .ok ((some bytes, r.run.after), r.run.ambientAfter) ∧
      RxPrepared r.packet ready ∧ bytes = ready.bytes.take ready.ipLen := by
  apply consumeDataDone_query
  simpa only [ConsumeReceipt.Valid, WGRunWitness.Valid, hb] using hv

/-- Source header/length predicates; keepalive is normal nondelivery. -/
def PrepareRejected (pkt : RxPacket) : Prop :=
  pkt.bytes.length = 0 ∨
  ¬ (pkt.bytes.length ≥ 20 ∧ ((pkt.bytes.headD 0).toNat / 16 = 4 ∨
    ((pkt.bytes.headD 0).toNat / 16 = 6 ∧ pkt.bytes.length ≥ 40))) ∨
  (ipTunnelParseProtocol pkt.bytes = 4 ∧ beAt pkt.bytes 2 2 < 20) ∨
  (ipTunnelParseProtocol pkt.bytes = 4 ∧ beAt pkt.bytes 2 2 > pkt.bytes.length) ∨
  (ipTunnelParseProtocol pkt.bytes = 6 ∧ beAt pkt.bytes 4 2 + 40 > pkt.bytes.length)

private theorem any_spec (a : Leanux.M α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  exact fun _ _ _ _ _ => True.intro

private theorem any_spec_ambient (a : WG.M α) :
    ⦃fun _ => ⌜True⌝⦄ a ⦃⇓? _ _ => ⌜True⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  exact fun _ _ _ _ _ _ _ => True.intro

/-- Compose only a syntactically exposed source head using the local checked contracts. -/
elab "receipt_prepare_step" : tactic => Lean.Elab.Tactic.withMainContext do
  let t := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  let args := t.getAppArgs
  unless args.size ≥ 3 do Lean.throwError "not a Hoare contract"
  let action := args[args.size - 3]!.consumeMData
  let applyLocal (name : String) : Lean.Elab.Tactic.TacticM Unit := do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply $(Lean.mkIdent (Lean.Name.mkSimple name))))
  if action.isAppOf ``Bind.bind then
    let bindArgs := action.getAppArgs
    unless bindArgs.size ≥ 2 do Lean.throwError "missing bind arguments"
    if bindArgs[bindArgs.size - 2]!.consumeMData.isAppOf ``Leanux.branch then
      applyLocal "decision"
    else
      applyLocal "step"
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro x))
  else if action.isAppOf ``Pure.pure then
    applyLocal "done"
  else if action.isAppOf ``ite then
    applyLocal "conditional"
    Lean.Elab.Tactic.evalTactic (← `(tactic| all_goals intro h))
  else
    Lean.throwError "no composition rule for action head"

/-- Every normal None from the preparation factor has an actual named
keepalive/header/length cause. Literal false arms and protocol fallthrough
supply no extra reachable rejection. -/
theorem prepare_none (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ⦃fun _ => ⌜True⌝⦄ rxPrepare pid pkt ep
    ⦃⇓? result _ => ⌜result = none → PrepareRejected pkt⌝⦄ := by
  classical
  by_cases rejected : PrepareRejected pkt
  · exact hoare_consequence (any_spec_ambient (rxPrepare pid pkt ep))
      (fun _ h => h) (fun _ _ _ _ => rejected)
  · simp only [PrepareRejected, not_or, Classical.not_not] at rejected
    rcases rejected with ⟨hzero, ⟨h20, versions⟩, hshort, hbound4, hbound6⟩
    let post : Option RxReady → WGWorld → Prop :=
      fun result _ => result ≠ none
    have step {α : Type} (a : WG.M α) (f : α → WG.M (Option RxReady))
        (hf : ∀ x, Hoare (f x) (fun _ => True) post) :
        Hoare (a >>= f) (fun _ => True) post :=
      hoare_bind _ _ (any_spec_ambient a) hf
    have decision (d : Decision) (b : Bool) (f : Bool → WG.M (Option RxReady))
        (hf : Hoare (f b) (fun _ => True) post) :
        Hoare (branch d b >>= f) (fun _ => True) post := by
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w ambient result v ambient' _ hr
      simp only [branch, StateT.run_monadLift, monadLift_self, StateT.run_bind,
        branch_run, except_ok_bind] at hr
      exact (hoare_iff_run_ambient _ _ _).mp hf w (record ambient d b)
        result v ambient' trivial hr
    have done (x : Option RxReady) (hx : x ≠ none) :
        Hoare (pure x : WG.M _) (fun _ => True) post :=
      hoare_consequence (hoare_pure x (fun _ : WGWorld => True)) (fun _ h => h)
        (fun y _ h => by simpa [post, h.1] using hx)
    have conditional (p : Prop) [Decidable p] (a b : WG.M (Option RxReady))
        (ha : p → Hoare a (fun _ => True) post)
        (hb : ¬p → Hoare b (fun _ => True) post) :
        Hoare (if p then a else b) (fun _ => True) post := by
      by_cases hp : p
      · simpa only [ite_eq_left hp] using ha hp
      · simpa only [ite_eq_right hp] using hb hp
    have bind_if {α β : Type} (p : Prop) [Decidable p] (a b : WG.M α) (f : α → WG.M β) :
        (if p then a else b) >>= f = (if p then a >>= f else b >>= f) := by
      split <;> rfl
    have noNone : Hoare (rxPrepare pid pkt ep) (fun _ => True) post := by
      rcases versions with version | ⟨version, h40⟩
      case' inl =>
        simp only [List.headD_eq_head?_getD] at version
        have proto : ipTunnelParseProtocol pkt.bytes = 4 := by
          simp [ipTunnelParseProtocol, h20, version]
        have hminimum := h20
        simp only [proto, true_and, false_and, not_false_eq_true, Nat.reduceEqDiff] at hshort hbound4 hbound6
      case' inr =>
        simp only [List.headD_eq_head?_getD] at version
        have proto : ipTunnelParseProtocol pkt.bytes = 6 := by
          simp [ipTunnelParseProtocol, h20, version, h40]
        have hminimum := h40
        simp only [proto, true_and, false_and, not_false_eq_true, Nat.reduceEqDiff] at hshort hbound4 hbound6
      all_goals
        unfold rxPrepare WG.andM WG.orM
        simp only [bind_assoc, bind_if, pure_bind]
        repeat' first
          | simp +failIfUnchanged only [List.headD_eq_head?_getD, hzero, h20, version, hminimum, proto, hshort, hbound4, hbound6,
              beq_iff_eq, decide_eq_true_eq, Bool.false_eq_true,
              Bool.not_true, Bool.not_false, ite_true, ite_false]
          | receipt_prepare_step
          | dsimp only
          | contradiction
        all_goals clear step decision done conditional bind_if
        all_goals clear post
        all_goals simp only [ne_eq, Option.some_ne_none, not_false_eq_true]
    exact hoare_consequence noNone (fun _ h => h)
      (fun result _ h hn => False.elim (h hn))

/-- Complete normal-None classification, including the actual repaid lookup
route. No packet/key validity or initialized-state premise is used. -/
theorem none_classified (r : ConsumeReceipt) (hv : r.Valid) (hn : r.run.value = none) :
    PrepareRejected r.packet ∨
    ∃ ready u q routed paid middle afterLookup afterPaid,
      ((rxPrepare r.peer r.packet r.endpoint).run r.run.before).run r.run.ambientBefore = .ok ((some ready, u), middle) ∧
      ((lookupSrc ready.protocol ready.bytes).run u).run middle = .ok ((routed, q), afterLookup) ∧
      ((peerPut routed).run q).run afterLookup = .ok (((), paid), afterPaid) ∧ routed ≠ some r.peer ∧
      ((rxAfterLookup r.peer ready routed).run q).run afterLookup = .ok ((none, r.run.after), r.run.ambientAfter) := by
  rcases none_route r hv hn with h | h
  · exact Or.inl ((hoare_iff_run_ambient _ _ _).mp (prepare_none r.peer r.packet r.endpoint)
      r.run.before r.run.ambientBefore none r.run.after r.run.ambientAfter True.intro h rfl)
  · exact Or.inr h

end Leanux.Proofs.WG.Queues.RxDisposition
