import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteTxFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuiet

/-! Append-only history follows the actual completion callbacks, including
terminal and peer-release receipts. No event is declared semantically quiet. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.TxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation.CompletionBatch HandshakeSecurity.StagedConservation
set_option maxRecDepth 4096

private theorem callbacks : CompletionEffects.Ops.Appends CausalJournal.completionOps where
  step := fun _ => Appends.focus _ _ _
  peer := fun _ => Appends.focus _ _ _
  modifyPeer := fun _ _ => Appends.focus _ _ _
  packet := fun _ => Appends.focus _ _ _
  completion := fun _ _ => Appends.focus _ _ _
  send := send_appends
  drop := fun _ _ => Appends.focus _ _ _
  dispose := fun pid item key => (CausalJournal.CallbackQuiet.dispose
    (fun _ => (none : Option Unit)) (fun _ => rfl) (fun _ => rfl) pid item key).1
  traversal := traversal_appends
  sent := fun _ => Appends.focus _ _ _
  dataSent := dataSent_appends
  fresh := fun pid => (Fresh.fresh_appends pid).liftWGObserver

open Lean Meta Elab Tactic in
elab "tx_append_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Appends do throwError "not an append contract"
  let some action := target.getAppArgs.back? | throwError "missing action"
  let action := action.consumeMData.headBeta
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

macro "tx_history_append " h:ident : tactic => `(tactic| first
  | (tx_append_head CompletionEffects.Ops.step; exact CompletionEffects.Ops.Appends.step $h _)
  | (tx_append_head CompletionEffects.Ops.peer; exact CompletionEffects.Ops.Appends.peer $h _)
  | (tx_append_head CompletionEffects.Ops.modifyPeer; exact CompletionEffects.Ops.Appends.modifyPeer $h _ _)
  | (tx_append_head CompletionEffects.Ops.packet; exact CompletionEffects.Ops.Appends.packet $h _)
  | (tx_append_head CompletionEffects.Ops.completion; exact CompletionEffects.Ops.Appends.completion $h _ _)
  | (tx_append_head CompletionEffects.Ops.send; exact CompletionEffects.Ops.Appends.send $h _ _ _)
  | (tx_append_head CompletionEffects.Ops.drop; exact CompletionEffects.Ops.Appends.drop $h _ _)
  | (tx_append_head CompletionEffects.Ops.dispose; exact CompletionEffects.Ops.Appends.dispose $h _ _ _)
  | (tx_append_head CompletionEffects.Ops.traversal; exact CompletionEffects.Ops.Appends.traversal $h _)
  | (tx_append_head CompletionEffects.Ops.sent; exact CompletionEffects.Ops.Appends.sent $h _)
  | (tx_append_head CompletionEffects.Ops.dataSent; exact CompletionEffects.Ops.Appends.dataSent $h _)
  | (tx_append_head CompletionEffects.Ops.fresh; exact CompletionEffects.Ops.Appends.fresh $h _)
  | (tx_append_head captureObserved; apply Appends.captureObserved)
  | (tx_append_head Pure.pure; exact Appends.pure _)
  | (tx_append_head Bind.bind; apply Appends.bind)
  | (tx_append_head ForIn.forIn; apply Appends.forIn)
  | (maintenance_intro; try dsimp only)
  | simp +failIfUnchanged only
  | split)

private theorem complete {o : CompletionEffects.Ops E} (h : CompletionEffects.Ops.Appends o)
    (pid : PeerId) (items : List SkbId) : Appends (CompletionEffects.completeWith o pid items) := by
  unfold CompletionEffects.completeWith TxDisposition.andObs
  repeat' tx_history_append h

private theorem complete_scoped (pid : PeerId) (items : List SkbId) :
    Appends (CompletionEffects.completeScoped CausalJournal.Event.scope
      CausalSources.Cause.completion CausalJournal.completionOps pid items) := by
  intro w h
  obtain ⟨suffix,grown⟩ := CausalScope.prefix_entry CausalJournal.Event.scope
    (CausalSources.Cause.completion pid items) (fun _ =>
      CompletionEffects.completeWith CausalJournal.completionOps pid items)
    (fun _ => complete callbacks pid items) w h
  exact ⟨_,grown⟩

private theorem body {o : CompletionEffects.Ops E} (h : CompletionEffects.Ops.Appends o)
    (completed : PeerId → List SkbId → PrefixM E Unit)
    (dead : PeerId → List SkbId → DataPacket → PrefixM E Bool)
    (hc : ∀ pid items, Appends (completed pid items))
    (hd : ∀ pid items head, Appends (dead pid items head))
    (pid : PeerId) (first : Option (List SkbId)) :
    Appends (Terminal.bodyWith o completed dead pid first) := by
  unfold Terminal.bodyWith TxDisposition.andObs
  repeat' first
    | exact hc _ _
    | exact hd _ _ _
    | tx_history_append h

private theorem step {o : CompletionEffects.Ops E} (h : CompletionEffects.Ops.Appends o)
    (completed : PeerId → List SkbId → PrefixM E Unit)
    (dead : PeerId → List SkbId → DataPacket → PrefixM E Bool)
    (hc : ∀ pid items, Appends (completed pid items))
    (hd : ∀ pid items head, Appends (dead pid items head)) (pid : PeerId) :
    Appends (Terminal.stepWith o completed dead pid) := by
  unfold Terminal.stepWith
  repeat' first
    | (tx_append_head Terminal.bodyWith; exact body h completed dead hc hd _ _)
    | tx_history_append h

theorem transmit (pid : PeerId) : Appends (CausalJournal.transmit pid) :=
  step callbacks _ _ complete_scoped
    (fun peer items head => (CausalJournal.CallbackQuiet.dead (fun _ => (none : Option Unit))
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) peer items head).1) pid

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.TxHistory
