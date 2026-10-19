import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryTimerObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryReceiveFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryQueuedPassive

/-! The actual receive maintenance source retains full Entry, including its
queued rekey initiation. No unconditional native peer-release frame is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ReceiveObserved
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Obligations RetirementSecurity CausalJournal
open Passive HandshakeSecurity.StagedDisposal
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
variable {ledger : Ledger} {debts : List AllocatedObligation.CleanupDebt} {locals : List TxLocalBatch}

open Lean Meta Elab Tactic in
elab "entry_passive_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Checked do throwError "not a fixed-entry contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observed source"
  let action := args.back!.consumeMData.headBeta
  let .const actual _ := action.getAppFn | throwError "not a constant source head"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

open Lean Meta Elab Tactic in
elab "entry_passive_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Checked do throwError "not a fixed-entry contract"
  let .app front action := target | throwError "missing observed source"
  let rec reduce : Nat → Expr → Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE _ _ value body _ => reduce n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE _ _ value body _ => reduce n (mkAppN (body.instantiate1 value) e.getAppArgs)
        | _ => e.headBeta
  let next := reduce 64 action
  if Expr.equal action next then throwError "source head unchanged"
  replaceMainGoal [← goal.replaceTargetDefEq (mkApp front next)]

macro "entry_passive_step" : tactic => `(tactic| first
  | (entry_passive_head liftWGPrefix; apply Passive.native; solve | entry_receive_native)
  | (entry_passive_head Pure.pure; exact pure_checked _)
  | (entry_passive_head Bind.bind; apply bind_checked)
  | maintenance_intro
  | (entry_passive_head ite; split)
  | entry_passive_reduce)

theorem fresh (pid : PeerId) : Checked ledger debts locals
    (PacketSource.freshReceiveWith effects peerRelease pid) := by
  unfold PacketSource.freshReceiveWith
  apply bind_checked (Passive.native _ (Queued.read pid))
  intro first
  apply bind_checked (ambient (AmbientM.branch .rxFreshSentLastminute first.sentLastminuteHandshake))
  intro sent
  split
  · exact pure_checked ()
  · apply bind_checked (Passive.native _ (Queued.read pid))
    intro peer
    apply bind_checked (Passive.native _ (ReceiveFrames.fresh_decision peer.keypairCurrent))
    intro requested
    apply bind_checked (ambient (AmbientM.branch .rxFreshSend requested))
    intro send
    split
    · apply bind_checked (Passive.native _ (Queued.update pid
        (fun p => {p with sentLastminuteHandshake := true}) (fun _ => ⟨rfl,rfl,rfl⟩)))
      intro ignored
      exact queued pid
    · exact pure_checked ()

theorem prepare (pid : PeerId) (pkt : RxPacket) : Checked ledger debts locals
    (PacketSource.prepareWith effects peerRelease pid pkt) := by
  unfold PacketSource.prepareWith
  simp only [effects,CausalEffects.ops,TimerEffects.observed]
  repeat' first
    | (entry_passive_head PacketSource.freshReceiveWith; exact fresh _)
    | (entry_passive_head TimerEffects.traversalWith; exact TimerObserved.traversal _)
    | (entry_passive_head TimerEffects.dataReceivedWith; exact TimerObserved.received _)
    | entry_passive_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.ReceiveObserved
