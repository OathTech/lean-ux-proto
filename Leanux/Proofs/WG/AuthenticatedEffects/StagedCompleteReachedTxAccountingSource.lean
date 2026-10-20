import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxAccountingAccessFrames

/-! Post-socket accounting follows its actual result guard and saved-peer
update. Native write points retain the completed socket receipt in history. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal
abbrev History := List CausalJournal.Event

def action (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) : PrefixM CausalJournal.Event Bool :=
  FirstTerminal.focused (afterSocket pid packet ret)

def guardedWorld (ret : Int) (w : World) : World :=
  {w with ambient:=CounterWindow.record w.ambient .sendSkbOk (ret==0)}

def guardedBody (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) : PrefixM CausalJournal.Event Bool :=
  if ret==0 then do
    TxAccountingAccess.observed (modifyPeerKeysPrefix pid fun p=>{p with txBytes:=p.txBytes+packet.value.bytes.length})
    pure (ret==0)
  else pure (ret==0)

private theorem branch_run (w : World) (decision : Decision) (value : Bool) :
    (liftWG (branch decision value)).run w=
      .ok (value,{w with ambient:=CounterWindow.record w.ambient decision value}) := rfl

theorem focused_pure (value : α) : FirstTerminal.focused (pure value)=(pure value : PrefixM CausalJournal.Event α) := by
  funext w h
  exact (FocusesUnder.pure (I:=fun (_ : List Completion.Event) (_ : World)=>True)
    (encode:=FirstTerminal.encode) (decode:=CausalJournal.completion?) value w h True.intro).symm

theorem focused_lift (body : Leanux.M α) : FirstTerminal.focused (liftPrefix body)=liftPrefix body := by
  funext w h
  exact (FocusesUnder.lift (I:=fun (_ : List Completion.Event) (_ : World)=>True)
    (encode:=FirstTerminal.encode) (decode:=CausalJournal.completion?) body w h True.intro).symm

theorem focused_bind {body : PrefixM Completion.Event α} {next : α → PrefixM Completion.Event β}
    (head : Appends body) (tail : ∀value,Appends (next value)) :
    FirstTerminal.focused (body >>= next)=(FirstTerminal.focused body >>= fun value=>FirstTerminal.focused (next value)) := by
  funext w h
  exact (focusPrefix_bind_appends FirstTerminal.encode CausalJournal.completion?
    (by intro event;cases event <;> rfl) head tail w h).symm

theorem after_guard (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) (w : World) (h : History) :
    runPrefix (action pid packet ret) w h=runPrefix (guardedBody pid packet ret) (guardedWorld ret w) h := by
  unfold action afterSocket
  rw [focused_bind (Appends.lift _) (fun sent=>by
    cases sent with
    | false=>exact Appends.pure _
    | true=>exact Appends.bind (Appends.focus _ _ _) (fun _=>Appends.pure _))]
  rw [focused_lift,runPrefix_bind,runPrefix_lift,branch_run]
  cases flag : ret==0 with
  | false=>simp only [guardedBody,guardedWorld,flag,Bool.false_eq_true,ite_false,focused_pure]
  | true=>
      simp only [guardedBody,guardedWorld,flag,ite_true]
      rw [focused_bind (body:=Completion.access (modifyPeerKeysPrefix pid fun p=>{p with txBytes:=p.txBytes+packet.value.bytes.length}))
        (by exact Appends.focus _ _ _) (fun _=>Appends.pure _)]
      simp only [focused_pure]
      rfl

inductive Point (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) (w : World) (h : History) :
    World → History → Prop where
  | entry : Point pid packet ret w h w h
  | guarded : Point pid packet ret w h (guardedWorld ret w) h
  | update (successful : (ret==0)=true)
      (point : TxAccountingAccess.RootPoint pid packet.value.bytes.length (guardedWorld ret w) h u middle) :
      Point pid packet ret w h u middle
  | returned (performed : runPrefix (action pid packet ret) w h=(.ok (sent,u),middle)) :
      Point pid packet ret w h u middle

theorem Point.remaining (point : Point pid packet ret w h u middle) :
    ∃remaining,runPrefix (action pid packet ret) w h=runPrefix remaining u middle := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | guarded=>exact ⟨_,after_guard pid packet ret w h⟩
  | update successful point=>
      obtain ⟨remaining,continued⟩:=point.remaining
      refine ⟨remaining >>= fun _=>pure (ret==0),?_⟩
      rw [after_guard]
      simp only [guardedBody,successful,ite_true]
      exact Scheduler.bind_run_equal _ continued
  | returned performed=>exact ⟨pure _,performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxAccounting
