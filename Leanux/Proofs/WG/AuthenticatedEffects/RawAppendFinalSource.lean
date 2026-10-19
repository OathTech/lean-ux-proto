import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendCompletionProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptNestedFrames
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuietActors

/-! The raw selector describes actual singleton native appends. It ignores
candidate scopes, allocations and disposal markers; those cannot manufacture
an append occurrence. The independent target is the same Driver instantiated
with direct original-append callbacks. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
abbrev FinalEvent := CausalJournal.Event

def journal? : Journal.Event → Option RawAppend.Event
  | .socket receipt => ofSent receipt.socket.before.wg.sent receipt.socket.after.wg.sent
  | _ => none

def raw? : FinalEvent → Option RawAppend.Event
  | .old event => journal? event
  | .protocolSocket receipt => ofSent receipt.run.before.sent receipt.run.after.sent
  | .cookieSocket receipt => some (datagramEvent receipt.datagram)
  | _ => none

theorem effects : TimerEffects.Ops.Projects raw? CausalJournal.effects TimerEffects.lifted :=
  CausalEffects.ops_projects CausalJournal.scope? CausalJournal.Event.armed CausalJournal.Event.queued raw?
    (fun _ => rfl) (fun _ => rfl)

theorem handshake (sg : PeerId → WGPrefix FinalEvent Bool)
    (st : PeerId → WGPrefix RawAppend.Event Bool)
    (kg : PeerId → WGPrefix FinalEvent Unit)
    (kt : PeerId → WGPrefix RawAppend.Event Unit)
    (hs : ∀ pid, StateProjectsPrefix raw? id (sg pid) (st pid))
    (hk : ∀ pid, StateProjectsPrefix raw? id (kg pid) (kt pid)) :
    StateProjectsPrefix raw? id (CausalJournal.handshake sg kg) (RawAppend.handshake st kt) := by
  apply CookieConsumption.worker_projects raw? _ _ _ _
  · intro msg
    exact HandshakeSecurity.Exchange.quiet_native_projection raw? _ _
      (CausalJournal.CallbackFrames.cookie_erases msg)
      (CausalJournal.CallbackFrames.cookie_quiet raw? (fun _ => rfl) (fun _ => rfl) msg).2
  intro mac
  apply HandshakeEffects.scopeOps_projects raw? CausalJournal.Event.scope CausalSources.Cause.handshake (fun _ => rfl)
  apply HandshakeSecurity.ExchangeJoint.receive_ignored raw? CausalJournal.Event.exchange (fun _ => rfl)
  refine {receive_effects_projects raw? (CausalJournal.Event.old ∘ Journal.Event.handshake)
    CausalJournal.handshake? (fun _ => rfl) CausalJournal.effects effects
    sg st kg kt hs hk mac CausalJournal.Event.protocolSocket CausalJournal.scope? CausalJournal.Event.cookieSocket
    (fun _ => rfl) (fun _ => rfl) with initiation := ?_, response := ?_, put := ?_}
  · intro msg
    exact HandshakeSecurity.Exchange.quiet_native_projection raw? _ _
      (CausalJournal.CallbackFrames.initiation_erases {mac with input := msg})
      (CausalJournal.CallbackFrames.initiation_quiet raw? (fun _ => rfl) (fun _ => rfl) _).2
  · intro msg
    exact HandshakeSecurity.Exchange.quiet_native_projection raw? _ _
      (CausalJournal.CallbackFrames.response_erases {mac with input := msg})
      (CausalJournal.CallbackFrames.response_quiet raw? (fun _ => rfl) (fun _ => rfl) _).2
  · intro peer
    exact HandshakeSecurity.StagedDisposal.Decoration.release_projects CausalJournal.Event.stagedDisposal
      CausalJournal.stagedDisposal? raw? (fun _ => rfl) peer

theorem flushed (pid : PeerId) :
    StateProjectsPrefix raw? id (CausalJournal.flushedSend pid) (RawAppend.flushed pid) := by
  have source := SendEffects.flushed_projects raw? CausalJournal.Event.scope (fun _ => rfl)
    (HandshakeSecurity.ExchangeJoint.send_ignored raw? CausalJournal.Event.exchange (fun _ => rfl) _ _
      (HandshakeSecurity.StagedDisposal.Decoration.send_projects CausalJournal.Event.stagedDisposal
        CausalJournal.stagedDisposal? raw? (fun _ => rfl)
        (send_projects raw? CausalJournal.Event.protocolSocket CausalJournal.scope? (fun _ => rfl))
        (fun _ => rfl))) effects pid
  have neutral : SendEffects.withEffects RawAppend.sendOps TimerEffects.lifted = RawAppend.sendOps := by
    simp only [SendEffects.withEffects,TimerEffects.traversal_lifted,TimerEffects.initiated_lifted,
      RawAppend.sendOps,SendEffects.native]
  simpa only [CausalJournal.flushedSend,RawAppend.flushed,neutral] using source

private theorem state_erasure (ρ : E → Option F) {g : WGPrefix E α} {t : WGPrefix F α}
    {native : WG.M α} (projection : StateProjectsPrefix ρ id g t) (erases : ErasesStatePrefix t native) :
    ErasesStatePrefix g native := by
  intro w a h
  have result := congrArg Prod.fst (projection w a h)
  change (runStatePrefix t w a (h.filterMap ρ)).1 = Except.map id _ at result
  simp only [Except.map_id] at result
  exact result.symm.trans (erases w a (h.filterMap ρ))

private theorem product_erasure (ρ : E → Option F) {g : PrefixM E α} {t : PrefixM F α}
    {native : Leanux.M α} (projection : ProjectsPrefix ρ id g t) (erases : ErasesPrefix t native) :
    ErasesPrefix g native := by
  intro w h
  have result := congrArg Prod.fst (projection w h)
  change (runPrefix t w (h.filterMap ρ)).1 = Except.map id _ at result
  simp only [Except.map_id] at result
  exact result.symm.trans (erases w (h.filterMap ρ))

private theorem old_completion : CompletionEffects.Ops.Projects journal?
    (CompletionEffects.focused Journal.completionEvent Journal.completion?) completionOps :=
  focused_completion_projects journal? Journal.completionEvent Journal.completion?
    (fun event => by cases event <;> rfl)

private theorem lifetime : LifetimeEffects.Ops.Projects raw? CausalJournal.completionLifetime lifetimeLifted := by
  have base := LifetimeEffects.decorate_projects raw? _ _
    (lifetime_base_projects raw? (CausalJournal.Event.old ∘ Journal.completionEvent)
      CausalJournal.completion? (fun event => by cases event <;> rfl))
    CausalJournal.scope? CausalJournal.Event.armed CausalJournal.Event.queued (fun _ => rfl) (fun _ => rfl)
  refine {base with put := ?_}
  intro peer
  apply HandshakeSecurity.Exchange.quiet_native_projection raw? _ _
  · apply state_erasure CausalJournal.old? (CausalJournal.completionLifetime_projects.put peer)
    apply state_erasure journal? ((lifetime_base_projects journal? Journal.completionEvent Journal.completion?
      (fun event => by cases event <;> rfl)).put peer)
    exact erasesStatePrefix_lift _
  · exact (CausalJournal.CallbackQuiet.peer raw? _ _ (fun _ => rfl) (fun _ => rfl) peer).2

private theorem completion_ops : CompletionEffects.Ops.Projects raw? CausalJournal.completionOps completionOps := by
  have base := HandshakeSecurity.StagedConservation.SendResult.decorate_projects CausalJournal.Event.sendResult raw?
    (fun _ => rfl)
    (observed_completion_projects raw? (CausalJournal.Event.old ∘ Journal.completionEvent)
      CausalJournal.completion? (fun event => by cases event <;> rfl)
      CausalJournal.scope? CausalJournal.Event.armed CausalJournal.Event.queued (fun _ => rfl) (fun _ => rfl))
  refine {base with dispose := ?_, fresh := ?_}
  · intro pid item key
    apply (CausalJournal.CallbackQuiet.dispose raw? (fun _ => rfl) (fun _ => rfl) pid item key).2.project
    exact product_erasure CausalJournal.old? (CausalJournal.completionOps_projects.dispose pid item key)
      (product_erasure journal? (old_completion.dispose pid item key) (erasesPrefix_lift _))
  · intro pid
    have projected := (LifetimeEffects.fresh_projects raw? lifetime pid).liftWGObserver raw? id
    simpa only [CausalJournal.completionOps,completionOps,lifetime_fresh,liftWGObserver_lift] using projected

theorem transmit (pid : PeerId) :
    ProjectsPrefix raw? id (CausalJournal.transmit pid) (RawAppend.completion pid) := by
  unfold RawAppend.completion
  rw [← CompletionEffects.stepSource_factor]
  apply HandshakeSecurity.StagedConservation.Terminal.step_projects raw? completion_ops _ _
    (CompletionEffects.completeScoped_projects raw? CausalJournal.Event.scope CausalSources.Cause.completion
      (fun _ => rfl) completion_ops) _ ?_ pid
  intro peer item head
  apply (CausalJournal.CallbackQuiet.dead raw? (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) peer item head).2.project
  apply product_erasure CausalJournal.old?
    (HandshakeSecurity.StagedConservation.Terminal.deadObserved_projects CausalJournal.old?
      CausalJournal.txEvent CausalJournal.txEvent? Journal.Event.disposition Journal.disposition?
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      CausalJournal.Event.stagedDisposal (fun _ => rfl) CausalJournal.Event.terminalDrop (fun _ => rfl) peer item head)
  exact focusPrefix_erases Journal.Event.disposition Journal.disposition? (TxDisposition.dispose_erases peer item head.keypair)

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
