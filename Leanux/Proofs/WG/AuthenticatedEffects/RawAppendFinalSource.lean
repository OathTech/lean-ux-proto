import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendCompletionProjection
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

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
    exact CookieConsumption.observed_projects raw? CausalJournal.Event.cookieConsumed (fun _ => rfl) msg
  intro mac
  apply HandshakeEffects.scopeOps_projects raw? CausalJournal.Event.scope CausalSources.Cause.handshake (fun _ => rfl)
  apply HandshakeSecurity.ExchangeJoint.receive_ignored raw? CausalJournal.Event.exchange (fun _ => rfl)
  refine {receive_effects_projects raw? (CausalJournal.Event.old ∘ Journal.Event.handshake)
    CausalJournal.handshake? (fun _ => rfl) CausalJournal.effects effects
    sg st kg kt hs hk mac CausalJournal.Event.protocolSocket CausalJournal.scope? CausalJournal.Event.cookieSocket
    (fun _ => rfl) (fun _ => rfl) with put := ?_}
  intro peer
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

theorem transmit (pid : PeerId) :
    ProjectsPrefix raw? id (CausalJournal.transmit pid) (RawAppend.completion pid) :=
  CompletionEffects.stepScoped_projects raw? CausalJournal.Event.scope CausalSources.Cause.completion
    (fun _ => rfl)
    (HandshakeSecurity.StagedConservation.SendResult.decorate_projects CausalJournal.Event.sendResult raw?
      (fun _ => rfl)
      (observed_completion_projects raw? (CausalJournal.Event.old ∘ Journal.completionEvent)
        CausalJournal.completion? (fun event => by cases event <;> rfl)
        CausalJournal.scope? CausalJournal.Event.armed CausalJournal.Event.queued (fun _ => rfl) (fun _ => rfl))) pid

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend.Final
