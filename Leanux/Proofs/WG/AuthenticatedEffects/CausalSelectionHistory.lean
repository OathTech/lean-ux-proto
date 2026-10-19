import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedSend
import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedProduct

/-! Positional delayed-selection evidence in the same final journal. A work
entry must select the first matching live ticket, preserving duplicates; a
timer selection must name its actual saved device and an earlier native arm.
These definitions do not authorize the earlier receipt's own cause. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

def WorkOrigin (h : List Event) (pid : PeerId) (entry : CausalSources.SendEntry) : Prop :=
  ∃ tickets ticket rest,
    entry.queue.getD [] = tickets.map QueuedOccurrences.Ticket.peer ∧
    (tickets.map QueuedOccurrences.Ticket.index).Nodup ∧
    (∀ t ∈ tickets, t.Valid Event.queued h) ∧
    QueuedOccurrences.Selected tickets pid ticket rest

def TimerOrigin (h : List Event) (r : TimerDispatch.Selection) : Prop :=
  r.Valid ∧ ∃ stamp expires,
    TimerSlots.Pending r.before.wg r.peer r.timer stamp expires r.entry ∧
    TimerOccurrences.HasCause Event.armed h r.peer r.timer stamp expires r.entry

def TimerEntry (pre : List Event) (bound : UInt64) (pid : PeerId)
    (timer : PeerTimer) (entry : WheelEntry) : Prop :=
  ∃ before receipt, pre = before ++ [Event.old (.timerSelected receipt)] ∧
    receipt.bound = bound ∧ receipt.peer = pid ∧ receipt.timer = timer ∧ receipt.entry = entry ∧
    TimerOrigin before receipt

def Checked (pre : List Event) : Event → Prop
  | .old (.timerSelected r) => TimerOrigin pre r
  | .scope (.entered ⟨_,.sendWork pid entry⟩) => WorkOrigin pre pid entry
  | .scope (.entered ⟨_,.timer bound pid timer entry⟩) => TimerEntry pre bound pid timer entry
  | _ => True

def Safe (history : List Event) : Prop :=
  ∀ pre event post, history = pre ++ event :: post → Checked pre event

def Quiet : Event → Prop
  | .old (.timerSelected _) | .scope (.entered ⟨_,.sendWork _ _⟩)
    | .scope (.entered ⟨_,.timer _ _ _ _⟩) => False
  | _ => True

theorem Safe.empty : Safe [] := by
  intro pre event post position
  have sizes := congrArg List.length position
  simp at sizes

theorem Safe.append (hi : Safe h)
    (checked : ∀ pre event post, suffix = pre ++ event :: post → Checked (h ++ pre) event) :
    Safe (h ++ suffix) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.HistorySupport.«0».Leanux.Proofs.WG.Origins.HistorySupport.positions_append)
    Checked h suffix hi checked

theorem quiet_checked (event : Event) (quiet : Quiet event) (pre : List Event) : Checked pre event := by
  cases event with
  | old old => cases old <;> first | exact quiet.elim | trivial
  | scope scope =>
    cases scope with
    | entered token => cases token with | mk index cause => cases cause <;> first | exact quiet.elim | trivial
    | exited index => trivial
  | stagingTaken _ | stagedRestored _ | terminalDrop _ => trivial
  | transmitInput _ | stagedDisposal _ | sendResult _ => trivial
  | delivery _ | cookieConsumed _ | armed _ | queued _ | exchange _ | keepalivePrepared _ _ | protocolSocket _ | cookieSocket _ => trivial

theorem Safe.emit (hi : Safe h) (checked : Checked h event) : Safe (h ++ [event]) := by
  apply hi.append
  intro pre entry post position
  cases pre with
  | nil => cases position; simpa only [List.append_nil] using checked
  | cons first rest =>
    have sizes := congrArg List.length position
    simp only [List.length_append,List.length_cons,List.length_nil] at sizes
    omega

theorem Safe.quiet (hi : Safe h) (quiet : ∀ event ∈ suffix, Quiet event) : Safe (h ++ suffix) := by
  apply hi.append
  intro pre event post position
  apply quiet_checked event
  apply quiet event
  rw [position]
  simp

theorem WorkOrigin.of_carrier (h : List Event) (w : WGWorld) (pid : PeerId)
    (carrier : QueuedOccurrences.Inv Event.queued h w)
    (present : pid ∈ QueuedOccurrences.queue w) : WorkOrigin h pid (CausalSources.sendEntry pid w) := by
  obtain ⟨tickets,queue,unique,valid⟩ := carrier
  obtain ⟨ticket,rest,selected⟩ := QueuedOccurrences.select_exists tickets pid (queue ▸ present)
  exact ⟨tickets,ticket,rest,queue,unique,valid,selected⟩

theorem TimerOrigin.of_carrier (h : List Event) (r : TimerDispatch.Selection)
    (valid : r.Valid) (carrier : TimerOccurrences.Carrier Event.armed h r.before.wg) : TimerOrigin h r := by
  obtain ⟨p,resident,wheel⟩ := TimerSlots.due_resident r.saved r.bound r.peer r.timer r.entry
    (TimerSlots.nextDue_member r.saved r.bound r.peer r.timer r.entry valid.2)
  have pending : TimerSlots.Pending r.before.wg r.peer r.timer p.internalId (p.timer r.timer) r.entry := by
    simp [TimerSlots.Pending,TimerSlots.view,valid.1,resident,wheel]
  exact ⟨valid,p.internalId,p.timer r.timer,pending,carrier _ _ _ _ _ pending⟩

theorem WorkOrigin.receipt (origin : WorkOrigin h pid entry) :
    ∃ ticket rest before after tickets,
      QueuedOccurrences.Selected tickets pid ticket rest ∧ ticket.peer = pid ∧
      entry.queue.getD [] = tickets.map QueuedOccurrences.Ticket.peer ∧
      h = before ++ Event.queued ticket.receipt :: after ∧ before.length = ticket.index ∧
      ticket.receipt.Valid := by
  obtain ⟨tickets,ticket,rest,queue,_,valid,selected⟩ := origin
  have decomposition := selected
  obtain ⟨left,right,split,_,peer,_⟩ := decomposition
  have receipt := valid ticket (by rw [split]; simp)
  obtain ⟨before,after,position,index⟩ := receipt.position
  exact ⟨ticket,rest,before,after,tickets,selected,peer,queue,position,index,receipt.2⟩

theorem Safe.work (safe : Safe history)
    (position : history = pre ++ Event.scope (.entered ⟨index,.sendWork pid entry⟩) :: post) :
    WorkOrigin pre pid entry := safe pre _ post position

theorem Safe.timer (safe : Safe history)
    (position : history = pre ++ Event.old (.timerSelected receipt) :: post) :
    TimerOrigin pre receipt := safe pre _ post position

theorem Safe.timer_entry (safe : Safe history)
    (position : history = pre ++ Event.scope (.entered ⟨index,.timer bound pid t entry⟩) :: post) :
    TimerEntry pre bound pid t entry := safe pre _ post position

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Selections
