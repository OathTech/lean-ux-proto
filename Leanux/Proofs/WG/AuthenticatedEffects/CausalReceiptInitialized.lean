import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptSend
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CausalReceiptCompletion
import Leanux.Proofs.WG.TransmitSecurity.DriverHistoryOuter

/-! Initialized receipt integrity on the final shared Driver. This establishes
native effect witnesses and exact current-token attribution, not that every
token is authorized or that a missing/malformed context is unreachable. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity

private theorem old_state (body : WGPrefix Journal.Event α) :
    Driver.StateHistorySafe Safe (state body) := quiet_state Event.old old? (fun _ => True.intro) body

private theorem old_product (body : PrefixM Journal.Event α) :
    Driver.ProductHistorySafe Safe (product body) := quiet_product Event.old old? (fun _ => True.intro) body

private theorem session (pid : PeerId) : Driver.StateHistorySafe Safe (CausalJournal.session pid) :=
  receipt_quiet _ (old_state _) _ (fun _ => True.intro)

private theorem selected (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    Driver.ProductHistorySafe Safe (hooks.timerSelected d j pid timer entry) := by
  intro w h hi
  exact Driver.History.product_bind
    (product_emit (.old (.timerSelected ⟨d,j,pid,timer,entry,w⟩)) True.intro)
    (fun _ => product_enter (.timer j pid timer entry)) w h hi

theorem hooks_safe : Driver.HooksHistorySafe Safe hooks where
  fixtureEnter := fun trigger => state_enter (.fixture trigger)
  fixtureLeave := state_leave
  handshake := handshake
  sendWorker := send_worker
  flushedSend := flushed_send
  armTimer := arm
  queueSend := queue
  candidateEnter := fun skb packet => product_enter (.candidate skb packet)
  candidateLeave := product_leave
  stackInput := fun entry _ preserves => product_scope (.stackInput entry) _ (fun _ => preserves)
  prepare := old_product _
  counterCheck := fun _ _ => old_product _
  timerSelected := selected
  timerFinished := product_leave
  selection := fun _ => old_state _
  confirmation := fun _ _ => old_state _
  session := session
  reserve := fun _ => old_state _
  allocate := fun _ => old_state _
  create := fun _ _ => old_state _
  front := fun _ _ _ _ => old_state _
  poll := old_product _
  encrypt := fun _ => old_product _
  transmit := transmit

theorem initialized (trace : Runner.Trace) (placeholders : Bool) :
    Safe (runPrefixOuter (execute trace placeholders) []).2 :=
  Driver.initialized_history hooks_safe Safe.empty trace placeholders

theorem initialized_arm (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : TimerEffects.Arm Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ Event.armed receipt :: post) :
    receipt.Valid ∧ receipt.cause = CausalScope.current scope? pre :=
  initialized trace placeholders pre (.armed receipt) post position

theorem initialized_queue (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List Event) (receipt : TimerEffects.Queued Context)
    (position : (runPrefixOuter (execute trace placeholders) []).2 = pre ++ Event.queued receipt :: post) :
    receipt.Valid ∧ receipt.cause = CausalScope.current scope? pre :=
  initialized trace placeholders pre (.queued receipt) post position

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Receipts
