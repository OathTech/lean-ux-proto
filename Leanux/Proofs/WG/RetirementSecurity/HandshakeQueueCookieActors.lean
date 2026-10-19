import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueCookieEffects
import Leanux.Proofs.WG.AuthenticatedEffects.CausalJournalOldProjection

/-! All concrete final-journal hooks except the checked-pop handshake preserve
cookie input-size history independently of state. The handshake remains a
separate physical-ring obligation and is neutral only in this helper instance. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Cookie
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity AuthenticatedEffects
open CausalJournal CookieInput HandshakeSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem old_state (body : WGPrefix TransmitSecurity.Journal.Event α) :
    Driver.StateHistorySafe Safe (state body) := quiet_state Event.old old? (fun _=>True.intro) body
private theorem old_product (body : PrefixM TransmitSecurity.Journal.Event α) :
    Driver.ProductHistorySafe Safe (product body) := quiet_product Event.old old? (fun _=>True.intro) body

theorem session (pid : PeerId) : Driver.StateHistorySafe Safe (CausalJournal.session pid) :=
  receipt_quiet _ (old_state _) _ (fun _=>True.intro)

private theorem selected (d : Device) (j : UInt64) (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) :
    Driver.ProductHistorySafe Safe (hooks.timerSelected d j pid timer entry) := by
  intro w h hi
  exact Driver.History.product_bind
    (product_emit (.old (.timerSelected ⟨d,j,pid,timer,entry,w⟩)) True.intro)
    (fun _=>product_enter (.timer j pid timer entry)) w h hi

private theorem front_select (family : Nat) (packets : List Packet) (mtu : Nat) (peer : Option PeerId) :
    Driver.StateHistorySafe Safe (StagedConservation.Front.selectWith
      (StagedConservation.Front.observedOps Event.stagedDisposal stagedDisposal?) family packets mtu peer) := by
  unfold StagedConservation.Front.selectWith
  simp only [StagedConservation.Front.observedOps]
  repeat' first
    | (driver_history_head focusStatePrefix; exact quiet_state Event.stagedDisposal stagedDisposal? (fun _=>True.intro) _)
    | driver_state_history_step

private theorem front_body (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (StagedConservation.Front.frontWith
      (StagedConservation.Front.observedOps Event.stagedDisposal stagedDisposal?) family addr packets mtu) := by
  unfold StagedConservation.Front.frontWith
  simp only [StagedConservation.Front.observedOps]
  repeat' first
    | (driver_history_head StagedConservation.Front.selectWith; exact front_select _ _ _ _)
    | driver_state_history_step

private theorem front (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Driver.StateHistorySafe Safe (CausalJournal.front family addr packets mtu) := by
  unfold CausalJournal.front StagedConservation.Front.observed
  exact Driver.History.state_bind (emit_quiet _ True.intro) fun _=>
    receipt_quiet _ (front_body family addr packets mtu) _ (fun _=>True.intro)

theorem quiet_hooks : Driver.HooksHistorySafe Safe (Journal.quietHooks CausalJournal.hooks) where
  stagedPurge := fun _=>quiet_state Event.stagedDisposal stagedDisposal? (fun _=>True.intro) _
  peerRelease := fun _=>quiet_state Event.stagedDisposal stagedDisposal? (fun _=>True.intro) _
  deliver := by
    change Driver.ProductHistorySafe Safe (DeliverySource.observed Event.delivery)
    unfold DeliverySource.observed
    exact Driver.History.product_bind (Driver.History.product_lift _) (fun w=>
      Driver.History.product_bind (product_emit (.delivery w.sent) True.intro) (fun _=>Driver.History.product_lift _))
  keepalivePrepare := fun _=>receipt_quiet _ (Driver.History.state_lift _) _ (fun _=>True.intro)
  fixtureEnter := fun trigger=>state_enter (.fixture trigger)
  fixtureLeave := state_leave
  handshake := fun _ _ _ _=>Driver.History.state_pure false
  sendWorker := send_worker
  flushedSend := flushed_send
  armTimer := effects_safe.arm
  queueSend := effects_safe.append
  candidateEnter := fun skb packet=>product_enter (.candidate skb packet)
  candidateLeave := product_leave
  stackInput := fun entry _ preserves=>product_scope (.stackInput entry) _ (fun _=>preserves)
  prepare := old_product _
  counterCheck := fun _ _=>old_product _
  timerSelected := selected
  timerFinished := product_leave
  selection := fun _=>old_state _
  confirmation := fun _ _=>old_state _
  session := session
  reserve := fun _=>old_state _
  allocate := fun _=>old_state _
  create := fun _ _=>old_state _
  front := front
  poll := old_product _
  encrypt := fun _=>old_product _
  transmit := transmit

theorem keepalive (pid : PeerId) : Driver.StateHistorySafe Safe (Driver.keepaliveObserved CausalJournal.hooks pid) :=
  Driver.keepalive_history quiet_hooks pid

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths.Cookie
