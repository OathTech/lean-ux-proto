import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialTimerFrames
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialTimerFrames

/-! Same-journal RX certificate transport through all five timer arms and
actual delayed workers. History before a stopped callback remains certified. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

theorem expired_keepalive (pid : PeerId) :
    StateSafe (Driver.expiredKeepaliveObserved Journal.hooks pid) := by
  rw [Driver.expiredKeepalive_lift Journal.hooks rfl]
  apply state_bind (keepalive pid)
  intro _
  apply state_bind (state_native _ (fun _ => bounded_read_peer pid))
  intro p
  apply state_bind (state_ambient _)
  intro another
  split
  · apply state_bind (state_native _ (fun _ => bounded_read_peer pid))
    intro saved
    apply state_bind (state_native _ (fun _ => bounded_set_peer pid _))
    intro _
    exact state_native _ (fun h => discard_view_spec id (Bounded h) _ (TimerFrames.modify_timer _ _ _ _))
  · exact state_pure ()

theorem persistent (pid : PeerId) : StateSafe (Driver.persistentObserved Journal.hooks pid) := by
  rw [Driver.persistent_lift Journal.hooks]
  apply state_bind (state_native _ (fun _ => bounded_read_peer pid))
  intro p
  apply state_bind (state_ambient _)
  intro active
  split
  · exact keepalive pid
  · exact state_pure ()

theorem timer (pid : PeerId) (t : PeerTimer) :
    StateSafe (Driver.timerObserved Journal.hooks pid t) := by
  cases t with
  | retransmitHandshake =>
    rw [Driver.timer_retransmit_lift Journal.hooks rfl]
    exact state_native _ (fun _ => TimerFrames.retransmit pid)
  | sendKeepalive => exact expired_keepalive pid
  | newHandshake =>
    rw [Driver.timer_new_lift Journal.hooks rfl]
    exact state_native _ (fun _ => TimerFrames.new_handshake pid)
  | zeroKeyMaterial => exact state_native _ (fun _ => TimerFrames.expired_zero pid)
  | persistentKeepalive => exact persistent pid

theorem wg_read : ProductSafe (liftPrefix getWG) :=
  product_store _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductSafe (liftPrefix (modifyWG f)) :=
  product_store _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductSafe (liftPrefix getEnv) := by
  apply product_lift
  intro h
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hi run
  cases run
  exact hi

theorem send_one : ProductSafe (liftPrefix Env.runOneSendWorker) :=
  product_lift _ (fun _ => ResidentMaterial.send_one_preserves
    (bounded_store getDev_sameWGStore) TimerFrames.flushed_send)

theorem clear_one : ProductSafe (liftPrefix Env.runOneClearWorker) :=
  product_lift _ (fun _ => ResidentMaterial.clear_one_preserves
    (bounded_store getDev_sameWGStore) TimerFrames.flushed_clear)

theorem timer_selected (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (we : WheelEntry) :
    ProductSafe (Journal.hooks.timerSelected d j pid t we) := by
  intro w h hi
  rw [show Journal.hooks.timerSelected d j pid t we =
    AuthenticatedEffects.TimerDispatch.scope Journal.Event.timerSelected d j pid t we (pure 0) from rfl,
    AuthenticatedEffects.TimerDispatch.scope_run,runPrefix_pure]
  have quiet : Quiet (.timerSelected ⟨d,j,pid,t,we,w⟩) := ⟨rfl,by intro p k r impossible; cases impossible⟩
  have good := hi.2.quiet (suffix := [.timerSelected ⟨d,j,pid,t,we,w⟩]) (by simpa using quiet)
  refine ⟨[.timerSelected ⟨d,j,pid,t,we,w⟩],rfl,good,?_⟩
  exact ⟨by rw [List.filterMap_append]; exact bounded_append hi.1,good⟩

theorem timer_finished (token : Nat) : ProductSafe (Journal.hooks.timerFinished token) := product_pure _

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial.Execution
