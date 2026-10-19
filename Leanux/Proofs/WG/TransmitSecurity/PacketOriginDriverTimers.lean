import Leanux.Proofs.WG.TransmitSecurity.PacketOriginDriverScheduler
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimerFrames

/-! Native timer callbacks retain TX allocation origins; keepalive callbacks
enter the same observed staging path as ordinary transmission. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity
set_option maxHeartbeats 600000

theorem expired_keepalive (pid : PeerId) : StateSafe (Driver.expiredKeepaliveObserved Journal.hooks pid) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  rw [Driver.expiredKeepalive_lift Journal.hooks rfl]
  simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
    | (nonce_source_head modifyDev; exact state_lift _ (fun _ => frame (PacketOrigins.modify _ (fun _ => rfl) (fun _ => rfl))))
    | (nonce_source_head modPeerTimer; exact state_lift _ (fun _ => frame (snapshot_wire (modPeerTimer_cryptWire _ _ _ _))))
    | origin_driver_step
  all_goals exact state_lift _ (fun _ =>
    preserves_bind (frame (snapshot_wire (modPeerTimer_cryptWire _ _ _ _)))
      (fun _ => preserves_pure _))

theorem persistent (pid : PeerId) : StateSafe (Driver.persistentObserved Journal.hooks pid) := by
  change StatePrefixPreserves (fun h w _ => JournalInv h w) Safe _
  rw [Driver.persistent_lift Journal.hooks]
  repeat' first
    | (nonce_source_head Driver.keepaliveObserved; exact keepalive _)
    | origin_driver_step

theorem timer (pid : PeerId) (t : PeerTimer) : StateSafe (Driver.timerObserved Journal.hooks pid t) := by
  cases t with
  | retransmitHandshake =>
    rw [Driver.timer_retransmit_lift Journal.hooks rfl]
    exact state_lift _ (fun _ => frame (snapshot_wire (OccurrenceTimers.retransmit_wire pid)))
  | sendKeepalive => exact expired_keepalive pid
  | newHandshake =>
    rw [Driver.timer_new_lift Journal.hooks rfl]
    exact state_lift _ (fun _ => frame (snapshot_wire (OccurrenceTimers.new_handshake_wire pid)))
  | zeroKeyMaterial => exact state_lift _ (fun _ => frame (snapshot_wire (OccurrenceTimers.expired_zero_wire pid)))
  | persistentKeepalive => exact persistent pid

theorem product_wire {action : Leanux.M α} (same : SameView (fun w : World => txCryptWire w.wg) action) :
    ProductSafe (liftPrefix action) := by
  exact product_lift _ (fun _ => product_wire_inv same)

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
  product_wire OccurrenceDeferred.send_one_wire

theorem clear_one : ProductSafe (liftPrefix Env.runOneClearWorker) :=
  product_wire OccurrenceDeferred.clear_one_wire

theorem timer_selected (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (we : WheelEntry) :
    ProductSafe (Journal.hooks.timerSelected d j pid t we) := by
  intro w h hi
  rw [show Journal.hooks.timerSelected d j pid t we =
    AuthenticatedEffects.TimerDispatch.scope Journal.Event.timerSelected d j pid t we (pure 0) from rfl,
    AuthenticatedEffects.TimerDispatch.scope_run,runPrefix_pure]
  have good := hi.2.quiet (event := .timerSelected ⟨d,j,pid,t,we,w⟩) (fun _ eq => by cases eq)
  exact ⟨[.timerSelected ⟨d,j,pid,t,we,w⟩],rfl,good,
    hi.1.mono (fun _ member => List.mem_append_left _ member),good⟩

theorem timer_finished (token : Nat) : ProductSafe (Journal.hooks.timerFinished token) :=
  product_pure _

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
