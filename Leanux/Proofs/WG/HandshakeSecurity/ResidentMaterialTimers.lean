import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialTimerFrames

/-! Actual timer callbacks and delayed workers preserve the material carrier.
Peer/key cleanup uses native C1 slot facts rather than an H1 hypothesis. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder

theorem expired_keepalive_carrier (pid : PeerId) :
    CarrierSafe (Driver.expiredKeepaliveObserved Journal.hooks pid) := by
  rw [Driver.expiredKeepalive_lift Journal.hooks rfl]
  apply StatePrefixEnsures.bind (keepalive_carrier pid)
  intro _
  apply StatePrefixEnsures.bind (carrier_lift _ (fun _ => NativeFrames.read_peer pid) (bounds_read_peer pid))
  intro p
  apply StatePrefixEnsures.bind (carrier_ambient _)
  intro another
  split
  · apply StatePrefixEnsures.bind (read_saved pid)
    intro saved
    apply StatePrefixEnsures.bind (write_saved pid saved
      (fun p => {p with timerNeedAnotherKeepalive := false}) (fun _ => rfl) (fun _ => rfl))
    intro _
    apply carrier_lift
    · intro h
      exact discard_view_spec id (Inv h) _ (NativeFrames.modify_timer _ _ _ _)
    · exact discard_view_spec id Bounds _ (bounds_forget (DriverCuts.carrier_modify_timer _ _ _ _))
  · exact carrier_pure ()

theorem persistent_carrier (pid : PeerId) : CarrierSafe (Driver.persistentObserved Journal.hooks pid) := by
  rw [Driver.persistent_lift Journal.hooks]
  apply StatePrefixEnsures.bind (carrier_lift _ (fun _ => NativeFrames.read_peer pid) (bounds_read_peer pid))
  intro p
  apply StatePrefixEnsures.bind (carrier_ambient _)
  intro active
  split
  · exact keepalive_carrier pid
  · exact carrier_pure ()

theorem timer_carrier (pid : PeerId) (t : PeerTimer) :
    CarrierSafe (Driver.timerObserved Journal.hooks pid t) := by
  cases t with
  | retransmitHandshake =>
    rw [Driver.timer_retransmit_lift Journal.hooks rfl rfl rfl]
    exact carrier_lift _ (fun _ => NativeFrames.retransmit pid) (bounds_forget (DriverCuts.carrier_retransmit pid))
  | sendKeepalive => exact expired_keepalive_carrier pid
  | newHandshake =>
    rw [Driver.timer_new_lift Journal.hooks rfl rfl]
    exact carrier_lift _ (fun _ => NativeFrames.new_handshake pid) (bounds_forget (DriverCuts.carrier_new_handshake pid))
  | zeroKeyMaterial =>
    exact carrier_lift _ (fun _ => NativeFrames.expired_zero pid) (bounds_forget (DriverCuts.carrier_zero_material pid))
  | persistentKeepalive => exact persistent_carrier pid

theorem wg_read : ProductSafe (liftPrefix getWG) :=
  product_store _ (fun initial => productGetWG_spec (· = initial))

theorem wg_bookkeeping (f : WGWorld → WGWorld) (same : ∀ w, wgStoreView (f w) = wgStoreView w) :
    ProductSafe (liftPrefix (modifyWG f)) :=
  product_store _ (fun initial => productModifyWG_spec (· = initial) f same)

theorem env_read : ProductSafe (liftPrefix getEnv) := by
  apply product_lift
  · intro h
    apply (hoare_iff_run _ _ _).mpr
    intro w x v hi run
    cases run
    exact hi
  · apply (hoare_iff_run _ _ _).mpr
    intro w x v hi run
    cases run
    exact hi

theorem send_one_carrier : ProductSafe (liftPrefix Env.runOneSendWorker) :=
  product_lift _
    (fun _ => send_one_preserves (NativeFrames.store getDev_sameWGStore) NativeFrames.flushed_send)
    (bounds_forget_product DriverCuts.carrier_send_one)

theorem clear_one_carrier : ProductSafe (liftPrefix Env.runOneClearWorker) :=
  product_lift _
    (fun _ => clear_one_preserves (NativeFrames.store getDev_sameWGStore) NativeFrames.flushed_clear)
    (clear_one_preserves (bounds_store getDev_sameWGStore) bounds_flushed_clear)

theorem timer_selected_carrier (d : Device) (j : UInt64) (pid : PeerId) (t : PeerTimer) (we : WheelEntry) :
    ProductSafe (Journal.hooks.timerSelected d j pid t we) := by
  intro w h hi
  rw [show Journal.hooks.timerSelected d j pid t we =
    AuthenticatedEffects.TimerDispatch.scope Journal.Event.timerSelected d j pid t we (pure 0) from rfl,
    AuthenticatedEffects.TimerDispatch.scope_run,runPrefix_pure]
  have good := hi.1.2.quiet (event := .timerSelected ⟨d,j,pid,t,we,w⟩) (fun _ eq => by cases eq)
  exact ⟨[.timerSelected ⟨d,j,pid,t,we,w⟩],rfl,good,
    ⟨⟨hi.1.1.mono (fun _ member => List.mem_append_left _ member),good⟩,hi.2⟩⟩

theorem timer_finished_carrier (token : Nat) : ProductSafe (Journal.hooks.timerFinished token) :=
  product_pure _

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
