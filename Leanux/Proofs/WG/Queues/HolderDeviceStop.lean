import Leanux.Proofs.WG.Queues.HolderTimerCallbacks
import Leanux.Proofs.WG.Queues.HolderDrains
import Leanux.Proofs.Framing.WGSocketLifecycle

/-! Native device shutdown retains the supplied complete account through
actual timer/work drains and key clearing. The source's queued-handshake Stop
remains; a normal return does not assert that crypt queues were drained. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceStop
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

private theorem read : Preserves (Boundary cs loans) getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a d v b hi run
  exact (DecryptCarrier.getDev_current a b run).1 ▸ hi

private theorem modify (f : Device → Device)
    (same : ∀ w : WGWorld, HolderEncrypt.fields {w with dev:=w.dev.map f}=HolderEncrypt.fields w) :
    Preserves (Boundary cs loans) (modifyDev f) := by
  apply hoare_modify
  intro w hi
  exact HolderEncrypt.boundary_fields hi (same w)

private theorem fromWork (action : WG.M α)
    (keeps : ∀ original, Preserves (DuringWork original cs loans) action) :
    Preserves (Boundary cs loans) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b hi run
  obtain ⟨holders,funded,stable⟩ := hi
  obtain ⟨out,_,fundedOut,stableOut⟩ := (hoare_iff_run_ambient _ _ _).mp (keeps holders)
    w a x v b (duringWork_initial funded stable) run
  exact ⟨out,fundedOut,stableOut⟩

theorem timers (pid : PeerId) : Preserves (Boundary cs loans) (timersStop pid) :=
  fromWork _ (fun _ => timersStop_preserves pid)

theorem keys (pid : PeerId) : Preserves (Boundary cs loans) (keypairsClear pid) :=
  fromWork _ (fun _ => keypairsClear_preserves pid)

theorem handshake (pid : PeerId) : Preserves (Boundary cs loans) (handshakeClear pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.frame_boundary)
    _ (HolderWorkFrames.handshakeClear_frame pid) (fun _ _ => ClearWork.handshakeClear_preserves pid)

theorem reset (pid : PeerId) : Preserves (Boundary cs loans) (resetLastSentHandshake pid) := by
  unfold resetLastSentHandshake
  apply preserves_bind (hoare_liftAmbient (AmbientM.hiddenClock64 .resetLastSent) (Boundary cs loans))
  intro now
  exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderTimerCallbacks.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderTimers.modify_boundary)
    pid (fun p => {p with lastSentHandshake:=now-(REKEY_TIMEOUT+1 : Nat).toInt64*NSEC_PER_SEC64})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ _ h => h) (fun _ => rfl)

theorem socket (new4 new6 : Option Nat) : Preserves (Boundary cs loans) (socketReinit new4 new6) := by
  apply HolderEncrypt.native_boundary
  apply (socketReinit_sameSocket new4 new6).of_factor
    (fun s : WGOwnedView => HolderEncrypt.fields {dev:=s.dev,nlSock7:=s.nlSock7,nlSock8:=s.nlSock8})
  intro w
  unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
  unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
  simp only [socketView,socketDevice,wgOwnedView,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def]
  simp only [rxView,Option.map_map,Option.bind_map,Function.comp_def]
  rfl

/-- The complete actual stop path retains carriers and charged holders. Work
flushes may pay selected holders; no surviving-peer premise is required. -/
theorem stop : Preserves (Boundary cs loans) wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [requireNotPending,branch,unsupported]
  repeat' first
    | (rx_retention_head getDev; exact read)
    | (rx_retention_head purgeStagedPackets; exact HolderTimers.purge_boundary _)
    | (rx_retention_head timersStop; exact timers _)
    | (rx_retention_head handshakeClear; exact handshake _)
    | (rx_retention_head keypairsClear; exact keys _)
    | (rx_retention_head resetLastSentHandshake; exact reset _)
    | (rx_retention_head socketReinit; exact socket _ _)
    | (rx_retention_head modifyDev
       apply modify
       intro w
       unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
       unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
       cases hd : w.dev <;> simp [hd,rxView])
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Boundary cs loans)
       intro x u
       change Preserves (Boundary cs loans) _)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ (Boundary cs loans))
    | rx_retention_step

theorem down : Preserves (Boundary cs loans) wgDown := by
  unfold wgDown
  apply preserves_bind
  · apply modify
    intro w
    unfold HolderEncrypt.fields DecryptCarrier.decryptView carrierView keyView peerView rxView
    unfold keyWords currentCells stableView RxRing.nativeCell passiveView sendView handoffTxView
    cases hd : w.dev <;> simp [hd,rxView]
  · intro _; exact stop

end Leanux.Proofs.WG.Queues.RxCredits.HolderDeviceStop
