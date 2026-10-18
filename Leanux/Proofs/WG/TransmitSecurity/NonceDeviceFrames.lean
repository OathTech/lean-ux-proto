import Leanux.Proofs.WG.TransmitSecurity.NonceConfigurationFrames

/-! Native device lifecycle retains historical nonce reservations even when
all resident key objects disappear. Re-creation installs an empty key store. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

def nonceStore (s : WGStoreView) : View :=
  ⟨s.keypairCounter,fun id => (s.dev.bind fun d => d.keypairs[id]?).map cell⟩

theorem nonceStore_link (w : WGWorld) : nonceStore (linkView w) = view w := by
  apply View.ext
  · rfl
  · funext id
    simp [nonceStore,view,linkView,linkStore,linkDevice,wgStoreView,Option.bind_map,Function.comp_def]

theorem create_device (h : List Allocation) : Preserves (fun w => Inv (view w) h) wgCreate := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi hr
  have hc := (hoare_iff_run_ambient _ _ _).mp (wgCreate_endpoint (linkView w)) w a result v b rfl hr
  rcases hc with same | ⟨_,fresh⟩
  · have eq := congrArg nonceStore same
    rw [nonceStore_link,nonceStore_link] at eq
    simpa only [eq] using hi
  · have eq := congrArg nonceStore fresh
    rw [nonceStore_link] at eq
    apply hi.subset (t := view v)
    · have hf := congrArg View.frontier eq
      exact Nat.le_of_eq hf.symm
    · intro id c hc
      rw [eq] at hc
      simp [nonceStore,registeredLink,setupLink,linkDevice] at hc

theorem socket_frame {α : Type} {a : WG.M α} (frame : SameSocket a) : SameView view a := by
  apply frame.of_factor (fun s : WGOwnedView => nonceStore s.toWGStoreView) view
  intro w
  apply View.ext
  · rfl
  · funext id
    simp [nonceStore,view,socketView,socketDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def]

theorem socket_init (port : Nat) : SameView view (socketInit port) := socket_frame (socketInit_sameSocket port)
theorem socket_reinit (a b : Option Nat) : SameView view (socketReinit a b) := socket_frame (socketReinit_sameSocket a b)

theorem stopped_device (h : List Allocation) : Preserves (fun w => Inv (view w) h) wgStop := by
  unfold wgStop
  simp (config := {zeta := false}) only [branch,requireNotPending,unsupported]
  repeat' first
    | (rx_retention_head keypairsClear; exact clear _ h)
    | (rx_retention_head timersStop; exact timers_stop _ h)
    | (rx_retention_head handshakeClear; exact native_frame h (clear_handshake _))
    | (rx_retention_head resetLastSentHandshake
       exact native_frame h (full (Origins.Retaining.resetLastSentHandshake_material _)
         (Keypairs.WGFrames.resetLastSentHandshake_sameSnapshot _)))
    | (rx_retention_head socketReinit; exact native_frame h (socket_reinit _ _))
    | nonce_timer_step h

theorem down_device (h : List Allocation) : Preserves (fun w => Inv (view w) h) wgDown := by
  unfold wgDown
  exact preserves_bind (native_frame h (update _ (fun _ => rfl))) (fun _ => stopped_device h)

theorem erase_device (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (modify (fun w : WGWorld => {w with dev := none}) : WG.M Unit) := by
  apply hoare_modify
  intro w hi
  apply hi.subset (t := view {w with dev := none}) (Nat.le_refl _)
  intro id c hc
  cases hc

theorem ratelimiter_finish : SameView view ratelimiterUninit := by
  apply ratelimiterUninit_sameRatelimiter.of_factor nonceStore view
  intro w
  rfl

theorem destruct_device (h : List Allocation) : Preserves (fun w => Inv (view w) h) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [invariant,unsupported]
  repeat' first
    | (rx_retention_head socketReinit; exact native_frame h (socket_reinit _ _))
    | (rx_retention_head peerRemoveAll; exact remove_all h)
    | (rx_retention_head ratelimiterUninit; exact native_frame h ratelimiter_finish)
    | (rx_retention_head mayHaveSlept; exact native_frame h (store mayHaveSlept_sameWGStore))
    | (rx_retention_head retireDeviceUnits; exact native_frame h (store retireDeviceUnits_sameWGStore))
    | (rx_retention_head modify; exact erase_device h)
    | nonce_preserves_step h

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
