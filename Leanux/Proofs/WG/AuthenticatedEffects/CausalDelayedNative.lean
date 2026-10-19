import Leanux.Proofs.WG.AuthenticatedEffects.CausalDelayedEffects

/-! Native endpoint contracts extracted from the same delayed carrier. These
are used only to frame an already observed native callback; its observations
remain the actual callback's appended prefix. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do
open TimerSlots Queues.WorkQueueFrames
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem native_contract (action : WG.M α) (safe : StateSafe (liftWGPrefix action)) (h : List Event) :
    Preserves (Inv h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b hi run
  obtain ⟨_,_,_,output⟩ := safe w a h hi
  have lifted : runPrefix ((liftWGPrefix action : WGPrefix Event α).run w) a h =
      (.ok ((value,v),b),h) :=
    (runWGPrefix_lift action w a h).trans (congrArg (fun result => (result,h)) run)
  rw [lifted] at output
  exact output

theorem observed_native (body : WGPrefix Event α) (native : WG.M α)
    (erases : ErasesStatePrefix body native) (appends : StateAppends body)
    (safe : StateSafe (liftWGPrefix native)) : StateSafe body :=
  state_observed body native erases appends (native_contract native safe)

theorem capture_native (native : WG.M α) (safe : StateSafe (liftWGPrefix native)) :
    StateSafe (captureWGRun native) := safe.captureWGObserved

theorem native_peer_update (pid : PeerId) (f : Peer → Peer)
    (timers : ∀ p timer, ((f p).internalId,(f p).timer timer,(f p).wheel timer) =
      (p.internalId,p.timer timer,p.wheel timer)) :
    StateSafe (liftWGPrefix (do setPeer pid (f (← getPeer pid)))) := by
  apply state_framed
  · intro initial
    apply retained_read initial pid
    intro p known
    apply retained_write initial pid
    intro timer
    rw [timers]
    exact known timer
  · exact (SendWorkCauses.peer_read_frame pid).bind (fun p => SendWorkCauses.peer_write_frame pid (f p))

theorem handshake_complete (pid : PeerId) (site : HiddenSite) :
    StateSafe (liftWGPrefix (timersHandshakeComplete pid site)) := by
  apply state_native
  intro h
  have factor : timersHandshakeComplete pid site = (do
      delTimer pid .retransmitHandshake
      (do setPeer pid { (← getPeer pid) with timerHandshakeAttempts := 0, sentLastminuteHandshake := false })
      let now ← hidden site
      (do setPeer pid { (← getPeer pid) with walltimeLastHandshake := now })) := by
    simp only [timersHandshakeComplete,bind_assoc]
  rw [factor]
  apply preserves_bind (native_contract _ (delete pid .retransmitHandshake) h)
  intro _
  apply preserves_bind (native_contract _ (native_peer_update pid
    (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false}) (by intro p timer; rfl)) h)
  intro _
  apply preserves_bind (native_contract _ (by unfold hidden; causal_delayed_native) h)
  intro _
  exact native_contract _ (native_peer_update pid _ (by intro p timer; rfl)) h

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Delayed
