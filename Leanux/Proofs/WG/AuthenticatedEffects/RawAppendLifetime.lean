import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendFocus
import Leanux.Proofs.WG.AuthenticatedEffects.CompletionEffectsObservedProjection

/-! Timer and work receipts inside TX completion do not become socket appends.
The projection keeps their exact native actions and independently removes only
their own lifetime/effect events. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

private theorem lift_bind (body : WG.M α) (next : α → WG.M β) :
    (liftWGPrefix (body >>= next) : WGPrefix E β) =
      (liftWGPrefix body >>= fun x => liftWGPrefix (next x)) := by
  funext w a history
  change runWGPrefix (liftWGPrefix (body >>= next)) w a history =
    runWGPrefix (liftWGPrefix body >>= fun x => liftWGPrefix (next x)) w a history
  rw [liftWG_bind_run]
  change (((body >>= next).run w).run a,history) = _
  rw [native_bind_run]
  cases (body.run w).run a <;> rfl

private theorem lift_quiet (body : WG.M α) : StateHistoryFrame some (liftWGPrefix body : WGPrefix E α) :=
  fun _ _ _ => rfl
private theorem pure_quiet (value : α) : StateHistoryFrame some (pure value : WGPrefix E α) :=
  fun _ _ _ => rfl

def lifetimeLifted : LifetimeEffects.Ops (WGPrefix E) where
  step := liftWGPrefix
  peer := fun pid => liftWGPrefix (getPeer pid)
  keypair := fun kid => liftWGPrefix (getKeypair kid)
  modifyPeer := fun pid f => liftWGPrefix (do setPeer pid (f (← getPeer pid)))
  guard := fun pid => liftWGPrefix (modPeerTimerGuard pid)
  arm := fun pid timer delay caller => liftWGPrefix (armTimer pid timer delay caller)
  get := fun pid => liftWGPrefix (peerGet pid)
  put := fun pid => liftWGPrefix (peerPut pid)
  append := fun pid => liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})

theorem lifetime_traversal (pid : PeerId) :
    LifetimeEffects.traversalWith (lifetimeLifted : LifetimeEffects.Ops (WGPrefix E)) pid =
      liftWGPrefix (timersTraversal pid) := TimerEffects.traversal_lifted pid

theorem lifetime_dataSent (pid : PeerId) :
    LifetimeEffects.dataSentWith (lifetimeLifted : LifetimeEffects.Ops (WGPrefix E)) pid =
      liftWGPrefix (timersDataSent pid) := TimerEffects.dataSent_lifted pid

private theorem lifetime_queue (pid : PeerId) (retry : Bool) :
    LifetimeEffects.queuedWith (lifetimeLifted : LifetimeEffects.Ops (WGPrefix E)) pid retry =
      liftWGPrefix (sendQueuedHandshakeInitiation pid retry) := by
  apply TimerEffects.eq_native_lift
  · unfold LifetimeEffects.queuedWith sendQueuedHandshakeInitiation
    simp only [lifetimeLifted,lift_bind]
    repeat' first
      | exact erasesStatePrefix_lift _
      | work_root_erasure_step
  · unfold LifetimeEffects.queuedWith
    simp only [lifetimeLifted]
    repeat' first
      | exact lift_quiet _
      | exact pure_quiet _
      | apply StateHistoryFrame.bind
      | (maintenance_intro; try dsimp only)
      | maintenance_reduce
      | split

private theorem lifetime_queue_erases (pid : PeerId) (retry : Bool) :
    ErasesStatePrefix (LifetimeEffects.queuedWith (lifetimeLifted : LifetimeEffects.Ops (WGPrefix E)) pid retry)
      (sendQueuedHandshakeInitiation pid retry) := by
  rw [lifetime_queue]
  exact erasesStatePrefix_lift _

private theorem lifetime_queue_quiet (pid : PeerId) (retry : Bool) :
    StateHistoryFrame some (LifetimeEffects.queuedWith (lifetimeLifted : LifetimeEffects.Ops (WGPrefix E)) pid retry) := by
  rw [lifetime_queue]
  exact lift_quiet _

theorem lifetime_fresh (pid : PeerId) :
    LifetimeEffects.freshWith (lifetimeLifted : LifetimeEffects.Ops (WGPrefix E)) pid =
      liftWGPrefix (keepKeyFresh pid) := by
  apply TimerEffects.eq_native_lift
  · unfold LifetimeEffects.freshWith keepKeyFresh
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro p
    apply erasesStatePrefix_bind
    · apply andPrefix_erases_state (erasesStatePrefix_lift _)
      cases he : p.keypairCurrent with
      | none => exact erasesStatePrefix_lift _
      | some id =>
        apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
        intro k
        exact andPrefix_erases_state (erasesStatePrefix_lift _)
          (orPrefix_erases_state (erasesStatePrefix_lift _)
            (andPrefix_erases_state (erasesStatePrefix_lift _) (erasesStatePrefix_lift _)))
    · intro send
      apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
      intro yes
      split
      · exact lifetime_queue_erases pid false
      · exact erasesStatePrefix_pure _
  · unfold LifetimeEffects.freshWith
    simp only [lifetimeLifted,andPrefix,orPrefix]
    repeat' first
      | with_reducible exact lifetime_queue_quiet _ _
      | exact lift_quiet _
      | exact pure_quiet _
      | apply StateHistoryFrame.bind
      | (maintenance_intro; try dsimp only)
      | maintenance_reduce
      | split

theorem lifetime_base_projects (rho : E → Option F)
    (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (quiet : ∀ event, rho (encode (CompletionEffects.lifetimeEvent event)) = none) :
    LifetimeEffects.Ops.Projects rho (CompletionEffects.lifetimeBase encode decode) lifetimeLifted := by
  have project {α} (body : MixedM α) (native : WG.M α) (erases : ErasesStatePrefix body native) :
      StateProjectsPrefix rho id
        (focusStatePrefix (encode ∘ CompletionEffects.lifetimeEvent)
          (fun e => (decode e).bind CompletionEffects.lifetime?) body) (liftWGPrefix native) := by
    intro w
    exact projectsPrefix_focus_other _ _ rho quiet (erases w)
  constructor
  · intro α action; exact project _ _ (erasesStatePrefix_lift _)
  · intro pid; exact project _ _ (getPeerMixed_erases _)
  · intro kid; exact project _ _ (getKeypairPrefix_erases _)
  · intro pid f; exact project _ _ (modifyPeerKeysPrefix_erases _ _)
  · intro pid; exact project _ _ (modPeerTimerGuardPrefix_erases _)
  · intro pid timer delay caller; exact project _ _ (armTimerPrefix_erases _ _ _ _)
  · intro pid; exact project _ _ (peerGetMixed_erases _)
  · intro pid; exact project _ _ (peerPutMixed_erases _)
  · intro pid; exact project _ _ (erasesStatePrefix_lift _)

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
