import Leanux.Proofs.WG.Noise.PendingTicketHandshakeFrames
import Leanux.Proofs.WG.Noise.PendingTicketTimerFrames
import Leanux.Proofs.WG.TimerDiscipline.InitiationTraversalSource

/-! Normal-return pending-ticket frames for the original initiation sender and
its worker. H6's exact arm effects cover both record modes; the worker's final
release may remove peers or keypairs and is therefore retention, not equality. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing TimerDiscipline

theorem wheelPlacementState_pending (entry : WGWorld) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (expires clk : UInt64) (ambient : Ambient)
    (resident : peerAt entry pid = some p) :
    view (wheelPlacementState entry pid p timer expires clk) = view entry := by
  cases device : entry.dev with
  | none => simp [peerAt,device] at resident
  | some d =>
    have found : d.peers[pid]? = some p := by simpa [peerAt,device] using resident
    have projection :
        stateView (wheelPlacementView (Campaign2.snapshot entry ambient).wg pid p timer expires clk) =
        view (wheelPlacementState entry pid p timer expires clk) := by
      cases placed : TimerWheel.place p timer expires clk <;>
        simp only [wheelPlacementState,wheelPlacementView,placed] <;> rfl
    rw [← projection]
    exact wheelPlacementView_pending _ d pid p timer expires clk device found

theorem armTimer_pending_of_resident (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) (g : WGWorld) (ambient : Ambient)
    (final : WGWorld) (after : Ambient) (p : Peer)
    (resident : peerAt g pid = some p)
    (run : ((armTimer pid timer delay caller).run g).run ambient = .ok (((),final),after)) :
    view final = view g := by
  cases mode : ambient.armRecords with
  | false =>
    rw [armTimer_off_effect pid timer delay caller g p resident ambient after final mode run]
    exact wheelPlacementState_pending g pid p timer _ _ ambient resident
  | true =>
    cases caller with
    | none =>
      have ambientRead : ((getAmbient : WG.M Ambient).run g).run ambient = .ok ((ambient,g),ambient) := rfl
      have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient =
          ((AmbientM.hidden .modTimerArm).run ambient >>= fun (bytes,next) => .ok ((bytes,g),next)) := rfl
      simp only [armTimer,StateT.run_bind,StateT.run_get,pure_bind] at run
      rw [ambientRead] at run
      simp only [bind,Except.bind,mode,Bool.not_true,Bool.false_eq_true,ite_false] at run
      change (((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient >>= _) = _ at run
      rw [hiddenRead] at run
      cases read : (AmbientM.hidden .modTimerArm).run ambient with
      | error stop => rw [read] at run; cases run
      | ok out => rw [read] at run; cases out; cases run
    | some caller =>
      by_cases same : p.timer timer = some (caller + delay.toUInt64)
      · obtain ⟨now,unit,_,_,effect⟩ := armTimer_sameExpiry_effect
          pid timer delay caller g p resident same ambient after final mode run
        rw [effect]
        rfl
      · obtain ⟨now,unit,clk,_,_,effect⟩ := armTimer_changedExpiry_effect
          pid timer delay caller g p resident same ambient after final mode run
        rw [effect]
        exact wheelPlacementState_pending _ pid p timer _ _ ambient resident

theorem guardedArm_pending_frame (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (caller : Option UInt64) :
    SameView view (do if ← modPeerTimerGuard pid then armTimer pid timer delay caller) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  change (((modPeerTimerGuard pid).run g).run ambient >>= fun ((allowed,current),inputs) =>
    ((if allowed then armTimer pid timer delay caller else pure () : WG.M Unit).run current).run inputs) = _ at run
  cases device : g.dev with
  | none =>
    simp [modPeerTimerGuard,WG.andM,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases found : d.peers[pid]? with
    | none =>
      simp [modPeerTimerGuard,WG.andM,getDev,getPeer,device,found,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      cases checked : ((modPeerTimerGuard pid).run g).run ambient with
      | error stop => rw [checked] at run; cases run
      | ok out =>
        obtain ⟨⟨allowed,current⟩,inputs⟩ := out
        have effect := modPeerTimerGuard_input_effect pid d p found
          g current ambient inputs allowed device checked
        have same := effect.2.1
        subst current
        rw [checked] at run
        cases allowed with
        | false => cases run; rfl
        | true =>
          cases result
          exact armTimer_pending_of_resident pid timer delay caller g inputs final after p
            (by simp [peerAt,device,found]) run

theorem timersHandshakeInitiated_frame (pid : PeerId) :
    SameView view (timersHandshakeInitiated pid) := by
  rw [handshakeInitiated_source]
  unfold jitteredArm
  exact ((callerJiffies_sameWGWorld _).factor view).bind (fun caller =>
    ((jitterBelowRekeyTimeout_sameWGWorld _).factor view).bind (fun jitter =>
      guardedArm_pending_frame pid .retransmitHandshake (REKEY_TIMEOUT_TICKS+jitter) caller))

theorem initiationTraversalPrelude_frame (pid : PeerId) :
    SameView view (initiationTraversalPrelude pid) := by
  have modify_eq (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have source : initiationTraversalPrelude pid = (do
      let p ← getPeer pid
      if ← branchExpired .initRateLimited p.lastSentHandshake REKEY_TIMEOUT (!·) then return none
      let now ← hiddenClock64 .initLastSent
      modifyPeer pid fun p => {p with lastSentHandshake := now}
      let created ← createInitiation pid
      if ← branch .initCreated created.isSome then
        let some msg := created | invariant "unreachable"
        return some (← addMacToPacket pid msg)
      return none) := by
    simp only [initiationTraversalPrelude,modify_eq,bind_assoc] <;> rfl
  rw [source]
  have peerRead : SameView view (getPeer pid) := by
    intro initial
    exact hoare_consequence (getPeer_spec pid (fun w => view w = initial))
      (fun _ h => h) (fun _ _ h => h.1)
  apply peerRead.bind
  intro p
  apply ((branchExpired_sameWGWorld _ _ _ (!·)).factor view).bind
  intro limited
  cases limited with
  | true => exact SameView.pure view none
  | false =>
    apply (frame_ambient (AmbientM.hiddenClock64 .initLastSent)).bind
    intro now
    apply (modifyPeer_spec_pending_variant pid (fun p => {p with lastSentHandshake := now}) (fun _ => rfl)).bind
    intro u
    apply (createInitiation_frame pid).bind
    intro created
    apply (frame_ambient (AmbientM.branch .initCreated created.isSome)).bind
    intro made
    cases made with
    | false => exact SameView.pure view none
    | true =>
      cases created with
      | none => exact (frame_ambient (AmbientM.invariant "unreachable")).bind (fun _ => SameView.pure view none)
      | some msg =>
        exact (addMacToPacket_frame pid msg).bind (fun authenticated => SameView.pure view (some authenticated))

theorem initiationTraversalFinish_frame (pid : PeerId) (message : List UInt8) :
    SameView view (initiationTraversalFinish pid message) := by
  have modify_eq (f : Peer → Peer) : modifyPeer pid f =
      (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have source : initiationTraversalFinish pid message = (do
      timersAnyAuthenticatedPacketSent pid
      let now ← hiddenClock64 .initLastSentAgain
      modifyPeer pid fun p => {p with lastSentHandshake := now}
      sendBufferToPeer pid message
      timersHandshakeInitiated pid) := by
    simp only [initiationTraversalFinish,modify_eq,bind_assoc]
  rw [source]
  exact (timersAnyAuthenticatedPacketSent_frame pid).bind (fun _ =>
    (frame_ambient (AmbientM.hiddenClock64 .initLastSentAgain)).bind (fun now =>
    (modifyPeer_spec_pending_variant pid (fun p => {p with lastSentHandshake := now}) (fun _ => rfl)).bind (fun _ =>
    (sendBufferToPeer_frame pid message).bind (fun _ =>
      timersHandshakeInitiated_frame pid))))

theorem initiationTraversalSuffix_frame (pid : PeerId) (message : Option (List UInt8)) :
    SameView view (initiationTraversalSuffix pid message) := by
  cases message with
  | none => exact SameView.pure view ()
  | some message => exact (timersTraversal_frame pid).bind (fun _ => initiationTraversalFinish_frame pid message)

/-- Exact global pending-slot allocation identities and frontier on every
normal return, including rate limiting and failed initiation creation. -/
theorem sendHandshakeInitiation_frame (pid : PeerId) :
    SameView view (sendHandshakeInitiation pid) := by
  rw [← initiationTraversal_source]
  exact (initiationTraversalPrelude_frame pid).bind (initiationTraversalSuffix_frame pid)

/-- The original final peer release can delete residents; every surviving
pending ticket retains its entry allocation identity and the frontier is fixed. -/
theorem handshakeSendWorker_retained (pid : PeerId) : RetainsCall (handshakeSendWorker pid) := by
  unfold handshakeSendWorker
  exact retains_bind (retained_of_frame (sendHandshakeInitiation_frame pid))
    (fun _ => peerPut_retained (some pid))

end Leanux.Proofs.WG.Noise.PendingTickets
