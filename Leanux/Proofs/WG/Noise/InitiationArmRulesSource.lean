import Leanux.Proofs.WG.Noise.InitiationCallerClaims
import Leanux.Proofs.WG.Noise.ResponseSuffixTagFrames
import Leanux.Proofs.WG.Noise.TagCoverageModel
import Leanux.Proofs.WG.Index.StagedSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.InitiationCaller
open Leanux Leanux.WG TimerDiscipline

theorem armTimer_deviceView_of_resident {σ : Type} (view : Option Device → σ) (pid : PeerId) (timer : PeerTimer)
    (wheel : ∀ (g : WGWorld) (p : Peer) (expires clk : UInt64),
      peerAt g pid = some p →
      view (wheelPlacementState g pid p timer expires clk).dev = view g.dev)
    (delay : Nat) (caller : Option UInt64) (g : WGWorld) (ambient : Ambient)
    (final : WGWorld) (after : Ambient) (p : Peer)
    (resident : peerAt g pid = some p)
    (run : ((armTimer pid timer delay caller).run g).run ambient = .ok (((),final),after)) :
    view final.dev = view g.dev := by
  cases mode : ambient.armRecords with
  | false =>
    rw [armTimer_off_effect pid timer delay caller g p resident ambient after final mode run]
    exact wheel g p _ _ resident
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
        exact wheel _ p _ _ resident

/-- The actual guard supplies residency and excludes malformed missing-peer
states before an arm. Its supplied device projection covers all three exact arming effects. -/
theorem guardedArm_deviceView {σ : Type} (view : Option Device → σ) (pid : PeerId) (timer : PeerTimer)
    (wheel : ∀ (g : WGWorld) (p : Peer) (expires clk : UInt64),
      peerAt g pid = some p →
      view (wheelPlacementState g pid p timer expires clk).dev = view g.dev)
    (delay : Nat) (caller : Option UInt64) (entry : Option Device) :
    Ensures (do if ← modPeerTimerGuard pid then armTimer pid timer delay caller)
      (fun g => view g.dev = view entry)
      (fun _ g => view g.dev = view entry) := by
  intro g ambient result final after pre run
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
        | false => cases run; exact pre
        | true =>
          cases result
          exact (armTimer_deviceView_of_resident view pid timer wheel delay caller g inputs final after p
            (by simp [peerAt,device,found]) run).trans pre

end Leanux.Proofs.WG.Noise.InitiationCaller
