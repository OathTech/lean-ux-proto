import Leanux.Proofs.WG.Noise.PendingOuterFrames

/-! Three pending-history variants of the shared OwnerControlCalls wrapper
contracts. The original polymorphic source supplies the full descriptor and
allocation-cut behavior, including errno returns and failed prefixes. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingOuter
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Configuration PendingSession

theorem socketCallOn_pending_variant (fd : Nat) (body : RxHistory.Obs Int)
    (hb : PrefixPreserves StateInv HistorySafe body) :
    PrefixPreserves StateInv HistorySafe
      (socketCallOnWith (fun {_} a => liftPrefix a) fd body) := by
  unfold socketCallOnWith
  apply PrefixPreserves.bind (lift_fs (fdget fd))
  intro f
  apply PrefixPreserves.ite
  · intro _; exact PrefixPreserves.pure PendingScheduler.safe _
  · intro _
    exact hb.bind (fun ret => (lift_fs (fdput f)).bind
      (fun _ => PrefixPreserves.pure PendingScheduler.safe ret))

theorem netlinkRequest_pending_variant (body : RxHistory.Obs Int)
    (hb : PrefixPreserves StateInv HistorySafe body) :
    PrefixPreserves StateInv HistorySafe
      (netlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold netlinkRequestWith
  apply PrefixPreserves.bind
    (socketCallOn_pending_variant _ _ ((lift_ambient (AmbientM.skipCut allocCuts)).bind
      (fun _ => hb.bind (fun ret => (lift_ambient (AmbientM.skipCut allocCuts)).bind
        (fun _ => PrefixPreserves.pure PendingScheduler.safe ret)))))
  intro ret
  exact (socketCallOn_pending_variant _ _ (PrefixPreserves.pure PendingScheduler.safe 0)).bind
    (fun _ => PrefixPreserves.pure PendingScheduler.safe ret)

macro "pending_outer_step" : tactic => `(tactic| first
  | (current_env_at unsupported; exact lift_ambient (AmbientM.unsupported _))
  | (current_env_at skipCut; exact lift_ambient (AmbientM.skipCut _))
  | (current_env_at liftPrefix; first
      | exact lift_fs _
      | exact lift_task _
      | exact lift_ambient _
      | exact lift_seccomp _
      | exact lift_get
      | exact lift_modify _ (fun _ => rfl))
  | (current_env_at Pure.pure; exact PrefixPreserves.pure PendingScheduler.safe _)
  | (current_env_at Bind.bind; apply PrefixPreserves.bind)
  | (current_env_at ite; apply PrefixPreserves.ite)
  | (current_env_at dite; split)
  | (maintenance_intro; try dsimp only)
  | current_env_match)

theorem rtnetlinkRequest_pending_variant (body : RxHistory.Obs Int)
    (hb : PrefixPreserves StateInv HistorySafe body) :
    PrefixPreserves StateInv HistorySafe
      (rtnetlinkRequestWith (fun {_} a => liftPrefix a) body) := by
  unfold rtnetlinkRequestWith
  repeat' first
    | exact hb
    | (current_env_at socketCallOnWith; apply socketCallOn_pending_variant)
    | pending_outer_step

end Leanux.Proofs.WG.Noise.PendingOuter
