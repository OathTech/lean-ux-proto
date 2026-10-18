import Leanux.Proofs.WG.Noise.CookieReplyTagFrames
import Leanux.Proofs.WG.Noise.PendingTicketRetentionFrames
import Leanux.Proofs.WG.Keypairs.Frames.WGMore

/-! Pending allocation identities follow the owned socket peer observation and
campaign 1's allocation snapshot. The socket source proofs are shared with
the existing timer and tag projections. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Leanux.Proofs.Framing TimerDiscipline Std.Do

theorem next_of_sendWork (w v : WGWorld) (pid : PeerId)
    (same : sendWorkAt v pid = sendWorkAt w pid) :
    nextSlots v = nextSlots w := by
  funext target
  have projected := congrArg (fun x : SendWorkView =>
    x.1.bind fun d => (d.2.2 target).bind Prod.snd) same
  simpa [sendWorkAt,sendWorkKernel,sendWorkDevice,nextSlots,
    Option.bind_map,Option.bind_assoc,Function.comp_def] using projected

/-- Exact global next-slot preservation combines with unchanged resident key
stamps and allocation counter; no selected-peer residency premise is needed. -/
theorem frame_from_sendWork {α : Type} (action : WG.M α) (pid : PeerId)
    (frame : ∀ (q : Option SendWorkDevice) (v : Option SendWorkPeer),
      ⦃fun w => ⌜sendWorkAt w pid = (q, v)⌝⦄ action
        ⦃⇓? _ w => ⌜sendWorkAt w pid = (q, v)⌝⦄)
    (keys : Keypairs.SameSnapshot action) : SameView view action := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v after run
  have same := (ensures_iff _ _ _).mpr
    (frame (sendWorkAt w pid).1 (sendWorkAt w pid).2)
    w ambient x v after rfl run
  exact view_same w v (next_of_sendWork w v pid same)
    ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp keys w ambient x v after run)

theorem sendBufferToPeer_frame (pid : PeerId) (msg : List UInt8) :
    SameView view (sendBufferToPeer pid msg) :=
  frame_from_sendWork _ pid (sendBufferToPeer_spec_sendWork_variant pid msg)
    (Keypairs.WGTransitions.sendBufferToPeer_sameSnapshot pid msg)

theorem send4_uncached_frame (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    SameView view (send4 e none bytes ds exactRx) :=
  frame_from_sendWork _ 0 (uncached_sendWorkView 0 false e bytes ds exactRx)
    (Keypairs.WGFrames.send4_sameSnapshot e none bytes ds exactRx)

theorem send6_uncached_frame (e : Endpoint) (bytes : List UInt8)
    (ds : Nat) (exactRx : Bool) :
    SameView view (send6 e none bytes ds exactRx) :=
  frame_from_sendWork _ 0 (uncached_sendWorkView 0 true e bytes ds exactRx)
    (Keypairs.WGFrames.send6_sameSnapshot e none bytes ds exactRx)

theorem sendBufferAsReplyToSkb_frame (src : SkbSource) (msg : List UInt8) :
    SameView view (sendBufferAsReplyToSkb src msg) :=
  frame_from_sendWork _ 0 (sendBufferAsReplyToSkb_sendWorkView 0 src msg)
    (Keypairs.WGMore.sendBufferAsReplyToSkb_sameSnapshot src msg)

end Leanux.Proofs.WG.Noise.PendingTickets
