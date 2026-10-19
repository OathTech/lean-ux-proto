import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseSource
import Leanux.Proofs.WG.AuthenticatedEffects.TimerEffectsFrames

/-! Callback contracts for the original nested peer-release paths, including Stop prefixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

structure Ops.Frames (ρ : E → Option F) (g : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (a : WG.M α), StateHistoryFrame ρ (g.step a)
  release : ∀ peer, StateHistoryFrame ρ (g.release peer)

macro "nested_release_frame " h:ident rho:ident : tactic => `(tactic| first
  | with_reducible exact Ops.Frames.step $h _
  | with_reducible exact Ops.Frames.release $h _
  | timer_effects_frame_step $rho)

variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem initiationOut_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (peer ret : Option PeerId) :
    StateHistoryFrame ρ (initiationOutWith g peer ret) := by
  unfold initiationOutWith
  repeat' first
    | nested_release_frame h ρ

theorem initiationTail_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    StateHistoryFrame ρ (initiationTailWith g msg e ck hash peer pid) := by
  unfold initiationTailWith
  repeat' first
    | with_reducible exact initiationOut_frame ρ h _ _
    | nested_release_frame h ρ

theorem initiationCheck_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (msg : Key) :
    StateHistoryFrame ρ (initiationCheckWith g msg) := by
  unfold initiationCheckWith
  repeat' first
    | with_reducible exact initiationOut_frame ρ h _ _
    | with_reducible exact initiationTail_frame ρ h _ _ _ _ _ _
    | nested_release_frame h ρ

theorem responseTail_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (msg : Key) (identity : StaticIdentity) (pid : PeerId) :
    StateHistoryFrame ρ (responseTailWith g msg identity pid) := by
  unfold responseTailWith
  repeat' first
    | nested_release_frame h ρ

theorem responseCheck_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (msg : Key) :
    StateHistoryFrame ρ (responseCheckWith g msg) := by
  unfold responseCheckWith
  repeat' first
    | with_reducible exact responseTail_frame ρ h _ _ _
    | nested_release_frame h ρ

theorem cookieAfter_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) (cookie : Option Key) :
    StateHistoryFrame ρ (cookieAfterWith g pid cookie) := by
  unfold cookieAfterWith
  repeat' first
    | nested_release_frame h ρ

theorem cookie_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (msg : Key) :
    StateHistoryFrame ρ (cookieWith g msg) := by
  unfold cookieWith
  repeat' first
    | with_reducible exact cookieAfter_frame ρ h _ _
    | nested_release_frame h ρ

theorem clear_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (clearWith g pid) := by
  unfold clearWith
  repeat' first
    | nested_release_frame h ρ

theorem flushedClear_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) :
    StateHistoryFrame ρ (flushedClearWith g pid) := by
  unfold flushedClearWith
  repeat' first
    | with_reducible exact clear_frame ρ h _
    | nested_release_frame h ρ

theorem cleanup_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (id : SkbId) (pkt : RxPacket) (flag : Bool) :
    StateHistoryFrame ρ (cleanupWith g id pkt flag) := by
  unfold cleanupWith
  repeat' first
    | nested_release_frame h ρ

theorem lifted_frames (ρ : E → Option F) : Ops.Frames ρ lifted where
  step := by intro α action w a h; rfl
  release := by intro peer w a h; rfl

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
