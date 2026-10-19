import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseSource
import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootFrames

/-! Callback contracts for the original nested peer-release paths, including Stop prefixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

structure Ops.Erases (g : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (a : WG.M α), ErasesStatePrefix (g.step a) (native.step a)
  release : ∀ peer, ErasesStatePrefix (g.release peer) (native.release peer)

macro "nested_release_erase " h:ident : tactic => `(tactic| first
  | with_reducible exact Ops.Erases.step $h _
  | with_reducible exact Ops.Erases.release $h _
  | work_root_erasure_step)

variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem initiationOut_erases (h : Ops.Erases g) (peer ret : Option PeerId) :
    ErasesStatePrefix (initiationOutWith g peer ret) (initiationOutWith native peer ret) := by
  unfold initiationOutWith
  repeat' first
    | nested_release_erase h

theorem initiationTail_erases (h : Ops.Erases g) (msg e ck hash : Key) (peer : Option PeerId) (pid : PeerId) :
    ErasesStatePrefix (initiationTailWith g msg e ck hash peer pid) (initiationTailWith native msg e ck hash peer pid) := by
  unfold initiationTailWith
  repeat' first
    | with_reducible exact initiationOut_erases h _ _
    | nested_release_erase h

theorem initiationCheck_erases (h : Ops.Erases g) (msg : Key) :
    ErasesStatePrefix (initiationCheckWith g msg) (initiationCheckWith native msg) := by
  unfold initiationCheckWith
  repeat' first
    | with_reducible exact initiationOut_erases h _ _
    | with_reducible exact initiationTail_erases h _ _ _ _ _ _
    | nested_release_erase h

theorem responseTail_erases (h : Ops.Erases g) (msg : Key) (identity : StaticIdentity) (pid : PeerId) :
    ErasesStatePrefix (responseTailWith g msg identity pid) (responseTailWith native msg identity pid) := by
  unfold responseTailWith
  repeat' first
    | nested_release_erase h

theorem responseCheck_erases (h : Ops.Erases g) (msg : Key) :
    ErasesStatePrefix (responseCheckWith g msg) (responseCheckWith native msg) := by
  unfold responseCheckWith
  repeat' first
    | with_reducible exact responseTail_erases h _ _ _
    | nested_release_erase h

theorem cookieAfter_erases (h : Ops.Erases g) (pid : PeerId) (cookie : Option Key) :
    ErasesStatePrefix (cookieAfterWith g pid cookie) (cookieAfterWith native pid cookie) := by
  unfold cookieAfterWith
  repeat' first
    | nested_release_erase h

theorem cookie_erases (h : Ops.Erases g) (msg : Key) :
    ErasesStatePrefix (cookieWith g msg) (cookieWith native msg) := by
  unfold cookieWith
  repeat' first
    | with_reducible exact cookieAfter_erases h _ _
    | nested_release_erase h

theorem clear_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (clearWith g pid) (clearWith native pid) := by
  unfold clearWith
  repeat' first
    | nested_release_erase h

theorem flushedClear_erases (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (flushedClearWith g pid) (flushedClearWith native pid) := by
  unfold flushedClearWith
  repeat' first
    | with_reducible exact clear_erases h _
    | nested_release_erase h

theorem cleanup_erases (h : Ops.Erases g) (id : SkbId) (pkt : RxPacket) (flag : Bool) :
    ErasesStatePrefix (cleanupWith g id pkt flag) (cleanupWith native id pkt flag) := by
  unfold cleanupWith
  repeat' first
    | nested_release_erase h

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
