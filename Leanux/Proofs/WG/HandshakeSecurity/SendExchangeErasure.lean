import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeSource
import Leanux.Proofs.WG.AuthenticatedEffects.WorkRootFrames

/-! Native result and Stop erasure, separately from journal projection. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.SendExchange
open Leanux Leanux.WG Leanux.Proofs.Logged
set_option maxRecDepth 4096
set_option maxHeartbeats 600000

structure Ops.Erases (g : Ops (WGPrefix E)) : Prop where
  step : ∀ {α} (a : WG.M α), ErasesStatePrefix (g.step a) a
  create : ∀ pid, ErasesStatePrefix (g.create pid) (createInitiation pid)
  mac : ∀ pid msg, ErasesStatePrefix (g.mac pid msg) (addMacToPacket pid msg)
  traversal : ∀ pid, ErasesStatePrefix (g.traversal pid) (timersTraversal pid)
  sent : ∀ pid, ErasesStatePrefix (g.sent pid) (timersAnyAuthenticatedPacketSent pid)
  send : ∀ pid msg, ErasesStatePrefix (g.send pid msg) (sendBufferToPeer pid msg)
  initiated : ∀ pid, ErasesStatePrefix (g.initiated pid) (timersHandshakeInitiated pid)
  put : ∀ pid, ErasesStatePrefix (g.put pid) (peerPut pid)

macro "send_exchange_erase " h:ident : tactic => `(tactic| first
  | exact Ops.Erases.step $h _
  | exact Ops.Erases.create $h _
  | exact Ops.Erases.mac $h _ _
  | exact Ops.Erases.traversal $h _
  | exact Ops.Erases.sent $h _
  | exact Ops.Erases.send $h _ _
  | exact Ops.Erases.initiated $h _
  | exact Ops.Erases.put $h _
  | work_root_erasure_step)

theorem send_erases {g : Ops (WGPrefix E)} (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (sendWith g pid) (sendHandshakeInitiation pid) := by
  unfold sendWith sendHandshakeInitiation
  repeat' send_exchange_erase h
  all_goals simp_all only [Option.some.injEq]
  all_goals first | exact h.mac _ _ | exact False.elim (by solve_by_elim)

theorem worker_erases {g : Ops (WGPrefix E)} (h : Ops.Erases g) (pid : PeerId) :
    ErasesStatePrefix (workerWith g pid) (handshakeSendWorker pid) := by
  unfold workerWith handshakeSendWorker
  exact erasesStatePrefix_bind (send_erases h pid) (fun _ => h.put _)

variable (sg : {α : Type} → WG.M α → WGPrefix E α)
  (hs : ∀ {α} (a : WG.M α), ErasesStatePrefix (sg a) a)
  (wg : PeerId → WGPrefix E Unit)
  (hw : ∀ pid, ErasesStatePrefix (wg pid) (handshakeSendWorker pid))

include hs hw in
theorem afterTake_erases (pid : PeerId) :
    ErasesStatePrefix (afterTakeWith sg wg pid) (AuthenticatedEffects.SendWorkCauses.afterTake pid) := by
  rw [← afterTake_factor]
  unfold afterTakeWith
  repeat' first | exact hs _ | exact hw _ | work_root_erasure_step

include hs hw in
theorem flushed_erases (pid : PeerId) :
    ErasesStatePrefix (flushedWith sg wg pid) (runFlushedSendWork pid) := by
  rw [← flushed_factor]
  unfold flushedWith
  exact erasesStatePrefix_bind (hs _) (fun _ => afterTake_erases sg hs wg hw pid)

include hs in
theorem drain_erases
    (wg cg : PeerId → WGPrefix E Unit)
    (hw : ∀ pid, ErasesStatePrefix (wg pid) (runFlushedSendWork pid))
    (hc : ∀ pid, ErasesStatePrefix (cg pid) (runFlushedClearWork pid)) (upTo : Option PeerId) :
    ErasesStatePrefix (drainWith sg wg cg upTo) (drainHandshakeSendWq upTo) := by
  rw [← drain_factor]
  unfold drainWith
  rw [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first | exact hs _ | exact hw _ | exact hc _ | work_root_erasure_step

theorem one_erases
    (sg : {α : Type} → Leanux.M α → PrefixM E α)
    (hs : ∀ {α} (a : Leanux.M α), ErasesPrefix (sg a) a)
    (wg : PeerId → PrefixM E Unit)
    (hw : ∀ pid, ErasesPrefix (wg pid) (Leanux.liftWG (runFlushedSendWork pid))) :
    ErasesPrefix (oneWith sg wg) Env.runOneSendWorker := by
  rw [← one_factor]
  unfold oneWith
  exact erasesPrefix_bind (hs _) hw

end Leanux.Proofs.WG.HandshakeSecurity.SendExchange
