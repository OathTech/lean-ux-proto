import Leanux.Proofs.WG.Index.TimerFrames
import Leanux.Proofs.WG.Index.ClearSource
import Leanux.Proofs.WG.TimerDiscipline.RetrySource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.CallbackRules
open Leanux Leanux.WG Noise Std.Do

structure Contracts (pid : PeerId) (P Q : WGWorld → Prop) : Prop where
  attempts : Ensures (modifyPeer pid (fun p => {p with timerHandshakeAttempts:=p.timerHandshakeAttempts+1})) P (fun _ => P)
  another : Ensures (modifyPeer pid (fun p => {p with timerNeedAnotherKeepalive:=false})) P (fun _ => P)
  endpoint : Ensures (clearPeerEndpointSrc pid) P (fun _ => P)
  purge : Ensures (purgeStagedPackets pid) P (fun _ => P)
  del : Ensures (delTimer pid .sendKeepalive) P (fun _ => P)
  arm : ∀ site timer delay, Ensures (modPeerTimer site pid timer delay) P (fun _ => P)
  queued : ∀ retry, Ensures (sendQueuedHandshakeInitiation pid retry) P (fun _ => P)
  keepalive : Ensures (sendKeepalive pid) P (fun _ => P)
  acquire : Ensures (peerGet pid) P (fun _ => Q)
  repay : Ensures (peerPut (some pid)) Q (fun _ => P)
  enqueue : Ensures (modifyDev fun d => {d with clearWorkQueue:=d.clearWorkQueue++[pid]}) Q (fun _ => P)

theorem pure_rule {α : Type} (value : α) (P : WGWorld → Prop) :
    Ensures (pure value : WG.M α) P (fun _ => P) := by
  intro w a result v b pre run
  cases run
  exact pre

theorem ambient_rule {α : Type} (action : AmbientM α) (P : WGWorld → Prop) :
    Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
  (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)

theorem read_rule (pid : PeerId) (P : WGWorld → Prop) :
    Ensures (getPeer pid) P (fun _ => P) := by
  intro w a result v b pre run
  exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P) w a result v b pre run).1

theorem device_rule (P : WGWorld → Prop) : Ensures getDev P (fun _ => P) := by
  intro w a result v b pre run
  cases device : w.dev with
  | none => simp [getDev,device,invariant,AmbientM.invariant] at run; cases run
  | some d =>
    simp [getDev,device] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact pre

theorem retransmit {pid : PeerId} {P Q : WGWorld → Prop} (c : Contracts pid P Q) :
    Ensures (expiredRetransmitHandshake pid) P (fun _ => P) := by
  have modify_source (f : Peer → Peer) : modifyPeer pid f = (do
      let p ← getPeer pid; setPeer pid (f p)) := rfl
  rw [TimerDiscipline.expiredRetransmit_source]
  refine ensures_bind _ _ (read_rule pid P) ?_
  intro p
  refine ensures_bind _ _ (ambient_rule (AmbientM.branchCmp .retransmitGiveUp
    (p.timerHandshakeAttempts > MAX_TIMER_HANDSHAKES) p.timerHandshakeAttempts MAX_TIMER_HANDSHAKES) P) ?_
  intro giveUp
  cases giveUp with
  | false =>
    have tail := ensures_bind _ _ c.attempts (fun _ =>
      ensures_bind _ _ c.endpoint (fun _ => c.queued true))
    simpa only [Bool.false_eq_true,ite_false,modify_source,bind_assoc] using tail
  | true =>
    unfold TimerDiscipline.retransmitGiveUp
    refine ensures_bind _ _ c.del ?_
    intro _
    refine ensures_bind _ _ c.purge ?_
    intro _
    refine ensures_bind _ _ (read_rule pid P) ?_
    intro p
    refine ensures_bind _ _ (ambient_rule
      (AmbientM.branch .retransmitZeroKeyNotPending (!p.timerPending .zeroKeyMaterial)) P) ?_
    intro pending
    cases pending with
    | false => exact pure_rule () P
    | true =>
      exact ensures_bind _ _
        (c.arm .timerJiffiesRetransmitZeroKey .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS)
        (fun _ => pure_rule () P)

theorem keepalive {pid : PeerId} {P Q : WGWorld → Prop} (c : Contracts pid P Q) :
    Ensures (expiredSendKeepalive pid) P (fun _ => P) := by
  have modify_source (f : Peer → Peer) : modifyPeer pid f = (do
      let p ← getPeer pid; setPeer pid (f p)) := rfl
  unfold expiredSendKeepalive
  refine ensures_bind _ _ c.keepalive ?_
  intro _
  refine ensures_bind _ _ (read_rule pid P) ?_
  intro p
  refine ensures_bind _ _ (ambient_rule (AmbientM.branch .keepaliveNeedAnother p.timerNeedAnotherKeepalive) P) ?_
  intro another
  cases another with
  | false => exact pure_rule () P
  | true =>
    have tail := ensures_bind _ _ c.another (fun _ =>
      ensures_bind _ _ (c.arm .timerJiffiesExpiredKeepalive .sendKeepalive KEEPALIVE_TIMEOUT_TICKS)
        (fun _ => pure_rule () P))
    simpa only [ite_true,modify_source,bind_assoc,discard,map_const,Function.comp_def,map_eq_pure_bind] using tail

theorem newHandshake {pid : PeerId} {P Q : WGWorld → Prop} (c : Contracts pid P Q) :
    Ensures (expiredNewHandshake pid) P (fun _ => P) := by
  unfold expiredNewHandshake
  exact ensures_bind _ _ c.endpoint (fun _ => c.queued false)

theorem zero {pid : PeerId} {P Q : WGWorld → Prop} (c : Contracts pid P Q) :
    Ensures (expiredZeroKeyMaterial pid) P (fun _ => P) := by
  unfold expiredZeroKeyMaterial
  refine ensures_bind _ _ (read_rule pid P) ?_
  intro p
  refine ensures_bind _ _ (ambient_rule (AmbientM.branch .zeroKeyAlive (!p.isDead)) P) ?_
  intro alive
  cases alive with
  | false => exact pure_rule () P
  | true =>
    refine ensures_bind _ _ c.acquire ?_
    intro _
    refine ensures_bind _ _ (device_rule Q) ?_
    intro d
    refine ensures_bind _ _ (ambient_rule (AmbientM.peekQueuedUnit .clearPeerWorker pid) Q) ?_
    intro peeked
    refine ensures_bind _ _ (ambient_rule
      (AmbientM.branch .zeroKeyAlreadyQueued (d.clearWorkQueue.contains pid && !peeked)) Q) ?_
    intro queued
    cases queued with
    | true => exact c.repay
    | false =>
      exact ensures_bind _ _ (ambient_rule (AmbientM.recordQueued .clearPeerWorker pid) Q)
        (fun _ => c.enqueue)

theorem persistent {pid : PeerId} {P Q : WGWorld → Prop} (c : Contracts pid P Q) :
    Ensures (expiredSendPersistentKeepalive pid) P (fun _ => P) := by
  unfold expiredSendPersistentKeepalive
  refine ensures_bind _ _ (read_rule pid P) ?_
  intro p
  refine ensures_bind _ _ (ambient_rule
    (AmbientM.branch .persistentKeepaliveInterval (p.persistentKeepaliveInterval != 0)) P) ?_
  intro enabled
  cases enabled
  · exact pure_rule () P
  · exact c.keepalive

theorem callback {pid : PeerId} {P Q : WGWorld → Prop} (c : Contracts pid P Q) (timer : PeerTimer) :
    Ensures (timerCallback pid timer) P (fun _ => P) := by
  cases timer
  · exact retransmit c
  · exact keepalive c
  · exact newHandshake c
  · exact zero c
  · exact persistent c

end Leanux.Proofs.WG.Index.CallbackRules
