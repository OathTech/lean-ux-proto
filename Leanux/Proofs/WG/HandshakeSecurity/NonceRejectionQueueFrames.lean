import Leanux.Proofs.WG.HandshakeSecurity.NonceRejectionCounterFrames
import Leanux.Proofs.WG.AuthenticatedEffects.ProtocolFrames

/-! The rejection arm's queue helper cannot count a drop: its failed enqueue
repays the reference obtained by the immediately preceding successful get. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open AuthenticatedEffects CounterWindow
set_option maxHeartbeats 800000
set_option pp.structureInstances false

private theorem get_safe (pid : PeerId) (initial : Option Nat) :
    Hoare (peerGet pid) (fun w => dropped w = initial)
      (fun _ w => dropped w = initial ∧ RepaySafe pid w) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases hd : w.dev with
  | none =>
    simp [peerGet,requireNotPending,getPeer,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [peerGet,requireNotPending,getPeer,getDev,hd,hp,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      by_cases zero : p.refcount = 0 <;> by_cases overflow : 2147483647 ≤ p.refcount <;>
        simp [StateT.run_bind,StateT.run_pure,StateT.run_monadLift,except_ok_bind,except_pure,
          peerGet,requireNotPending,getPeer,getDev,setPeer,modifyDev,hd,hp,refcountInc,
          branch,branchCmp,AmbientM.branch,AmbientM.branchCmp,unsupported,AmbientM.unsupported,
          zero,overflow] at run
      all_goals try (change Except.error _ = Except.ok _ at run; cases run)
      all_goals rcases run with ⟨rfl,rfl⟩
      all_goals refine ⟨?_,{d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}},
        {p with refcount := p.refcount + 1},rfl,?_,?_⟩
      all_goals simp only [dropped,hd,Option.map_some] at hi ⊢
      all_goals first | exact hi | exact Std.TreeMap.getElem?_insert_self | (change 1 < p.refcount + 1; omega)

private theorem put_safe (pid : PeerId) (initial : Option Nat) :
    Hoare (peerPut (some pid)) (fun w => dropped w = initial ∧ RepaySafe pid w)
      (fun _ w => dropped w = initial) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  obtain ⟨d,p,hd,hp,count⟩ := hi.2
  have positive : 0 < p.refcount := by omega
  have zero : p.refcount ≠ 0 := by omega
  have final : p.refcount ≠ 1 := by omega
  simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,refcountDecAndTest,
    branch,branchCmp,branch_run,branchCmp_run,hd,hp,positive,zero,final,
    StateT.run_bind,StateT.run_pure,StateT.run_monadLift,except_ok_bind,except_pure] at run
  obtain ⟨rfl,_⟩ := run
  simpa only [dropped,hd,Option.map_some] using hi.1

private def afterGet (pid : PeerId) (p : Peer) : WG.M Unit := do
  if ← branch .queuedAlreadyQueued (p.handshakePending && !(← peekQueuedUnit .sendWorker pid)) then
    peerPut (some pid)
    return
  setPeer pid {(← getPeer pid) with handshakePending := true}
  recordQueued .sendWorker pid
  modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}

private theorem after_get_safe (pid : PeerId) (p : Peer) (initial : Option Nat) :
    Hoare (afterGet pid p) (fun w => dropped w = initial ∧ RepaySafe pid w)
      (fun _ w => dropped w = initial) := by
  unfold afterGet
  simp only [peekQueuedUnit,branch]
  apply hoare_bind _ _ (hoare_liftAmbient _ _)
  intro queued
  apply hoare_bind _ _ (hoare_liftAmbient _ _)
  intro checked
  split
  · apply hoare_bind _ _ (put_safe pid initial)
    intro _
    exact preserves_pure ()
  · apply hoare_consequence ?_ (fun _ hi => hi.1) (fun _ _ hi => hi)
    change Preserves (fun w => dropped w = initial) _
    simp only [recordQueued]
    repeat' rejection_drop_step initial

private theorem acquire_then (pid : PeerId) (p : Peer) (initial : Option Nat) :
    Preserves (fun w => dropped w = initial) (do peerGet pid; afterGet pid p) :=
  hoare_bind _ _ (get_safe pid initial) (fun _ => after_get_safe pid p initial)

theorem queued_dropped (pid : PeerId) : SameView dropped (sendQueuedHandshakeInitiation pid false) := by
  intro initial
  change Preserves (fun w => dropped w = initial) _
  have factor : sendQueuedHandshakeInitiation pid false = (do
      if ← branch .queuedNotRetry true then
        setPeer pid {(← getPeer pid) with timerHandshakeAttempts := 0}
      let p ← getPeer pid
      if ← branchExpired .queuedNotExpired p.lastSentHandshake REKEY_TIMEOUT (!·) then return
      if ← branch .queuedDead p.isDead then return
      peerGet pid
      afterGet pid p) := rfl
  rw [factor]
  repeat' first
    | (unfold Preserves; rx_stack_bind_head peerGet; exact acquire_then pid _ initial)
    | rejection_drop_step initial

theorem rejected_dropped (pid : PeerId) (packets : List Packet) (kid : KeypairId) :
    SameView dropped (stagedOutNokey pid packets (some kid) true) := by
  intro initial
  change Preserves (fun w => dropped w = initial) _
  rw [factor]
  unfold invalidate release restore
  repeat' first
    | (rx_retention_head keypairPut; exact (key_put_dropped _).wp (· = initial))
    | (rx_retention_head sendQueuedHandshakeInitiation; exact (queued_dropped _).wp (· = initial))
    | rejection_drop_step initial

end Leanux.Proofs.WG.HandshakeSecurity.NonceRejection
