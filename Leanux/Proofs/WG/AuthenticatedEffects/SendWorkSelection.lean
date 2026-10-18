import Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCarrier
import Leanux.Proofs.WG.Queues.SendEnvironment

/-! The native recorded-unit/head selector supplies the actual dispatch peer
before its worker runs. Its receipt survives a Stop anywhere in that worker. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def select : Leanux.M PeerId := do
  let d ← Leanux.liftWG getDev
  let some headPid := d.sendWorkQueue.head? | invariant "no queued handshake send work"
  match ← peekUnit .sendWorker with
    | some u => resolveUnit .sendWorker u d.sendWorkQueue
    | none => pure headPid

def dispatch : PrefixM (RunWitness PeerId) Unit := do
  let r ← captureRun select
  emitPrefix r
  liftPrefix (Leanux.liftWG (runFlushedSendWork r.value))

theorem select_factor : Env.runOneSendWorker =
    (do let pid ← select; Leanux.liftWG (runFlushedSendWork pid)) := by
  rw [Queues.RxCredits.SendEnvironment.runOneSendWorker_factor]
  simp only [select,bind_assoc]
  congr 1
  funext d
  cases d.sendWorkQueue.head? <;> simp only [pure_bind]
  · rfl
  · simp only [bind_assoc]
    congr 1
    funext unit
    cases unit <;> simp only [pure_bind]

theorem select_member (w v : World) (pid : PeerId)
    (run : select.run w = .ok (pid,v)) : v.wg = w.wg ∧ pid ∈ queue w.wg := by
  unfold select at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨d,read,hread,tail⟩ := run
  cases hd : w.wg.dev with
  | none =>
    simp [liftWG_run,getDev,hd,invariant,AmbientM.invariant] at hread
    change Except.error _ = Except.ok _ at hread
    cases hread
  | some device =>
    have getter : (Leanux.liftWG getDev).run w = .ok (device,w) := by
      simp [liftWG_run,getDev,hd]
      rfl
    rw [getter] at hread
    simp only [Except.ok.injEq,Prod.mk.injEq] at hread
    obtain ⟨rfl,rfl⟩ := hread
    cases hh : device.sendWorkQueue.head? with
    | none =>
      simp only [hh] at tail
      change Except.error _ = Except.ok _ at tail
      cases tail
    | some headPid =>
      simp only [hh] at tail
      rw [MaterialOrigin.bind_ok] at tail
      obtain ⟨unit,peeked,hpeek,worker⟩ := tail
      change (liftAmbient (AmbientM.peekUnit .sendWorker)).run w = .ok (unit,peeked) at hpeek
      rw [liftAmbient_run] at hpeek
      cases hp : (AmbientM.peekUnit .sendWorker).run w.ambient with
      | error e => simp [hp,Except.map] at hpeek
      | ok out =>
        rcases out with ⟨chosen,afterPeek⟩
        simp only [hp,Except.map,Except.ok.injEq,Prod.mk.injEq] at hpeek
        obtain ⟨rfl,rfl⟩ := hpeek
        cases chosen with
        | none =>
          change Except.ok (headPid,{w with ambient := afterPeek}) = .ok (pid,v) at worker
          cases worker
          exact ⟨rfl,by simpa [queue,hd] using List.mem_of_head? hh⟩
        | some u =>
          change (liftAmbient (AmbientM.resolveUnit .sendWorker u device.sendWorkQueue)).run
            {w with ambient := afterPeek} = .ok (pid,v) at worker
          rw [liftAmbient_run] at worker
          cases hpick : (AmbientM.resolveUnit .sendWorker u device.sendWorkQueue).run afterPeek with
          | error e => simp [hpick,Except.map] at worker
          | ok out =>
            rcases out with ⟨selected,beforeWorker⟩
            simp only [hpick,Except.map,Except.ok.injEq,Prod.mk.injEq] at worker
            obtain ⟨rfl,rfl⟩ := worker
            exact ⟨rfl,by simpa [queue,hd] using
              (Queues.RxCredits.ClearWork.resolveUnit_member .sendWorker u device.sendWorkQueue
                afterPeek beforeWorker selected hpick).1⟩

theorem dispatch_erases : ErasesPrefix dispatch Env.runOneSendWorker := by
  intro w h
  rw [select_factor]
  simp only [dispatch,runPrefix_bind,runPrefix_captureRun]
  cases run : select.run w with
  | error e => simp only [StateT.run_bind,run]; rfl
  | ok out =>
    rcases out with ⟨pid,v⟩
    simp only [runPrefix_emit,runPrefix_lift,StateT.run_bind,run]
    rfl

theorem dispatch_receipts (w : World) :
    ∀ r ∈ (runPrefix dispatch w []).2,
      r.Valid select ∧ r.before = w ∧ r.after.wg = w.wg ∧ r.value ∈ queue w.wg := by
  simp only [dispatch,runPrefix_bind,runPrefix_captureRun]
  cases run : select.run w with
  | error e => simp
  | ok out =>
    rcases out with ⟨pid,v⟩
    simp only [runPrefix_emit,runPrefix_lift,List.nil_append,List.mem_singleton]
    intro r same
    subst r
    exact ⟨run,rfl,select_member w v pid run⟩

theorem dispatch_ticket (w : World) (carrier : Carrier h tickets w.wg)
    (r : RunWitness PeerId) (reached : r ∈ (runPrefix dispatch w []).2) :
    ∃ ticket rest, Selected tickets r.value ticket rest ∧ ticket.Valid h ∧
      Carrier h rest {w.wg with dev := (w.wg.dev.map
        (fun d => {d with sendWorkQueue := d.sendWorkQueue.erase r.value}))} := by
  have receipt := dispatch_receipts w r reached
  obtain ⟨ticket,rest,selected⟩ := select_exists tickets r.value (carrier.1 ▸ receipt.2.2.2)
  have frame := native_erase r.value w.wg _ w.ambient w.ambient rfl
  exact ⟨ticket,rest,selected,carrier.dequeue selected frame⟩

end Leanux.Proofs.WG.AuthenticatedEffects.SendWorkCauses
