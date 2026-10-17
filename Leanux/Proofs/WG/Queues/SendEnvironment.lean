import Leanux.Proofs.WG.Queues.SendDispatch
import Leanux.Proofs.WG.Queues.EnvClearDispatch

/-! The environment's actual recorded-unit/head selection uses an aligned
ordered reservation ledger. Source guards still determine whether it returns;
no pending flag or extra counter value is treated as an owner reservation. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.SendEnvironment
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open WorkReservations SendDispatch

/-- Only the existing non-NET_RX worker factor is used; both section records
and the actual queued send body remain inside the canonical WG adapter. -/
theorem runOneSendWorker_factor : Env.runOneSendWorker =
    (do
      let d ← liftWG getDev
      let some headPid := d.sendWorkQueue.head? | invariant "no queued handshake send work"
      let pid ← match ← peekUnit .sendWorker with
        | some u => resolveUnit .sendWorker u d.sendWorkQueue
        | none => pure headPid
      liftWG (runFlushedSendWork pid) : Leanux.M Unit) := by
  unfold Env.runOneSendWorker
  simp only [(pinned_const _private.Leanux.Proofs.WG.Lifetimes.EnvWorkersAudit.«0».Leanux.Proofs.WG.Lifetimes.runFlushedSendWork_lift)]
  rfl

/-- The returned witness follows the actual peek and optional resolver, then
runs exactly the native dequeue/section/body/section source at that Ambient
cut. The selected peer is proved to belong to the original queue. -/
theorem runOneSendWorker_selected (w v : World)
    (hr : Env.runOneSendWorker.run w = .ok ((),v)) :
    ∃ d headPid unit afterPeek pid beforeWorker,
      w.wg.dev = some d ∧ d.sendWorkQueue.head? = some headPid ∧
      (AmbientM.peekUnit .sendWorker).run w.ambient = .ok (unit,afterPeek) ∧
      ((match unit with
        | some u => AmbientM.resolveUnit .sendWorker u d.sendWorkQueue
        | none => pure headPid) : AmbientM PeerId).run afterPeek = .ok (pid,beforeWorker) ∧
      pid ∈ d.sendWorkQueue ∧
      ((runFlushedSendWork pid).run w.wg).run beforeWorker = .ok (((),v.wg),v.ambient) := by
  rw [runOneSendWorker_factor,MaterialOrigin.bind_ok] at hr
  obtain ⟨d,read,hread,tail⟩ := hr
  cases hd : w.wg.dev with
  | none =>
    simp [liftWG_run,getDev,hd,invariant,AmbientM.invariant] at hread
    change Except.error _ = Except.ok _ at hread
    cases hread
  | some device =>
    have getter : (liftWG getDev).run w = .ok (device,w) := by
      simp [liftWG_run,getDev,hd]
      rfl
    rw [getter] at hread
    simp only [Except.ok.injEq,Prod.mk.injEq] at hread
    have deq := hread.1
    have req := hread.2
    subst d
    subst read
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
          simp only [pure_bind] at worker
          refine ⟨device,headPid,none,afterPeek,headPid,afterPeek,rfl,hh,rfl,rfl,?_,?_⟩
          · exact List.mem_of_head? hh
          · exact (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) _ _ v () worker
        | some u =>
          rw [MaterialOrigin.bind_ok] at worker
          obtain ⟨pid,picked,resolve,worker⟩ := worker
          change (liftAmbient (AmbientM.resolveUnit .sendWorker u device.sendWorkQueue)).run
            {w with ambient := afterPeek} = .ok (pid,picked) at resolve
          rw [liftAmbient_run] at resolve
          cases hpick : (AmbientM.resolveUnit .sendWorker u device.sendWorkQueue).run afterPeek with
          | error e => simp [hpick,Except.map] at resolve
          | ok out =>
            rcases out with ⟨selected,beforeWorker⟩
            simp only [hpick,Except.map,Except.ok.injEq,Prod.mk.injEq] at resolve
            obtain ⟨rfl,rfl⟩ := resolve
            exact ⟨device,headPid,some u,afterPeek,selected,beforeWorker,rfl,hh,rfl,hpick,
              (ClearWork.resolveUnit_member .sendWorker u device.sendWorkQueue afterPeek beforeWorker selected hpick).1,
              (pinned_const _private.Leanux.Proofs.WG.Queues.RxPollCarrier.«0».Leanux.Proofs.WG.Queues.RxCredits.native_receipt) _ _ v () worker⟩

/-- One actual environment dispatch pays the selected work occurrence and
retains the ordered remainder. Duplicate peer ids are not collapsed. -/
theorem runOneSendWorker_normal (w v : World) (hi : Inv cs (owners ++ loans) w.wg)
    (queue : queueView w.wg = some (epoch,owners.map Owner.slot))
    (hr : Env.runOneSendWorker.run w = .ok ((),v)) :
    ∃ pid o restOwners, WorkReservations.Selected owners pid o restOwners ∧
      Inv cs (restOwners ++ loans) v.wg ∧
      queueView v.wg = some (epoch,restOwners.map Owner.slot) := by
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,hd,_,_,_,member,worker⟩ :=
    runOneSendWorker_selected w v hr
  have lists : d.sendWorkQueue = owners.map Owner.slot := by
    simpa only [queueView,hd,Option.map_some,Option.some.injEq,Prod.mk.injEq] using
      congrArg (Option.map Prod.snd) queue
  obtain ⟨o,restOwners,selected,kept,after⟩ := flushed_normal hi queue
    (lists ▸ member) beforeWorker v.ambient worker
  exact ⟨pid,o,restOwners,selected,kept,after⟩

/-- The original audit observer gives the same accounting at its actual normal
endpoint, for any incoming journal. This does not invent a state at a Stop. -/
theorem runOneSendWorkerAudit_normal (w v : World) (history : List AuditEvent)
    (hi : Inv cs (owners ++ loans) w.wg)
    (queue : queueView w.wg = some (epoch,owners.map Owner.slot))
    (hr : (runPrefix runOneSendWorkerAudit w history).1 = .ok ((),v)) :
    ∃ pid o restOwners, WorkReservations.Selected owners pid o restOwners ∧
      Inv cs (restOwners ++ loans) v.wg ∧
      queueView v.wg = some (epoch,restOwners.map Owner.slot) := by
  apply runOneSendWorker_normal w v hi queue
  exact (runOneSendWorkerAudit_erases w history).symm.trans hr


end Leanux.Proofs.WG.Queues.RxCredits.SendEnvironment
