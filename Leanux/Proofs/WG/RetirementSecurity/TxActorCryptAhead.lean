import Leanux.Proofs.WG.RetirementSecurity.TxActorEncrypt
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceScheduler
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageScheduler

/-! The real crypt-ahead correction temporarily requeues its active TX peer,
executes the selected encrypt iteration, then restores that active obligation.
Incrementing the suspended encrypt record cannot discard another TX actor. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem covered_work (f : List PeerId→List PeerId) :
    Preserves (Covered locals crypt) (modifyDev fun d=>{d with txWorkQueue:=f d.txWorkQueue}) :=
  TxCovered.join (OccurrenceScheduler.work_queue f) (TxCoverageScheduler.work_queue f)

theorem At.requeue (before : At (Covered locals crypt) crypt [pid] w)
    (run : (liftWG (modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]})).run w=.ok ((),v)) :
    At (Covered locals crypt) crypt [] v := by
  have native:=HolderPoll.native_receipt run
  have service:=before.1.requeue w.ambient v.ambient native
  have kept:=(hoare_iff_run_ambient _ _ _).mp (covered_work (·++[pid]))
    w.wg w.ambient () v.wg v.ambient before.2 native
  cases run
  exact ⟨service,kept⟩

theorem At.crypt_increment (before : At P crypt tx w) (enc : Activation)
    (run : (modifyAmbient fun s=>{s with suspended:=s.suspended.map fun x=>
      if x == enc then {x with iterations:=x.iterations+1} else x} : Leanux.M Unit).run w=.ok ((),v)) :
    At P crypt tx v := by
  have service:=TxWork.crypt_increment before.1 enc run
  cases run
  exact ⟨service,before.2⟩

def cryptAheadBody (pid : PeerId) (enc : Activation) : Leanux.M Unit := do
  modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]}
  let result←encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)
  modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}
  match result with
  | .continued=>
    modifyAmbient fun s=>{s with suspended:=s.suspended.map fun x=>
      if x == enc then {x with iterations:=x.iterations+1} else x}
  | .ended=>throw (.hidden "the encrypt activation's queue is empty, but the next record is the traversal timer's caller read or arm (site 426 or 100)")
  | .yielded=>invariant "the encrypt activation yielded on a record that is not a resched"

theorem crypt_ahead_body
    (callback : ∀item : Option (List SkbId),Preserves
      (At (Covered locals (item.toList++crypt)) (item.toList++crypt) []) Env.napiSoftirq)
    (before : At (Covered locals crypt) crypt [pid] w)
    (run : (cryptAheadBody pid enc).run w=.ok ((),v)) : At (Covered locals crypt) crypt [pid] v := by
  unfold cryptAheadBody at run
  rw [MaterialOrigin.bind_ok] at run
  obtain ⟨_,u,queued,tail⟩:=run
  have idle:=before.requeue queued
  rw [MaterialOrigin.bind_ok] at tail
  obtain ⟨result,t,encrypted,tail⟩:=tail
  have ready:=encrypt_iteration_service callback idle encrypted
  rw [MaterialOrigin.bind_ok] at tail
  obtain ⟨_,s,dispatched,tail⟩:=tail
  have active:=ready.dispatch pid (covered_work (·.erase pid)) dispatched
  cases result with
  | continued=>exact active.crypt_increment enc tail
  | ended=>cases tail
  | yielded=>cases tail

def cryptAheadSource (pid : PeerId) : Leanux.M Unit := do
  if (←getAmbient).hidden.isNone then return
  let some item := (←getPeer pid).txQueue.all.head? | return
  let some id := item.head? | invariant "an empty ring item"
  if (←getTxSkb id).state != .uncrypted then return
  let next←peekHiddenSite
  unless next == some HiddenSite.modTimerArm.info.id || next == some HiddenSite.timerJiffiesTraversal.info.id do return
  let some enc := (←getAmbient).suspended.find? (·.worker == .encryptWorker)
    | throw (.hidden "the tx worker's head is uncrypted and no encrypt activation is suspended, but the next record is the traversal timer's caller read or arm (site 426 or 100)")
  cryptAheadBody pid enc

theorem cryptAheadSource_eq (pid : PeerId) : cryptAheadSource pid=Env.cryptAhead pid := rfl

theorem crypt_ahead_service
    (callback : ∀item : Option (List SkbId),Preserves
      (At (Covered locals (item.toList++crypt)) (item.toList++crypt) []) Env.napiSoftirq)
    (pid : PeerId) : Preserves (At (Covered locals crypt) crypt [pid]) (Env.cryptAhead pid) := by
  let P := At (Covered locals crypt) crypt [pid]
  have read : Preserves P (getAmbient : Leanux.M Ambient) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
    exact before
  have peer (q : PeerId) : Preserves P (monadLift (getPeer q) : Leanux.M Peer) :=
    (TxActorFrames.peer q).wp P
  have packet (skb : SkbId) : Preserves P (monadLift (getTxSkb skb) : Leanux.M DataPacket) :=
    (TxActorFrames.packet skb).wp P
  have peek : Preserves P (peekHiddenSite : Leanux.M (Option Nat)) :=
    at_frame (TxActorFrames.lift_ambient TxActorFrames.peek_site)
  have stop {α : Type} (error : Stop) : Preserves P (throw error : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
  have invariant {α : Type} (message : String) : Preserves P (Leanux.invariant message : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases run
  have finish (enc : Activation) : Preserves P (cryptAheadBody pid enc) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    cases result
    exact crypt_ahead_body callback before run
  change Preserves P _
  rw [←cryptAheadSource_eq]
  routing_tx_source [cryptAheadSource] using [finish,read,peer,packet,peek,stop,invariant]

end Leanux.Proofs.WG.RetirementSecurity.TxWork
