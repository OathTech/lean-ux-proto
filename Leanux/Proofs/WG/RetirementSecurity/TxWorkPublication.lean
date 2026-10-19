import Leanux.Proofs.WG.RetirementSecurity.TxWorkFrames

/-! A completed actual publication leaves its selected owner's TX work
queued. This is the source obligation used when a queued batch changes from
uncrypted to DEAD/CRYPTED; the owner is the native key-derived read. -/
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

def schedule (pid : PeerId) : WG.M Unit := do
  if !(←getDev).txWorkQueue.contains pid || (←peekQueuedUnit .txWorker pid) then
    recordQueued .txWorker pid
    modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]}

theorem schedule_member (pid : PeerId) (a b : Ambient)
    (run : ((schedule pid).run w).run a=.ok (((),v),b)) : pid∈queued v := by
  unfold schedule at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨d,u,c,readRun,decision,t,e,peekRun,tail⟩:=run
  have read : u=w ∧ c=a ∧ w.dev=some d := by
    cases device:w.dev with
    | none=>simp [getDev,device,invariant,AmbientM.invariant] at readRun; cases readRun
    | some original=>
      simp [getDev,device] at readRun
      obtain ⟨⟨rfl,rfl⟩,rfl⟩:=readRun
      exact ⟨rfl,rfl,rfl⟩
  obtain ⟨hu,hc,device⟩:=read
  subst u
  subst c
  have same:t=w := (hoare_iff_run_ambient _ _ _).mp
    (hoare_liftAmbient (AmbientM.peekQueuedUnit .txWorker pid) (fun t=>t=w))
      w a decision t e rfl peekRun
  subst t
  by_cases guard:(!d.txWorkQueue.contains pid || decision)=true
  · simp only [guard,ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,t,f,recordRun,writeRun⟩:=tail
    have same:t=w := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.recordQueued .txWorker pid) (fun t=>t=w))
        w e () t f rfl recordRun
    subst t
    cases writeRun
    simp [queued,device]
  · simp only [guard] at tail
    cases tail
    have contains:d.txWorkQueue.contains pid=true := by
      cases member:d.txWorkQueue.contains pid <;> simp_all
    simpa only [queued,device,Option.map_some,Option.getD_some] using
      List.contains_iff_mem.mp contains

theorem middle_factor (pid : PeerId) (first : SkbId) (state : PacketState) :
    TxDisposition.publicationMiddle pid first state=(do
      if !((←getPeer pid).txQueue.all.any (·.head? == some first)) then
        invariant "an item for the tx worker that is not on its peer's tx_queue"
      setTxSkb first fun p=>{p with state}
      _←cpumaskChooseOnline pid
      schedule pid) := rfl

theorem middle_member (pid : PeerId) (first : SkbId) (state : PacketState) (a b : Ambient)
    (run : ((TxDisposition.publicationMiddle pid first state).run w).run a=.ok (((),v),b)) :
    pid∈queued v := by
  rw [middle_factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,_,rest⟩:=run
  split at rest
  · simp only [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨_,_,_,stopped,_⟩:=rest
    cases stopped
  · simp only [MaterialOrigin.bind_ok_ambient] at rest
    obtain ⟨_,t,e,_,_,s,f,_,tail⟩:=rest
    exact schedule_member pid f b tail

/-- Publication's endpoint schedules the actual owner returned by its native
peer dereference. The source witness keeps that selection distinct from the
original enqueue caller's peer; no owner-equality premise is invented here. -/
theorem publication_member (items : List SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx items state).run w).run a=.ok (((),v),b)) :
    ∃first packet u c pid t e,
      items.head?=some first ∧
      ((getTxSkb first).run w).run a=.ok ((packet,u),c) ∧
      ((IndexOwner.peerDeref (.keypair packet.keypair)).run u).run c=.ok ((pid,t),e) ∧
      pid∈queued v := by
  rw [TxDisposition.publication_factor] at run
  cases head:items.head? with
  | none=>simp only [head] at run; cases run
  | some first=>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨packet,u,c,getRun,pid,t,e,ownerRun,_,s,f,_,_,x,g,middle,put⟩:=run
    have member:=middle_member pid first state f g middle
    have same:queued v=queued x := (ProjectedAction.iff_run_ambient _ _ _).mp
      (peer_put (some pid)) x g () v b put
    exact ⟨first,packet,u,c,pid,t,e,rfl,getRun,ownerRun,same.symm ▸ member⟩

end Leanux.Proofs.WG.RetirementSecurity.TxWork
