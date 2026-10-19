import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceEnqueue
import Leanux.Proofs.WG.RetirementSecurity.CreateRefusalReceipts

/-! Rejected createData return codes identify the two actual native guards:
a dead peer, or a full peer queue. Device-ring EPIPE remains admitted/pending. -/
namespace Leanux.Proofs.WG.RetirementSecurity.CreateRefusal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

theorem enqueue_rejected (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a=.ok ((ret,v),b))
    (zero : ret≠0) (pipe : ret≠-WG.EPIPE) :
    ret=-WG.ENOSPC ∧ ∃first u c p t e,
      items.head?=some first ∧
      ((setTxSkb first fun q=>{q with state:=.uncrypted}).run w).run a=.ok (((),u),c) ∧
      ((getPeer pid).run u).run c=.ok ((p,t),e) ∧ MAX_QUEUED_PACKETS≤p.txQueue.count := by
  rw [enqueue_factor] at run
  cases head : items.head? with
  | none=>simp only [head] at run; cases run
  | some first=>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨_,u,c,markRun,p,t,e,peerRun,full,s,f,branchRun,tail⟩:=run
    have equals : full=decide (MAX_QUEUED_PACKETS≤p.txQueue.count) := by cases branchRun; rfl
    cases full with
    | true=>
      simp only [ite_true] at tail
      cases tail
      exact ⟨rfl,first,u,c,p,t,e,rfl,markRun,peerRun,of_decide_eq_true equals.symm⟩
    | false=>
      simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
      obtain ⟨_,s,g,_,tailRun⟩:=tail
      rcases enqueue_tail_result items g b tailRun with yes | refused
      · exact False.elim (zero yes)
      · exact False.elim (pipe refused)

theorem publication_return (item : List SkbId) (ret : Int) (a b : Ambient)
    (run : ((createPublishReturn item ret).run w).run a=.ok ((result,v),b)) : result=ret := by
  simp only [createPublishReturn,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨pipe,u,c,_,tail⟩:=run
  cases pipe with
  | false=>simp only [Bool.false_eq_true,ite_false] at tail; cases tail; rfl
  | true=>
    simp only [ite_true,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨_,_,_,_,done⟩:=tail
    cases done
    rfl

/-- The named refusal arm retains the actual source read and preceding call
cuts, rather than inferring a cause solely from a packet's eventual absence. -/
inductive Arm (r : Receipt) : Prop where
  | peerDead (p : Peer) :
      peerAt r.run.before r.peer=some p → p.isDead=true →
      r.run.value=-EINVAL → Arm r
  | peerQueueFull (p : Peer) (u : WGWorld) (a : Ambient) (q : Peer)
      (v : WGWorld) (b : Ambient) (first : SkbId) :
      peerAt r.run.before r.peer=some p → p.isDead=false →
      r.batch.head?=some first →
      ((branch .createDataDead false : WG.M Bool).run r.run.before).run r.run.ambientBefore=
        .ok ((false,r.run.before),a) →
      ((setTxSkb first fun t=>{t with state:=.uncrypted}).run r.run.before).run a=.ok (((),u),b) →
      ((getPeer r.peer).run u).run b=.ok ((q,v),b) →
      MAX_QUEUED_PACKETS≤q.txQueue.count → r.run.value=-WG.ENOSPC → Arm r

theorem codes (r : Receipt) (valid : r.Valid) :
    r.run.value=-EINVAL ∨ r.run.value=-WG.ENOSPC := by
  obtain ⟨_,run,zero,pipe⟩:=valid
  change ((createReturnSource r.peer r.batch).run r.run.before).run r.run.ambientBefore=
    .ok ((r.run.value,r.run.after),r.run.ambientAfter) at run
  simp only [createReturnSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,peerRun,dead,t,e,branchRun,tail⟩:=run
  cases dead with
  | true=>
    simp only [ite_true] at tail
    exact Or.inl (congrArg (fun pair : (Int×WGWorld)×Ambient=>pair.1.1) (Except.ok.inj tail)).symm
  | false=>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ret,s,f,enqueueRun,publishRun⟩:=tail
    have same := publication_return r.batch ret f r.run.ambientAfter publishRun
    exact Or.inr (same.trans (enqueue_rejected r.peer r.batch e f enqueueRun
      (fun h=>zero (same.trans h)) (fun h=>pipe (same.trans h))).1)

theorem classified (r : Receipt) (valid : r.Valid) : Arm r := by
  obtain ⟨_,run,zero,pipe⟩:=valid
  change ((createReturnSource r.peer r.batch).run r.run.before).run r.run.ambientBefore=
    .ok ((r.run.value,r.run.after),r.run.ambientAfter) at run
  simp only [createReturnSource,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,peerRun,dead,t,e,branchRun,tail⟩:=run
  obtain ⟨hu,hc,d,device,stored⟩:=Origins.getPeer_return r.peer r.run.before u p r.run.ambientBefore c peerRun
  subst u
  subst c
  have peer : peerAt r.run.before r.peer=some p := by simp [peerAt,device,stored]
  have equals : dead=p.isDead := by cases branchRun; rfl
  have ht : t=r.run.before := by cases branchRun; rfl
  subst t
  cases dead with
  | true=>
    simp only [ite_true] at tail
    exact Arm.peerDead p peer equals.symm
      (congrArg (fun pair : (Int×WGWorld)×Ambient=>pair.1.1) (Except.ok.inj tail)).symm
  | false=>
    simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
    obtain ⟨ret,s,f,enqueueRun,publishRun⟩:=tail
    have same := publication_return r.batch ret f r.run.ambientAfter publishRun
    obtain ⟨code,first,v,c,q,t,b,head,markRun,getRun,full⟩:=
      enqueue_rejected r.peer r.batch e f enqueueRun
        (fun h=>zero (same.trans h)) (fun h=>pipe (same.trans h))
    have hb := (Origins.getPeer_return r.peer v t q c b getRun).2.1
    subst b
    exact Arm.peerQueueFull p v e q t c first peer equals.symm head
      (by simpa only [←equals] using branchRun) markRun getRun full (same.trans code)

/-- All markers reached by one actual native call are classified, including
markers followed by a stopped cleanup. This deliberately makes no claim that
its whole batch has already been released. -/
theorem native_receipts (pid : PeerId) (items : List SkbId) (w : WGWorld) (a : Ambient) :
    ∀r∈(runStatePrefix (native pid items) w a []).2.filterMap refusal?,r.Valid ∧ Arm r := by
  have safe := (native_good pid items w a [] (by simp [Good])).choose_spec.2.1
  intro r member
  have valid := safe r member
  exact ⟨valid,classified r valid⟩

end Leanux.Proofs.WG.RetirementSecurity.CreateRefusal
