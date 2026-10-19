import Leanux.Proofs.WG.RetirementSecurity.TxWorkerHolders
import Leanux.Proofs.WG.RetirementSecurity.RxCleanupHolders

/-! Last-reference removal at original TX and RX disposal cuts. The saved
packet/batch reference is paid by the native call, and later peer/packet
cleanup cannot resurrect its removed allocation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.FinalDisposal
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem absent_retains {id : KeypairId} (none : keyAt w id=Option.none) (kept : Retains w v) : keyAt v id=Option.none := by
  cases found:keyAt v id with
  | none=>rfl
  | some k=>obtain ⟨old,earlier,_⟩:=kept.keys id k found; rw [none] at earlier; cases earlier

theorem absent_material {id : KeypairId} (none : keyAt w id=Option.none) (same : Origins.view v=Origins.view w) :
    keyAt v id=Option.none := by
  have cells := congrArg (fun view=>view.bind fun fields=>fields.2 id) same
  have equality : keyAt v id=keyAt w id := by
    simpa only [Origins.view,keyAt,Option.bind_map,Function.comp_def] using cells
  exact equality.trans none

theorem put_one {id : KeypairId} (found : keyAt w id=some k) (one : k.refcount=1) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some id) now).run w).run a=.ok (((),v),b)) :
    keyAt v id=none ∧ Unpublished id v := by
  cases device:w.dev with
  | none=>simp [keyAt,device] at found
  | some d=>
    have effect := put_effect id now w v a b d k device (by simpa [keyAt,device] using found) run
    exact ⟨effect.final one,effect.unpublished (.inr one)⟩

theorem free_list_credits (items : List SkbId) (credits : Credits.Ledger) :
    Preserves (Credits.Exact credits) (Queues.TxDisposition.freeList items) := by
  induction items with
  | nil=>exact preserves_pure ()
  | cons id rest ih=>
    rw [Queues.TxDisposition.freeList_cons]
    exact preserves_bind (Credits.freeTx_preserves id credits) (fun _=>ih)

theorem packet_key (action : SkbM α) (id : KeypairId) : SameView (fun w=>keyAt w id) (liftSkb action) := by
  intro initial
  apply hoare_liftSkb action
  intro w d store hi device
  simpa [keyAt,device] using hi

theorem tx (allocation : Credits.Allocation) (remaining : Credits.Ledger)
    (account : Credits.Exact (allocation::remaining) w) (last : allocation∉remaining)
    (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((Queues.TxDisposition.disposeSource pid items allocation.slot).run w).run a=.ok ((result,v),b)) :
    result=true ∧ keyAt v allocation.slot=none := by
  have factor : Queues.TxDisposition.disposeSource pid items allocation.slot=(do
      Queues.TxDisposition.freeList items
      keypairPut (some allocation.slot) false
      peerPut (some pid)
      pure true) := by simp [Queues.TxDisposition.disposeSource,Queues.TxDisposition.freeList]
  rw [factor] at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨r,u,c,freeRun,r2,t,e,putRun,r3,s,f,peerRun,tail⟩ := run
  cases r
  cases r2
  cases r3
  have paid := (hoare_iff_run_ambient _ _ _).mp (free_list_credits items (allocation::remaining))
    w a () u c account freeRun
  have erased := paid.put_last last false c e putRun
  have absent := absent_retains erased.1 (peerPut_retains (some pid) t s e f peerRun)
  cases tail
  exact ⟨rfl,absent⟩

theorem rx (allocation : Credits.Allocation) (remaining : Credits.Ledger)
    (account : Credits.Exact (allocation::remaining) w) (last : allocation∉remaining)
    (id : SkbId) (pkt : RxPacket) (flag : Bool) (key : pkt.keypair=allocation.slot) (a b : Ambient)
    (run : ((Queues.RxCredits.cleanup id pkt flag).run w).run a=.ok (((),v),b)) :
    keyAt v allocation.slot=none := by
  simp only [Queues.RxCredits.cleanup,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨r,u,c,putRun,r2,t,e,peerRun,_,s,f,branchRun,freeRun⟩ := run
  cases r
  cases r2
  rw [key] at putRun
  have erased := account.put_last last false a c putRun
  have absent := absent_retains erased.1 (peerPut_retains (some pkt.peer) u t c e peerRun)
  have same : s=t := by cases branchRun; rfl
  subst s
  exact ((ProjectedAction.iff_run_ambient _ _ _).mp
    (packet_key (SkbStore.freeRx id) allocation.slot) t f () v b freeRun).trans absent

end Leanux.Proofs.WG.RetirementSecurity.FinalDisposal
