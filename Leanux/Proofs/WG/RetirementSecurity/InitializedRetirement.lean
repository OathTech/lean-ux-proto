import Leanux.Proofs.WG.RetirementSecurity.HolderInitialized
import Leanux.Proofs.WG.RetirementSecurity.FinalTxWorker

/-! Operational retirement from initialized source endpoints. Actual work
execution is the progress premise; retained packet debts remain in the exact
native account until their actual final disposal. -/
namespace Leanux.Proofs.WG.RetirementSecurity.InitializedRetirement
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem clear_worker (trace : Runner.Trace) (placeholders : Bool)
    (initialized : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (dispatch : Env.runOneClearWorker.run w=.ok ((),v)) :
    HolderAccount [] v.wg ∧ ∃d pid,w.wg.dev=some d ∧ pid∈d.clearWorkQueue ∧
      SlotsCleared pid v.wg ∧ Retains w.wg v.wg :=
  (HolderInitialized.account trace placeholders initialized).dispatched_zero dispatch

/-- The selected normal native TX worker consumes the last actual key
holder. The explicit scheduling premise is that this exact worker returns
true, after encryption/dead publication has made the batch ready. -/
theorem final_tx (trace : Runner.Trace) (placeholders : Bool)
    (initialized : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (allocation : Credits.Allocation) (projected : durableLoans w.wg=some loans)
    (last : (loans.map (·.allocation)).count allocation=1)
    (pid : PeerId) (p : Peer) (items : List SkbId) (headId : SkbId) (head : DataPacket)
    (peer : peerAt w.wg pid=some p) (queued : p.txQueue.all.head?=some items)
    (first : items.head?=some headId) (packet : TxDisposition.txPackets w.wg headId=some head)
    (key : head.keypair=allocation.slot) (b : Ambient)
    (worker : ((txStep pid).run w.wg).run w.ambient=.ok ((true,v),b)) :
    keyAt v allocation.slot=none :=
  FinalDisposal.tx_step allocation (HolderInitialized.account trace placeholders initialized)
    projected last pid p items headId head peer queued first packet key w.ambient b worker

/-- Store removal prevents the native getter from returning any keypair.
The mirror establishes no physical-memory zeroisation statement. -/
theorem removed_cannot_read {id : KeypairId} (removed : keyAt w id=none) (a b : Ambient)
    (run : ((getKeypair id).run w).run a=.ok ((k,v),b)) : False := by
  obtain ⟨_,_,d,device,found⟩ := KeyTimes.getKeypair_return id w v k a b run
  have present : keyAt w id=some k := by simp [keyAt,device,found]
  rw [removed] at present
  cases present

/-- A removed key cannot be successfully reacquired by the native reference
getter. Fresh allocation is a distinct operation with a new allocation stamp. -/
theorem removed_cannot_acquire {id : KeypairId} (removed : keyAt w id=none) (a b : Ambient)
    (run : ((keypairGet (some id)).run w).run a=.ok ((out,v),b)) : False := by
  unfold keypairGet at run
  simp only [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨null,u,c,test,tail⟩ := run
  have testRun : ((branch .keypairGetNull false : WG.M Bool).run w).run a=
      .ok ((null,u),c) := test
  have noNull : null=false ∧ u=w := by cases testRun; exact ⟨rfl,rfl⟩
  obtain ⟨rfl,rfl⟩ := noNull
  simp only [Bool.false_eq_true,ite_false,MaterialOrigin.bind_ok_ambient] at tail
  obtain ⟨k,t,e,read,_⟩ := tail
  exact removed_cannot_read removed c e read

end Leanux.Proofs.WG.RetirementSecurity.InitializedRetirement
