import Leanux.Proofs.WG.Queues.RxRingSocket

/-! TX completion and worker frames for the complete physical decrypt ring.
The source can send, release peers/keypairs and delete TX packets; none of
those are decrypt-ring operations. Frames describe normal endpoints only. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem sendSkbToPeer_cell pid bytes ds : SameView cell (sendSkbToPeer pid bytes ds) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_frame pid p).wp (fun t => t = s)
  have h4 := fun e => (send4_cell e (some pid) bytes ds true).wp (fun t => t = s)
  have h6 := fun e => (send6_cell e (some pid) bytes ds true).wp (fun t => t = s)
  mvcgen [sendSkbToPeer, hp, hs, h4, h6, branch]

theorem timersDataSent_cell pid : SameView cell (timersDataSent pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hj := (kernel (jitterBelowRekeyTimeout_sameKernel .newHandshakeJitter)).wp (fun t => t = s)
  have hg := (modPeerTimerGuard_cell pid).wp (fun t => t = s)
  have ha := fun n jc => (armTimer_cell pid .newHandshake n jc).wp (fun t => t = s)
  have hc := (kernel (callerJiffies_sameKernel .timerJiffiesDataSent)).wp (fun t => t = s)
  mvcgen [timersDataSent, hp, hj, hg, ha, hc, branch]

theorem timersAnyAuthenticatedPacketSent_cell pid : SameView cell (timersAnyAuthenticatedPacketSent pid) :=
  delTimer_cell pid .sendKeepalive

theorem keepKeyFresh_cell pid : SameView cell (keepKeyFresh pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have he := fun d birth age => (kernel (branchExpired_sameKernel d birth age)).wp (fun t => t = s)
  have hh := (sendQueuedHandshakeInitiation_cell pid false).wp (fun t => t = s)
  mvcgen [keepKeyFresh, hp, hk, he, hh, WG.andM, WG.orM, branch, branchCmp, invariant]

theorem createDataDone_cell pid item : SameView cell (createDataDone pid item) := by
  apply SameView.of_wp
  intro s
  have ht := (timersTraversal_cell pid).wp (fun t => t = s)
  have ha := (timersAnyAuthenticatedPacketSent_cell pid).wp (fun t => t = s)
  have hg := fun id => (getTxSkb_cell id).wp (fun t => t = s)
  have hs := fun bytes ds => (sendSkbToPeer_cell pid bytes ds).wp (fun t => t = s)
  have hd := (timersDataSent_cell pid).wp (fun t => t = s)
  have hk := (keepKeyFresh_cell pid).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec cell (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    createDataDone, ht, ha, hg, hs, hd, hk, WG.andM, branch]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem txStep_cell pid : SameView cell (txStep pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_frame pid p).wp (fun t => t = s)
  have hg := fun id => (getTxSkb_cell id).wp (fun t => t = s)
  have hq := fun (q : PrevQueue (List SkbId)) => (kernel (prevQueuePeek_sameKernel q)).wp (fun t => t = s)
  have hd := fun item => (createDataDone_cell pid item).wp (fun t => t = s)
  have hf := fun id => (freeTxSkb_cell id).wp (fun t => t = s)
  have hk := fun kp => (keypairPut_frame kp false).wp (fun t => t = s)
  have hu := (peerPut_frame (some pid)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec cell (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    txStep, hp, hs, hg, hq, hd, hf, hk, hu, WG.andM, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem txIter_cell pid resched (hr : SameView cell resched) : SameView cell (txIter pid resched) := by
  apply SameView.of_wp
  intro s
  have ht := (txStep_cell pid).wp (fun t => t = s)
  have hh := hr.wp (fun t => t = s)
  mvcgen [txIter, workerIter, ht, hh, branch]

theorem cryptAhead_cell pid : SameView cell (Leanux.Env.cryptAhead pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hg := fun id => (getTxSkb_cell id).wp (fun t => t = s)
  have hh := (kernel peekHiddenSite_sameKernel).wp (fun t => t = s)
  have he := actualEncryptIter_cell.wp (fun t => t = s)
  have hm := fun (f : List PeerId → List PeerId) => (modifyDev_cell (fun d => {d with txWorkQueue := f d.txWorkQueue}) (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  have hma := hm (fun q => q ++ [pid])
  have hme := hm (fun q => q.erase pid)
  mvcgen [Leanux.Env.cryptAhead, hp, hg, hh, he, hma, hme, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell]

end Leanux.Proofs.WG.Queues.RxRing
