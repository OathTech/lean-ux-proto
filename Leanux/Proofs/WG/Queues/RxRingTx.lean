import Leanux.Proofs.WG.Queues.RxRingSocket

/-! TX completion and worker frames for the complete physical decrypt ring.
The source can send, release peers/keypairs and delete TX packets; none of
those are decrypt-ring operations. Frames describe normal endpoints only. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem sendSkbToPeer_cell pid bytes ds : SameView nativeCell (sendSkbToPeer pid bytes ds) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_frame pid p).wp (fun t => t = s)
  have h4 := fun e => (send4_cell e (some pid) bytes ds true).wp (fun t => t = s)
  have h6 := fun e => (send6_cell e (some pid) bytes ds true).wp (fun t => t = s)
  mvcgen [sendSkbToPeer, hp, hs, h4, h6, branch, AmbientM.branch]

theorem timersDataSent_cell pid : SameView nativeCell (timersDataSent pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hj := (jitterBelowRekeyTimeout_sameWGWorld .newHandshakeJitter).wp (fun w => nativeCell w = s)
  have hg := (modPeerTimerGuard_cell pid).wp (fun t => t = s)
  have ha := fun n jc => (armTimer_cell pid .newHandshake n jc).wp (fun t => t = s)
  have hc := (callerJiffies_sameWGWorld .timerJiffiesDataSent).wp (fun w => nativeCell w = s)
  mvcgen [timersDataSent, hp, hj, hg, ha, hc, branch, AmbientM.branch]

theorem timersAnyAuthenticatedPacketSent_cell pid : SameView nativeCell (timersAnyAuthenticatedPacketSent pid) :=
  delTimer_cell pid .sendKeepalive

theorem keepKeyFresh_cell pid : SameView nativeCell (keepKeyFresh pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hk := fun id => (getKeypair_frame id).wp (fun t => t = s)
  have he := fun d birth age => (branchExpired_sameWGWorld d birth age).wp (fun w => nativeCell w = s)
  have hh := (sendQueuedHandshakeInitiation_cell pid false).wp (fun t => t = s)
  mvcgen [keepKeyFresh, hp, hk, he, hh, WG.andM, WG.orM, branch, branchCmp, invariant, AmbientM.branch, AmbientM.branchCmp, AmbientM.invariant]

theorem createDataDone_cell pid item : SameView nativeCell (createDataDone pid item) := by
  apply SameView.of_wp
  intro s
  have ht := (timersTraversal_cell pid).wp (fun t => t = s)
  have ha := (timersAnyAuthenticatedPacketSent_cell pid).wp (fun t => t = s)
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa [nativeCell, hd] using hi
  unfold Hoare at skb
  have hs := fun bytes ds => (sendSkbToPeer_cell pid bytes ds).wp (fun t => t = s)
  have hd := (timersDataSent_cell pid).wp (fun t => t = s)
  have hk := (keepKeyFresh_cell pid).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec (m := AmbientM) nativeCell (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    createDataDone, ht, ha, getTxSkb, skb, hs, hd, hk, WG.andM, branch, AmbientM.branch]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem txStep_cell pid : SameView nativeCell (txStep pid) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_frame pid p).wp (fun t => t = s)
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun w => nativeCell w = s) (fun _ w => nativeCell w = s) := by
    apply hoare_liftSkb a
    intro w d store hi hd
    simpa [nativeCell, hd] using hi
  unfold Hoare at skb
  have hq := fun (q : PrevQueue (List SkbId)) => (kernel (prevQueuePeek_sameWGStore q)).wp (fun t => t = s)
  have hd := fun item => (createDataDone_cell pid item).wp (fun t => t = s)
  have hk := fun kp => (keypairPut_frame kp false).wp (fun t => t = s)
  have hu := (peerPut_frame (some pid)).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec (m := AmbientM) nativeCell (α := α) (β := β) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    txStep, hp, hs, getTxSkb, skb, hq, hd, freeTxSkb, hk, hu, WG.andM, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜nativeCell w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem txIter_cell (pid : PeerId) (resched : Leanux.M Bool)
    (hr : SameView cell resched) : SameView cell (txIter pid resched) := by
  apply SameView.of_wp
  intro s
  have ht := (sameView_liftWG cell nativeCell (txStep pid)
    (txStep_cell pid) (fun _ _ _ h => h)).wp (fun t => t = s)
  have hh := hr.wp (fun t => t = s)
  mvcgen [txIter, workerIter, ht, hh, branch, AmbientM.branch]

theorem cryptAhead_cell pid : SameView cell (Leanux.Env.cryptAhead pid) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have native {α : Type} (a : WG.M α) (ha : SameView nativeCell a) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    (sameView_liftWG cell nativeCell a ha (fun _ _ _ h => h)).wp P
  have packets {α : Type} (a : SkbM α) : SameView nativeCell (liftSkb a) := by
    intro initial
    apply hoare_liftSkb
    intro g d store hg hd
    simpa [nativeCell, hd] using hg
  have skb {α : Type} (a : SkbM α) := native (liftSkb a) (packets a)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have hp := native (getPeer pid) (getPeer_frame pid)
  have he := actualEncryptIter_cell.wp P
  have hm := fun (f : List PeerId → List PeerId) =>
    native (modifyDev (fun d => {d with txWorkQueue := f d.txWorkQueue}))
      (modifyDev_cell _ (fun _ => rfl) (fun _ => rfl))
  have hma := hm (fun q => q ++ [pid])
  have hme := hm (fun q => q.erase pid)
  unfold Hoare at skb ambient hp hma hme
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.cryptAhead,
    hp, getTxSkb, skb, ambient, he, hma, hme, getAmbient, peekHiddenSite, modifyAmbient, invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals simp_all [cell]

end Leanux.Proofs.WG.Queues.RxRing
