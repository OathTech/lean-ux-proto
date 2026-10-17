import Leanux.Proofs.WG.Queues.RxRingSocket

/-! TX completion and worker frames for the complete physical decrypt ring.
The source can send, release peers/keypairs and delete TX packets; none of
those are decrypt-ring operations. Frames describe normal endpoints only. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem sendSkbToPeer_cell pid bytes ds : SameView nativeCell (sendSkbToPeer pid bytes ds) := by
  ring_cell_source [sendSkbToPeer] using [send4_cell, send6_cell]

theorem timersDataSent_cell pid : SameView nativeCell (timersDataSent pid) := by
  have clock : SameView nativeCell (callerJiffies .timerJiffiesDataSent) :=
    (callerJiffies_sameWGWorld .timerJiffiesDataSent).factor nativeCell
  have jitter : SameView nativeCell (jitterBelowRekeyTimeout .newHandshakeJitter) :=
    (jitterBelowRekeyTimeout_sameWGWorld .newHandshakeJitter).factor nativeCell
  have arm (delay : Nat) (jc : Option UInt64) :
      SameView nativeCell (armTimer pid .newHandshake delay jc) := armTimer_cell pid _ delay jc
  ring_cell_source [timersDataSent] using [clock, jitter, modPeerTimerGuard_cell, arm]

theorem timersAnyAuthenticatedPacketSent_cell pid : SameView nativeCell (timersAnyAuthenticatedPacketSent pid) :=
  delTimer_cell pid .sendKeepalive

theorem keepKeyFresh_cell pid : SameView nativeCell (keepKeyFresh pid) := by
  have expired (d : Decision) (birth : Int64) (age : Nat) :
      SameView nativeCell (branchExpired d birth age) :=
    (branchExpired_sameWGWorld d birth age).factor nativeCell
  ring_cell_source [keepKeyFresh] using [expired, sendQueuedHandshakeInitiation_cell]

theorem createDataDone_cell pid item : SameView nativeCell (createDataDone pid item) := by
  ring_cell_source [createDataDone] using [timersTraversal_cell,
    timersAnyAuthenticatedPacketSent_cell, sendSkbToPeer_cell, timersDataSent_cell, keepKeyFresh_cell]

theorem txStep_cell pid : SameView nativeCell (txStep pid) := by
  have peek := fun (q : PrevQueue (List SkbId)) => kernel (prevQueuePeek_sameWGStore q)
  ring_cell_source [txStep] using [peek, createDataDone_cell, keypairPut_frame, peerPut_frame]

theorem txIter_cell (pid : PeerId) (resched : Leanux.M Bool)
    (hr : SameView cell resched) : SameView cell (txIter pid resched) := by
  ring_poll_source [txIter, workerIter] using [hr] with [txStep_cell]

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
  change Preserves (fun w => P (cell w)) (Leanux.Env.cryptAhead pid)
  unfold Leanux.Env.cryptAhead
  apply preserves_bind (ambient (get : AmbientM Ambient))
  intro inputs
  split
  · exact preserves_pure _
  · apply preserves_bind hp
    intro peer
    cases hitem : peer.txQueue.all.head? with
    | none => dsimp only; exact preserves_pure _
    | some item =>
      dsimp only
      cases hid : item.head? with
      | none => dsimp only; exact ambient (AmbientM.invariant _)
      | some id =>
        dsimp only
        apply preserves_bind (skb (SkbStore.getTx id))
        intro packet
        split
        · exact preserves_pure _
        · apply preserves_bind (ambient peekHiddenSite)
          intro site
          split
          · apply preserves_bind (ambient (get : AmbientM Ambient))
            intro inputs
            cases henc : inputs.suspended.find? (·.worker == .encryptWorker) with
            | none =>
              dsimp only
              apply (hoare_iff_run _ _ _).mpr
              intro w x v hi hr
              cases hr
            | some enc =>
              dsimp only
              apply preserves_bind hma
              intro _
              apply preserves_bind he
              intro result
              apply preserves_bind hme
              intro _
              cases result with
              | continued => exact ambient (modifyThe Ambient _ : AmbientM Unit)
              | ended =>
                apply (hoare_iff_run _ _ _).mpr
                intro w x v hi hr
                cases hr
              | yielded => exact ambient (AmbientM.invariant _)
          · exact preserves_pure _

end Leanux.Proofs.WG.Queues.RxRing
