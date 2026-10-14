import Leanux.Proofs.WG.Queues.TxRingCuts

/-! Complete TX admission and createData observers. The enqueue source's
installation is followed only by pure return, so its event is appended there.
ENOSPC has no ring offer; EPIPE is a refusal, not a packet disposal. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

theorem Inv.safe (hi : Inv deviceIndex initial h w) : Safe initial h := Ring.Source.Inv.safe hi

theorem lift_frame (ha : SameView cell a) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (liftPrefix a) := Ring.Source.lift_frame ha

def enqueue (pid : PeerId) (item : List SkbId) : Obs Int :=
  Ring.Source.enqueue (enqueuePerDeviceAndPeer pid item) item

theorem enqueue_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (enqueue pid item) (enqueuePerDeviceAndPeer pid item) := Ring.Source.enqueue_erases _ _

theorem enqueue_preserves (pid : PeerId) (item : List SkbId) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (enqueue pid item) :=
  Ring.Source.enqueue_preserves _ item
    (fun w ret v hr => enqueue_result pid item w v ret hr)
    (fun _ _ _ hc hr => enqueue_free pid item hc hr)

def poll : Obs (Option (List SkbId)) := Ring.Source.poll pollSource

theorem poll_erases : ErasesPrefix poll pollSource := Ring.Source.poll_erases _

theorem poll_preserves : PrefixPreserves (Inv deviceIndex initial) (Safe initial) poll :=
  Ring.Source.poll_preserves _ (fun _ _ _ _ hc hr => poll_result hc hr)

def create (pid : PeerId) (item : List SkbId) : Obs Unit := do
  let some first := item.head? | liftPrefix (invariant "an empty ring item")
  let ret ← do
    if ← liftPrefix (branch .createDataDead (← liftPrefix (getPeer pid)).isDead) then pure (-EINVAL)
    else
      let ret ← enqueue pid item
      if ← liftPrefix (branch .createDataEpipe (ret == -WG.EPIPE)) then liftPrefix (enqueuePerPeerTx item .dead)
      pure ret
  if ← liftPrefix (branch .createDataOk (ret == 0)) then return
  if ← liftPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
  liftPrefix (keypairPut (some (← liftPrefix (getTxSkb first)).keypair) false)
  liftPrefix (peerPut (some pid))
  for id in item do liftPrefix (freeTxSkb id)

theorem create_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (create pid item) (createData pid item) := by
  unfold create createData
  cases he : item.head? with
  | none => exact erasesPrefix_lift _
  | some first =>
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro p
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro dead
    have tail (ret : Int) : ErasesPrefix (Event := Event)
        (do
          if ← liftPrefix (branch .createDataOk (ret == 0)) then return
          if ← liftPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
          liftPrefix (keypairPut (some (← liftPrefix (getTxSkb first)).keypair) false)
          liftPrefix (peerPut (some pid))
          for id in item do liftPrefix (freeTxSkb id))
        (do
          if ← branch .createDataOk (ret == 0) then return
          if ← branch .createDataOkEpipe (ret == -WG.EPIPE) then return
          keypairPut (some (← getTxSkb first).keypair) false
          peerPut (some pid)
          for id in item do freeTxSkb id) := by
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro ok
      split
      · exact erasesPrefix_pure _
      · apply erasesPrefix_bind (erasesPrefix_lift _)
        intro pipe
        split
        · exact erasesPrefix_pure _
        · apply erasesPrefix_bind (erasesPrefix_lift _)
          intro pkt
          apply erasesPrefix_bind (erasesPrefix_lift _)
          intro _
          apply erasesPrefix_bind (erasesPrefix_lift _)
          intro _
          apply erasesPrefix_bind (erasesPrefix_forIn _ _ _ _ (fun id _ =>
            erasesPrefix_bind (erasesPrefix_lift (freeTxSkb id)) (fun _ => erasesPrefix_pure _)))
          intro _
          exact erasesPrefix_pure _
    split
    · simpa only [pure_bind] using tail (-EINVAL)
    · apply erasesPrefix_bind (enqueue_erases _ _)
      intro ret
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro pipe
      split
      · simpa only [pure_bind] using erasesPrefix_bind (erasesPrefix_lift (enqueuePerPeerTx item .dead)) (fun _ => tail ret)
      · simpa only [pure_bind] using tail ret

theorem create_preserves (pid : PeerId) (item : List SkbId) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (create pid item) := by
  unfold create
  repeat' first
    | with_reducible exact enqueue_preserves _ _
    | with_reducible exact lift_frame (enqueuePeer_frame _ _)
    | with_reducible exact lift_frame (getPeer_frame _)
    | with_reducible exact lift_frame (getTx_frame _)
    | with_reducible exact lift_frame (keypairPut_frame _ _)
    | with_reducible exact lift_frame (peerPut_frame _)
    | with_reducible exact lift_frame (freeTx_frame _)
    | with_reducible exact lift_frame (kernel (sameKernel_branch _ _))
    | with_reducible exact lift_frame (invariant_frame _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.Queues.TxRing
