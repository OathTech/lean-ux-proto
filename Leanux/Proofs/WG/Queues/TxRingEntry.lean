import Leanux.Proofs.WG.Queues.TxRingCuts
import Leanux.Proofs.Framing.Product

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
  Ring.Source.enqueue (liftWG (enqueuePerDeviceAndPeer pid item)) item

theorem enqueue_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (enqueue pid item) (liftWG (enqueuePerDeviceAndPeer pid item)) := Ring.Source.enqueue_erases _ _

theorem enqueue_preserves (pid : PeerId) (item : List SkbId) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (enqueue pid item) := by
  apply Ring.Source.enqueue_preserves _ item
  · intro w ret v hr
    rw [liftWG_run] at hr
    cases he : ((enqueuePerDeviceAndPeer pid item).run w.wg).run w.ambient with
    | error e => simp [he, Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨x, g⟩, ambient⟩
      simp [he, Except.map] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact enqueue_result pid item w.wg g w.ambient ambient x he
  · intro w v r hc hr
    rw [liftWG_run] at hr
    cases he : ((enqueuePerDeviceAndPeer pid item).run w.wg).run w.ambient with
    | error e => simp [he, Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨x, g⟩, ambient⟩
      simp [he, Except.map] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact enqueue_free pid item hc he

def poll : Obs (Option (List SkbId)) := Ring.Source.poll (liftWG pollSource)

theorem poll_erases : ErasesPrefix poll (liftWG pollSource) := Ring.Source.poll_erases _

theorem poll_preserves : PrefixPreserves (Inv deviceIndex initial) (Safe initial) poll := by
  apply Ring.Source.poll_preserves
  intro w out v r hc hr
  rw [liftWG_run] at hr
  cases he : (pollSource.run w.wg).run w.ambient with
  | error e => simp [he, Except.map] at hr
  | ok result =>
    rcases result with ⟨⟨x, g⟩, ambient⟩
    simp [he, Except.map] at hr
    rcases hr with ⟨rfl, rfl⟩
    exact poll_result hc he

theorem lift_native_frame {a : WG.M α} (ha : SameView nativeCell a) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (liftPrefix (liftWG a)) :=
  lift_frame (sameView_liftWG cell nativeCell a ha (fun _ _ _ he => he))

private theorem lift_forIn (xs : List α) (init : β) (f : α → β → WG.M (ForInStep β)) :
    liftWG (forIn xs init f) = forIn xs init (fun x b => liftWG (f x b)) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.forIn_cons, liftWG_bind]
    congr 1
    funext result
    cases result <;> simp only [liftWG_pure, ih]


def create (pid : PeerId) (item : List SkbId) : Obs Unit := do
  let some first := item.head? | liftPrefix (liftWG (invariant "an empty ring item"))
  let ret ← do
    if ← liftPrefix (liftWG (branch .createDataDead (← liftPrefix (liftWG (getPeer pid))).isDead)) then pure (-EINVAL)
    else
      let ret ← enqueue pid item
      if ← liftPrefix (liftWG (branch .createDataEpipe (ret == -WG.EPIPE))) then liftPrefix (liftWG (enqueuePerPeerTx item .dead))
      pure ret
  if ← liftPrefix (liftWG (branch .createDataOk (ret == 0))) then return
  if ← liftPrefix (liftWG (branch .createDataOkEpipe (ret == -WG.EPIPE))) then return
  liftPrefix (liftWG (keypairPut (some (← liftPrefix (liftWG (getTxSkb first))).keypair) false))
  liftPrefix (liftWG (peerPut (some pid)))
  for id in item do liftPrefix (liftWG (freeTxSkb id))

theorem create_erases (pid : PeerId) (item : List SkbId) :
    ErasesPrefix (create pid item) (liftWG (createData pid item)) := by
  unfold create createData
  cases he : item.head? with
  | none => exact erasesPrefix_lift _
  | some first =>
    simp only [liftWG_bind, liftWG_pure, lift_forIn, apply_ite]
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro p
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro dead
    have tail (ret : Int) : ErasesPrefix (Event := Event)
        (do
          if ← liftPrefix (liftWG (branch .createDataOk (ret == 0))) then return
          if ← liftPrefix (liftWG (branch .createDataOkEpipe (ret == -WG.EPIPE))) then return
          liftPrefix (liftWG (keypairPut (some (← liftPrefix (liftWG (getTxSkb first))).keypair) false))
          liftPrefix (liftWG (peerPut (some pid)))
          for id in item do liftPrefix (liftWG (freeTxSkb id)))
        (do
          if ← liftWG (branch .createDataOk (ret == 0)) then return
          if ← liftWG (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
          liftWG (keypairPut (some (← liftWG (getTxSkb first)).keypair) false)
          liftWG (peerPut (some pid))
          for id in item do liftWG (freeTxSkb id)) := by
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
            erasesPrefix_bind (erasesPrefix_lift (liftWG (freeTxSkb id))) (fun _ => erasesPrefix_pure _)))
          intro _
          exact erasesPrefix_pure _
    try simp only [liftWG_bind, liftWG_pure, lift_forIn, apply_ite]
    split
    · simpa only [pure_bind, liftWG_bind, liftWG_pure] using tail (-EINVAL)
    · apply erasesPrefix_bind (enqueue_erases _ _)
      intro ret
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro pipe
      split
      · simpa only [pure_bind] using erasesPrefix_bind (erasesPrefix_lift (liftWG (enqueuePerPeerTx item .dead))) (fun _ => tail ret)
      · simpa only [pure_bind] using tail ret

theorem create_preserves (pid : PeerId) (item : List SkbId) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (create pid item) := by
  have ambient {α : Type} (a : AmbientM α) :
      SameView nativeCell (StateT.lift a : WG.M α) := by
    intro initial
    exact hoare_liftAmbient a _
  have packet {α : Type} (a : SkbM α) : SameView nativeCell (liftSkb a) := by
    intro initial
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [nativeCell, hd] using hg
  unfold create
  simp only [branch, invariant, getTxSkb, freeTxSkb]
  repeat' first
    | with_reducible exact enqueue_preserves _ _
    | with_reducible exact lift_native_frame (enqueuePeer_frame _ _)
    | with_reducible exact lift_native_frame (getPeer_frame _)
    | with_reducible exact lift_native_frame (packet _)
    | with_reducible exact lift_native_frame (keypairPut_frame _ _)
    | with_reducible exact lift_native_frame (peerPut_frame _)
    | with_reducible exact lift_native_frame (ambient _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.Queues.TxRing
