import Leanux.Proofs.WG.Queues.RxRingCuts
import Leanux.Proofs.Framing.Product

/-! Ring-only observers of complete receive entry. Enqueue's installation is
its last mutation followed only by pure return 0, so appending at that return
crosses no source effect. ENOSPC and every pre-install Stop emit no ring event;
EPIPE records a refused offer and does not assert a packet disposal. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Ring.Journal

theorem lift_frame (ha : SameView cell a) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (liftPrefix a) :=
  Ring.Source.lift_frame ha

def enqueue (id : SkbId) : Obs Int := Ring.Source.enqueue (liftWG (enqueuePerDeviceAndPeerRx id)) id

theorem enqueue_erases (id : SkbId) : ErasesPrefix (enqueue id) (liftWG (enqueuePerDeviceAndPeerRx id)) :=
  Ring.Source.enqueue_erases _ _

theorem enqueue_preserves (id : SkbId) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (enqueue id) := by
  apply Ring.Source.enqueue_preserves _ id
  · intro w ret v hr
    rw [liftWG_run] at hr
    cases he : ((enqueuePerDeviceAndPeerRx id).run w.wg).run w.ambient with
    | error e => simp [he, Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨x, g⟩, ambient⟩
      simp [he, Except.map] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact enqueue_result id w.wg g w.ambient ambient x he
  · intro w v r hc hr
    rw [liftWG_run] at hr
    cases he : ((enqueuePerDeviceAndPeerRx id).run w.wg).run w.ambient with
    | error e => simp [he, Except.map] at hr
    | ok out =>
      rcases out with ⟨⟨x, g⟩, ambient⟩
      simp [he, Except.map] at hr
      rcases hr with ⟨rfl, rfl⟩
      exact enqueue_free id hc he

def poll : Obs (Option SkbId) := Ring.Source.poll (liftWG pollSource)

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

def enqueuePeer (irq : Obs Unit) (id : SkbId) (state : PacketState) : Obs Unit := do
  let pid ← liftPrefix (liftWG (IndexOwner.peerDeref (.keypair (← liftPrefix (liftWG (getRxSkb id))).keypair)))
  liftPrefix (liftWG (peerGet pid))
  let p ← liftPrefix (liftWG (getPeer pid))
  if !(p.rxQueue.all.contains id) then liftPrefix (liftWG (invariant "a decrypted packet that is not on its peer's rx_queue"))
  liftPrefix (liftWG (setRxSkb id fun q => {q with state}))
  liftPrefix (liftWG (setPeer pid {p with napiScheduled := true}))
  irq
  liftPrefix (liftWG (peerPut (some pid)))

theorem enqueuePeer_erases (hi : ErasesPrefix irq originalIrq) (id : SkbId) (state : PacketState) :
    ErasesPrefix (enqueuePeer irq id state) (enqueuePerPeerRx originalIrq id state) := by
  unfold enqueuePeer enqueuePerPeerRx
  repeat' first
    | with_reducible exact hi
    | with_reducible exact erasesPrefix_lift _
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals exact erasesPrefix_lift _

theorem enqueuePeer_preserves (hi : PrefixPreserves (Inv deviceIndex initial) (Safe initial) irq)
    (id : SkbId) (state : PacketState) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (enqueuePeer irq id state) := by
  have packets {α : Type} (a : SkbM α) : SameView nativeCell (liftSkb a) := by
    intro initial
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [nativeCell, hd] using hg
  have ambient {α : Type} (a : AmbientM α) : SameView nativeCell (StateT.lift a : WG.M α) := by
    intro initial
    exact hoare_liftAmbient a _
  have owner (o : IndexOwner) : SameView nativeCell o.peerDeref := by
    intro initial
    exact indexOwner_peerDeref_preserves o _
  unfold enqueuePeer
  simp only [getRxSkb, setRxSkb, invariant]
  repeat' first
    | with_reducible exact hi
    | with_reducible exact lift_native_frame (packets _)
    | with_reducible exact lift_native_frame (owner _)
    | with_reducible exact lift_native_frame (getPeer_frame _)
    | with_reducible exact lift_native_frame (peerGet_frame _)
    | with_reducible exact lift_native_frame (setPeer_frame _ _)
    | with_reducible exact lift_native_frame (peerPut_frame _)
    | with_reducible exact lift_native_frame (ambient _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

def consume (msg : List UInt8) (src : SkbSource) (ds : Nat) : Obs Unit := do
  let entry ← liftPrefix (liftWG (indexLookup [.keypair] (u32le msg 4)))
  let (keypair, peer) ← match entry with
    | none => pure (none, none)
    | some (IndexOwner.keypair kp, pid) => pure (some kp, some pid)
    | some (IndexOwner.handshake _, _) => liftPrefix (liftWG (invariant "a handshake entry under the keypair mask"))
  let kp ← match keypair with
    | none => do liftPrefix (liftWG keypairGetNull); pure none
    | some kp => liftPrefix (liftWG (keypairGet (some kp)))
  if ← liftPrefix (liftWG (branch .dataNoKeypair kp.isNone)) then
    liftPrefix (liftWG (peerPut peer))
    return
  let some id := kp | liftPrefix (liftWG (invariant "unreachable"))
  let some pid := peer | liftPrefix (liftWG (invariant "a keypair entry without a peer"))
  if ← liftPrefix (liftWG (branch .dataPeerDead (← liftPrefix (liftWG (getPeer pid))).isDead)) then
    liftPrefix (liftWG (keypairPut (some id) false))
    liftPrefix (liftWG (peerPut peer))
    return
  let skb ← liftPrefix (liftWG (newRxSkb {peer := pid, keypair := id, bytes := msg, source := src, ds}))
  let ret ← enqueue skb
  if ← liftPrefix (liftWG (branch .dataEpipe (ret == -EPIPE))) then enqueuePeer (pure ()) skb .dead
  if ← liftPrefix (liftWG (WG.orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE)))) then return
  liftPrefix (liftWG (keypairPut (some id) false))
  liftPrefix (liftWG (peerPut peer))
  liftPrefix (liftWG (freeRxSkb skb))

theorem consume_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesPrefix (consume msg src ds) (liftWG (consumeData msg src ds)) := by
  unfold consume consumeData
  simp only [liftWG_bind, pure_bind]
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro entry
  cases entry with
  | none =>
    simp only [liftWG_bind, liftWG_pure, apply_ite]
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    try simp only [liftWG_bind, liftWG_pure, pure_bind, Option.map_none, apply_ite]
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro noKey
    split
    · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _)
    · exact erasesPrefix_lift _
  | some e =>
    rcases e with ⟨owner, pid⟩
    cases owner with
    | handshake owner =>
      intro w h
      rfl
    | keypair key =>
      try simp only [liftWG_bind, liftWG_pure, apply_ite]
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro kp
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro noKey
      split
      · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _)
      · cases kp with
        | none => exact erasesPrefix_lift _
        | some id =>
          simp only [liftWG_bind, liftWG_pure, apply_ite]
          apply erasesPrefix_bind (erasesPrefix_lift _)
          intro p
          apply erasesPrefix_bind (erasesPrefix_lift _)
          intro dead
          split
          · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
              erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _))
          · apply erasesPrefix_bind (erasesPrefix_lift _)
            intro skb
            apply erasesPrefix_bind (enqueue_erases skb)
            intro ret
            apply erasesPrefix_bind (erasesPrefix_lift _)
            intro pipe
            have tail : ErasesPrefix (Event := Event)
                (do if ← liftPrefix (liftWG (WG.orM (branch .dataEnqueueOk (ret == 0))
                      (branch .dataEnqueueOkEpipe (ret == -EPIPE)))) then return
                    liftPrefix (liftWG (keypairPut (some id) false))
                    liftPrefix (liftWG (peerPut (some pid)))
                    liftPrefix (liftWG (freeRxSkb skb)))
                (do if ← liftWG (WG.orM (branch .dataEnqueueOk (ret == 0))
                      (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
                    liftWG (keypairPut (some id) false)
                    liftWG (peerPut (some pid))
                    liftWG (freeRxSkb skb)) := by
              apply erasesPrefix_bind (erasesPrefix_lift _)
              intro okay
              split
              · exact erasesPrefix_pure _
              · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
                  erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _))
            have hpeer : liftWG (enqueuePerPeerRx (pure ()) skb .dead) =
                enqueuePerPeerRx (pure ()) skb .dead := by
              unfold enqueuePerPeerRx
              simp only [monadLift_self, liftWG_bind, liftWG_pure, apply_ite]
              rfl
            split
            · rw [hpeer]
              exact erasesPrefix_bind (enqueuePeer_erases (erasesPrefix_pure ()) skb .dead) (fun _ => tail)
            · exact tail

theorem consume_preserves (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (consume msg src ds) := by
  have packets {α : Type} (a : SkbM α) : SameView nativeCell (liftSkb a) := by
    intro initial
    apply hoare_liftSkb
    intro g d packets hg hd
    simpa [nativeCell, hd] using hg
  have ambient {α : Type} (a : AmbientM α) : SameView nativeCell (StateT.lift a : WG.M α) := by
    intro initial
    exact hoare_liftAmbient a _
  have hor (x y : WG.M Bool) (hx : SameView nativeCell x) (hy : SameView nativeCell y) :
      SameView nativeCell (WG.orM x y) := by
    unfold WG.orM
    apply SameView.bind hx
    intro b
    split
    · exact SameView.pure _ _
    · exact hy
  unfold consume
  simp only [newRxSkb, freeRxSkb, branch, invariant]
  repeat' first
    | with_reducible exact enqueue_preserves _
    | with_reducible apply enqueuePeer_preserves
    | with_reducible exact lift_native_frame (indexLookup_frame _ _)
    | with_reducible exact lift_native_frame (keypairGet_frame _)
    | with_reducible exact lift_native_frame (keypairPut_frame _ _)
    | with_reducible exact lift_native_frame (peerPut_frame _)
    | with_reducible exact lift_native_frame (getPeer_frame _)
    | with_reducible exact lift_native_frame (packets _)
    | with_reducible exact lift_native_frame (kernel Lifetimes.keypairGetNull_sameStore)
    | with_reducible exact lift_native_frame (hor _ _ (ambient _) (ambient _))
    | with_reducible exact lift_native_frame (ambient _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.Queues.RxRing
