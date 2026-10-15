import Leanux.Proofs.WG.Queues.RxRingCuts

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

def enqueue (id : SkbId) : Obs Int := Ring.Source.enqueue (enqueuePerDeviceAndPeerRx id) id

theorem enqueue_erases (id : SkbId) : ErasesPrefix (enqueue id) (enqueuePerDeviceAndPeerRx id) :=
  Ring.Source.enqueue_erases _ _

theorem enqueue_preserves (id : SkbId) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (enqueue id) :=
  Ring.Source.enqueue_preserves _ id
    (fun w ret v hr => enqueue_result id w v ret hr)
    (fun _ _ _ hc hr => enqueue_free id hc hr)

def poll : Obs (Option SkbId) := Ring.Source.poll pollSource

theorem poll_erases : ErasesPrefix poll pollSource := Ring.Source.poll_erases _

theorem poll_preserves : PrefixPreserves (Inv deviceIndex initial) (Safe initial) poll :=
  Ring.Source.poll_preserves _ (fun _ _ _ _ hc hr => poll_result hc hr)

def enqueuePeer (irq : Obs Unit) (id : SkbId) (state : PacketState) : Obs Unit := do
  let pid ← liftPrefix (IndexOwner.peerDeref (.keypair (← liftPrefix (getRxSkb id)).keypair))
  liftPrefix (peerGet pid)
  let p ← liftPrefix (getPeer pid)
  if !(p.rxQueue.all.contains id) then liftPrefix (invariant "a decrypted packet that is not on its peer's rx_queue")
  liftPrefix (setRxSkb id fun q => {q with state})
  liftPrefix (setPeer pid {p with napiScheduled := true})
  irq
  liftPrefix (peerPut (some pid))

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

theorem invariant_frame (why : String) : SameView cell (invariant (α := α) why) := by
  intro w x v hr
  cases hr

theorem enqueuePeer_preserves (hi : PrefixPreserves (Inv deviceIndex initial) (Safe initial) irq)
    (id : SkbId) (state : PacketState) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (enqueuePeer irq id state) := by
  unfold enqueuePeer
  repeat' first
    | with_reducible exact hi
    | with_reducible exact lift_frame (getRx_frame _)
    | with_reducible exact lift_frame (kernel (indexOwner_peerDeref_sameKernel _))
    | with_reducible exact lift_frame (getKeypair_frame _)
    | with_reducible exact lift_frame (getPeer_frame _)
    | with_reducible exact lift_frame (peerGet_frame _)
    | with_reducible exact lift_frame (setRx_frame _ _)
    | with_reducible exact lift_frame (setPeer_frame _ _)
    | with_reducible exact lift_frame (peerPut_frame _)
    | with_reducible exact lift_frame (invariant_frame _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

def consume (msg : List UInt8) (src : SkbSource) (ds : Nat) : Obs Unit := do
  let entry ← liftPrefix (indexLookup [.keypair] (u32le msg 4))
  let (keypair, peer) ← match entry with
    | none => pure (none, none)
    | some (IndexOwner.keypair kp, pid) => pure (some kp, some pid)
    | some (IndexOwner.handshake _, _) => liftPrefix (invariant "a handshake entry under the keypair mask")
  let kp ← match keypair with
    | none => do liftPrefix keypairGetCurrent; pure none
    | some kp => liftPrefix (keypairGet (some kp))
  if ← liftPrefix (branch .dataNoKeypair kp.isNone) then
    liftPrefix (peerPut peer)
    return
  let some id := kp | liftPrefix (invariant "unreachable")
  let some pid := peer | liftPrefix (invariant "a keypair entry without a peer")
  if ← liftPrefix (branch .dataPeerDead (← liftPrefix (getPeer pid)).isDead) then
    liftPrefix (keypairPut (some id) false)
    liftPrefix (peerPut peer)
    return
  let skb ← liftPrefix (newRxSkb {peer := pid, keypair := id, bytes := msg, source := src, ds})
  let ret ← enqueue skb
  if ← liftPrefix (branch .dataEpipe (ret == -EPIPE)) then enqueuePeer (pure ()) skb .dead
  if ← liftPrefix (WG.orM (branch .dataEnqueueOk (ret == 0)) (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
  liftPrefix (keypairPut (some id) false)
  liftPrefix (peerPut peer)
  liftPrefix (freeRxSkb skb)

theorem consume_erases (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    ErasesPrefix (consume msg src ds) (consumeData msg src ds) := by
  unfold consume consumeData
  simp only [pure_bind]
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro entry
  cases entry with
  | none =>
    apply erasesPrefix_bind (erasesPrefix_lift _)
    intro _
    try simp only [pure_bind, Option.map_none]
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
      simp [runPrefix_bind, runPrefix_lift, invariant, StateT.run_bind]
    | keypair key =>
      try simp only [pure_bind]
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro kp
      apply erasesPrefix_bind (erasesPrefix_lift _)
      intro noKey
      split
      · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_pure _)
      · cases kp with
        | none => exact erasesPrefix_lift _
        | some id =>
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
                (do if ← liftPrefix (WG.orM (branch .dataEnqueueOk (ret == 0))
                      (branch .dataEnqueueOkEpipe (ret == -EPIPE))) then return
                    liftPrefix (keypairPut (some id) false)
                    liftPrefix (peerPut (some pid))
                    liftPrefix (freeRxSkb skb))
                (do if ← WG.orM (branch .dataEnqueueOk (ret == 0))
                      (branch .dataEnqueueOkEpipe (ret == -EPIPE)) then return
                    keypairPut (some id) false
                    peerPut (some pid)
                    freeRxSkb skb) := by
              apply erasesPrefix_bind (erasesPrefix_lift _)
              intro okay
              split
              · exact erasesPrefix_pure _
              · exact erasesPrefix_bind (erasesPrefix_lift _) (fun _ =>
                  erasesPrefix_bind (erasesPrefix_lift _) (fun _ => erasesPrefix_lift _))
            split
            · exact erasesPrefix_bind (enqueuePeer_erases (erasesPrefix_pure ()) skb .dead) (fun _ => tail)
            · exact tail

theorem consume_preserves (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    PrefixPreserves (Inv deviceIndex initial) (Safe initial) (consume msg src ds) := by
  unfold consume
  repeat' first
    | with_reducible exact enqueue_preserves _
    | with_reducible apply enqueuePeer_preserves
    | with_reducible exact lift_frame (indexLookup_frame _ _)
    | with_reducible exact lift_frame (keypairGet_frame _)
    | with_reducible exact lift_frame (keypairPut_frame _ _)
    | with_reducible exact lift_frame (peerPut_frame _)
    | with_reducible exact lift_frame (getPeer_frame _)
    | with_reducible exact lift_frame (newRx_frame _)
    | with_reducible exact lift_frame (freeRx_frame _)
    | with_reducible exact lift_frame (kernel Lifetimes.keypairGetCurrent_sameKernel)
    | with_reducible exact lift_frame (kernel (Lifetimes.orM_sameKernel (sameKernel_branch _ _) (sameKernel_branch _ _)))
    | with_reducible exact lift_frame (kernel (sameKernel_branch _ _))
    | with_reducible exact lift_frame (invariant_frame _)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

end Leanux.Proofs.WG.Queues.RxRing
