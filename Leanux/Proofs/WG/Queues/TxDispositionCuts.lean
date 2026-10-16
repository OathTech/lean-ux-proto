import Leanux.Proofs.WG.Queues.TxDispositionBorrow
import Leanux.Proofs.WG.Queues.TxDispositionProjection

/-! Exact disposition continuations of the original source. These cuts do
not assume the original queue pid equals the keypair-derived publication pid.
An entered completion is not a successful send; a ring refusal is not a free. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Std.Do

def cleanup (pid : PeerId) (item : List SkbId) (first : SkbId) : Obs Unit := do
  nativeAccess (keypairPutPrefix (some (← nativeAccess (getTxSkbPrefix first)).keypair) false)
  nativeAccess (peerPutMixed (some pid))
  for id in item do nativeAccess (freeTxSkbPrefix id)

def createTail (pid : PeerId) (item : List SkbId) (first : SkbId) (ret : Int) : Obs Unit := do
  if ← liftPrefix (branch .createDataOk (ret == 0)) then return
  if ← liftPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
  cleanup pid item first

theorem create_factor (pid : PeerId) (item : List SkbId) : create pid item = (do
    let some first := item.head? | liftPrefix (invariant "an empty ring item")
    let ret ← do
      if ← liftPrefix (branch .createDataDead (← nativeAccess (getPeerMixed pid)).isDead) then pure (-EINVAL)
      else
        let ret ← enqueue pid item
        if ← liftPrefix (branch .createDataEpipe (ret == -WG.EPIPE)) then publish item .dead
        pure ret
    createTail pid item first ret) := rfl

/-- EPIPE returns after its two original decisions; no cleanup is entered. -/
theorem epipe_tail (pid : PeerId) (item : List SkbId) (first : SkbId) :
    createTail pid item first (-WG.EPIPE) = (do
      _ ← liftPrefix (branch .createDataOk false)
      _ ← liftPrefix (branch .createDataOkEpipe true)
      pure ()) := by
  funext w
  rfl

/-- ENOSPC reaches cleanup only after its two original false decisions.
Cleanup may Stop at its first getter or later release. -/
theorem enospc_tail (pid : PeerId) (item : List SkbId) (first : SkbId) :
    createTail pid item first (-WG.ENOSPC) = (do
      _ ← liftPrefix (branch .createDataOk false)
      _ ← liftPrefix (branch .createDataOkEpipe false)
      cleanup pid item first) := by
  funext w
  rfl

def afterHead (pid : PeerId) (item : List SkbId) (head : DataPacket) : Obs Bool := do
  drop pid item
  if ← liftPrefix (branch .txCrypted (head.state == .crypted)) then complete pid item
  dispose pid item head.keypair

theorem body_factor (pid : PeerId) (first : SkbId) (rest : List SkbId) :
    body pid (some (first :: rest)) = (do
      let go ← andObs (liftPrefix (branch .txPacket true)) do
        liftPrefix (branch .txNotUncrypted ((← nativeAccess (getTxSkbPrefix first)).state != .uncrypted))
      if !go then return false
      let head ← nativeAccess (getTxSkbPrefix first)
      afterHead pid (first :: rest) head) := rfl

/-- The DEAD reached tail drops the queue item and enters disposal, skipping
createDataDone entirely; the original false decision remains in Ambient.steps. -/
theorem dead_afterHead (pid : PeerId) (item : List SkbId) (head : DataPacket)
    (hd : head.state = .dead) : afterHead pid item head = (do
      drop pid item
      _ ← liftPrefix (branch .txCrypted false)
      dispose pid item head.keypair) := by
  unfold afterHead
  rw [hd]
  funext w
  rfl

def completionEvent : Event → Option (PeerId × List SkbId)
  | .completion pid item => some (pid, item)
  | _ => none

theorem dispose_no_completion (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    HistoryFrame completionEvent (dispose pid item key) := by
  unfold dispose nativeAccess
  repeat' first
    | with_reducible exact access_history _ (fun _ => rfl) _
    | with_reducible exact HistoryFrame.pure _ _
    | with_reducible apply HistoryFrame.bind
    | with_reducible apply HistoryFrame.forIn
    | (with_reducible intro x; try dsimp only)

theorem dead_no_completion (pid : PeerId) (item : List SkbId) (head : DataPacket)
    (hd : head.state = .dead) : HistoryFrame completionEvent (afterHead pid item head) := by
  rw [dead_afterHead pid item head hd]
  unfold drop nativeAccess
  repeat' first
    | with_reducible exact dispose_no_completion _ _ _
    | with_reducible exact access_history _ (fun _ => rfl) _
    | with_reducible exact HistoryFrame.lift _ _
    | with_reducible exact HistoryFrame.emit _ rfl
    | with_reducible apply HistoryFrame.bind
    | (with_reducible intro x; try dsimp only)

/-- Exact reached free observation, including the original release marker.
Later composition retains this prefix even if the next free or put Stops. -/
theorem free_run (id : SkbId) (w : World) (h : List Event) :
    runPrefix (nativeAccess (freeTxSkbPrefix id)) w h =
      match (liftWG (getTxSkb id)).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((liftWG (freeTxSkb id)).run w,
          h ++ [.access (.packet (.read (.inl id) (packetStamp w.wg id))),
                .access (.packet (.release (.inl id) (packetStamp w.wg id)))]) := by
  unfold nativeAccess access
  cases hr : ((getTxSkb id).run w.wg).run w.ambient with
  | error e =>
    simp only [liftWG_run, hr, Except.map]
    simpa only [List.map_nil, List.append_nil] using
      focusPrefix_suffix Event.access accessEvent (liftWGObserver (freeTxSkbPrefix id)) w h (.error e) []
        (by simp only [liftWGObserver_run, runWGPrefix, freeTxSkbPrefix_run, hr,
          Except.map, List.append_nil])
  | ok out =>
    simp only [liftWG_run, hr, Except.map]
    refine focusPrefix_suffix Event.access accessEvent (liftWGObserver (freeTxSkbPrefix id)) w h
      ((((freeTxSkb id).run w.wg).run w.ambient).map
        (fun ((x, wg), ambient) => (x, {w with wg, ambient})))
      [.packet (.read (.inl id) (packetStamp w.wg id)),
       .packet (.release (.inl id) (packetStamp w.wg id))] ?_
    rw [liftWGObserver_run]
    change ((runStatePrefix (freeTxSkbPrefix id) w.wg w.ambient _).1.map _,
      (runStatePrefix (freeTxSkbPrefix id) w.wg w.ambient _).2) = _
    simp only [freeTxSkbPrefix_run, hr]

/-- The disposal path performs no socket output. The frame is only about a
normal returned WGWorld; its failed release prefix is specified separately. -/
theorem dispose_no_send (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    Framing.SameView (fun w : WGWorld => w.sent) (disposeSource pid item key) := by
  apply Framing.SameView.of_wp
  intro sent
  have index_spec (α : Type) (a : IndexM α) :
      ⦃fun w : WGWorld => ⌜w.sent = sent⌝⦄ (MonadLift.monadLift a : WG.M α)
      ⦃⇓? _ w => ⌜w.sent = sent⌝⦄ := by
    apply hoare_liftIndex a (fun w => w.sent = sent)
    intro g d table hg _
    exact hg
  have skb_spec (α : Type) (a : SkbM α) :
      ⦃fun w : WGWorld => ⌜w.sent = sent⌝⦄ liftSkb a
      ⦃⇓? _ w => ⌜w.sent = sent⌝⦄ := by
    apply hoare_liftSkb a (fun w : WGWorld => w.sent = sent)
    intro g d packets hg _
    exact hg
  have kp : ⦃fun w : WGWorld => ⌜w.sent = sent⌝⦄ keypairPut (some key) false
      ⦃⇓? _ w => ⌜w.sent = sent⌝⦄ := by
    have hd := fun o => indexOwner_peerDeref_preserves o (fun w : WGWorld => w.sent = sent)
    unfold Preserves Hoare at hd
    mvcgen [index_spec, hd, keypairPut, getKeypair, getDev,
      setKeypair, modifyDev, refcountDecAndTest, branch, branchCmp,
      AmbientM.branch, AmbientM.branchCmp, invariant, unsupported,
      AmbientM.invariant, AmbientM.unsupported]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  have pp : ⦃fun w : WGWorld => ⌜w.sent = sent⌝⦄ peerPut (some pid)
      ⦃⇓? _ w => ⌜w.sent = sent⌝⦄ := by
    mvcgen [index_spec, peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev,
      retirePeerUnits, modifyAmbient, refcountDecAndTest, branch, branchCmp,
      AmbientM.branch, AmbientM.branchCmp, invariant, unsupported,
      AmbientM.invariant, AmbientM.unsupported]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all
  mvcgen [disposeSource, freeTxSkb, skb_spec, kp, pp]
  all_goals try exact ((⇓? _ w => ⌜w.sent = sent⌝) :
    Std.Do.PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals simp_all

end Leanux.Proofs.WG.Queues.TxDisposition
