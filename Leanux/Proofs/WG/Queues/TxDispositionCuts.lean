import Leanux.Proofs.WG.Queues.TxDispositionBorrow

/-! Exact disposition continuations of the original source. These cuts do
not assume the original queue pid equals the keypair-derived publication pid.
An entered completion is not a successful send; a ring refusal is not a free. -/
set_option maxHeartbeats 1000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Std.Do

def cleanup (pid : PeerId) (item : List SkbId) (first : SkbId) : Obs Unit := do
  access (keypairPutPrefix (some (← access (getTxSkbPrefix first)).keypair) false)
  access (peerPutMixed (some pid))
  for id in item do access (freeTxSkbPrefix id)

def createTail (pid : PeerId) (item : List SkbId) (first : SkbId) (ret : Int) : Obs Unit := do
  if ← liftPrefix (branch .createDataOk (ret == 0)) then return
  if ← liftPrefix (branch .createDataOkEpipe (ret == -WG.EPIPE)) then return
  cleanup pid item first

theorem create_factor (pid : PeerId) (item : List SkbId) : create pid item = (do
    let some first := item.head? | liftPrefix (invariant "an empty ring item")
    let ret ← do
      if ← liftPrefix (branch .createDataDead (← access (getPeerMixed pid)).isDead) then pure (-EINVAL)
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
        liftPrefix (branch .txNotUncrypted ((← access (getTxSkbPrefix first)).state != .uncrypted))
      if !go then return false
      let head ← access (getTxSkbPrefix first)
      afterHead pid (first :: rest) head) := rfl

/-- The DEAD reached tail drops the queue item and enters disposal, skipping
createDataDone entirely; the original false decision remains in World.steps. -/
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
  unfold dispose
  repeat' first
    | with_reducible exact access_history _ (fun _ => rfl) _
    | with_reducible exact HistoryFrame.pure _ _
    | with_reducible apply HistoryFrame.bind
    | with_reducible apply HistoryFrame.forIn
    | (with_reducible intro x; try dsimp only)

theorem dead_no_completion (pid : PeerId) (item : List SkbId) (head : DataPacket)
    (hd : head.state = .dead) : HistoryFrame completionEvent (afterHead pid item head) := by
  rw [dead_afterHead pid item head hd]
  unfold drop
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
    runPrefix (access (freeTxSkbPrefix id)) w h =
      match (getTxSkb id).run w with
      | .error e => (.error e, h)
      | .ok (_, _) => ((freeTxSkb id).run w,
          h ++ [.access (.packet (.read (.inl id) (packetStamp w id))),
                .access (.packet (.release (.inl id) (packetStamp w id)))]) := by
  unfold access
  cases hr : (getTxSkb id).run w with
  | error e =>
    simpa only [List.map_nil, List.append_nil] using
      focusPrefix_suffix Event.access accessEvent (freeTxSkbPrefix id) w h (.error e) []
        (by simp only [freeTxSkbPrefix_run, hr, List.append_nil])
  | ok out =>
    exact focusPrefix_suffix _ _ _ _ _ _ _ (by rw [freeTxSkbPrefix_run, hr])

/-- The disposal path performs no socket output. The frame is only about a
normal returned World; its failed release prefix is specified separately. -/
theorem dispose_no_send (pid : PeerId) (item : List SkbId) (key : KeypairId) :
    Framing.SameView (fun w => w.sent) (disposeSource pid item key) := by
  apply Framing.SameView.of_wp
  intro sent
  have free (id : SkbId) : ⦃fun w => ⌜w.sent = sent⌝⦄ freeTxSkb id
      ⦃⇓? _ w => ⌜w.sent = sent⌝⦄ := by
    mvcgen [freeTxSkb, getTxSkb, getDev, getK, modifyDev, modifyK, invariant]
  have kp : ⦃fun w => ⌜w.sent = sent⌝⦄ keypairPut (some key) false
      ⦃⇓? _ w => ⌜w.sent = sent⌝⦄ := by
    simp only [keypairPut, Framing.indexRemoveKeypair_eq]
    mvcgen [Framing.indexUnhash, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
      refcountDecAndTest, branch, branchCmp, invariant, unsupported]
  have pp : ⦃fun w => ⌜w.sent = sent⌝⦄ peerPut (some pid)
      ⦃⇓? _ w => ⌜w.sent = sent⌝⦄ := by
    simp only [peerPut, Framing.indexRemove_eq]
    mvcgen [requireNotPending, Framing.indexUnhash, getPeer, getDev, getK, setPeer,
      modifyDev, modifyK, retirePeerUnits, refcountDecAndTest, branch, branchCmp,
      invariant, unsupported]
  mvcgen [disposeSource, free, kp, pp]
  all_goals try exact ((⇓? _ w => ⌜w.sent = sent⌝) : Std.Do.PostCond _ (.arg World (.except Stop .pure)))
  all_goals simp_all

end Leanux.Proofs.WG.Queues.TxDisposition
