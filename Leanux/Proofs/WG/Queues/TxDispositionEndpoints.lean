import Leanux.Proofs.WG.Queues.TxDisposal
import Leanux.Proofs.WG.Queues.PrevQueue

/-! Source-derived normal EPIPE and ENOSPC endpoints. These local contracts do
not assert that a future arbitrary schedule preserves a DEAD mark or reaches a
worker. The source observer records the reached cuts separately on Stops. -/
set_option maxHeartbeats 1800000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.TxDisposition
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

theorem peerGet_packets (pid : PeerId) : SameView txPackets (peerGet pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer, getDev, setPeer, modifyDev,
    refcountInc, branch, branchCmp, branchCmpExcluded, invariant, unsupported, AmbientM.branch, AmbientM.branchCmp, AmbientM.branchCmpExcluded, AmbientM.invariant, AmbientM.unsupported]
  all_goals unfold txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all

theorem cpu_packets (pid : PeerId) : SameView txPackets (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [cpumaskChooseOnline, getPeer, getDev, setPeer, modifyDev, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜txPackets w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
  all_goals unfold txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals subst_vars
  all_goals try simp_all

theorem packets_kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => txPackets (project w)) a :=
  ha.of_factor (fun store : WGStoreView => fun id => store.dev.bind fun d => d.txSkbs[id]?)
    (fun w => txPackets (project w)) (fun _ => rfl)

def HeadState (first : SkbId) (state : PacketState) (w : WGWorld) : Prop :=
  ∃ p, txPackets w first = some p ∧ p.state = state

theorem publication_head (first : SkbId) (rest : List SkbId) (state : PacketState) :
    ⦃fun _ => ⌜True⌝⦄ enqueuePerPeerTx (first :: rest) state
    ⦃⇓? _ w => ⌜HeadState first state w⌝⦄ := by
  have hg := fun pid => (peerGet_packets pid).wp (fun _ => True)
  have ho := fun owner => indexOwner_peerDeref_preserves owner (fun _ => True)
  unfold Preserves Hoare at ho
  have hc := fun pid => (cpu_packets pid).wp (fun s => ∃ p, s first = some p ∧ p.state = state)
  have hp := fun pid => (peerPut_packets (some pid)).wp (fun s => ∃ p, s first = some p ∧ p.state = state)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (HeadState first state)
        (fun _ => HeadState first state) := hoare_liftAmbient a _
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) (fun _ => True) (fun _ _ => True) :=
    hoare_liftSkb a _ (fun _ _ _ _ _ => trivial)
  have written :
      Hoare (setTxSkb first (fun p => {p with state})) (fun _ => True)
        (fun _ => HeadState first state) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient u v ambient' _ hr
    cases u
    cases hd : w.dev with
    | none => simp [setTxSkb, liftSkb_run, hd] at hr
    | some d =>
      cases hp : d.txSkbs[first]? with
      | none =>
        simp [setTxSkb, liftSkb_run, SkbStore.setTx, SkbStore.getTx,
          hd, hp, invariant, AmbientM.invariant] at hr
        cases hr
      | some p =>
        rw [Packets.setTxSkb_run w ambient d first p _ hd hp] at hr
        cases hr
        exact ⟨{p with state}, by simp [txPackets, Packets.update, hd], rfl⟩
  have peek := fun pid => ambient (AmbientM.peekQueuedUnit .txWorker pid)
  have record := fun pid => ambient (AmbientM.recordQueued .txWorker pid)
  unfold Hoare at ambient skb written peek record
  unfold HeadState at ambient written peek record
  unfold HeadState
  rw [publication_factor]
  simp only [List.head?_cons]
  mvcgen [-Std.Do.Spec.monadLift_StateT, publicationMiddle, ho, hg, hc, hp, peek, record, written,
    getTxSkb, skb, getKeypair, getPeer, getDev, modifyDev, invariant, AmbientM.invariant,
    peekQueuedUnit, recordQueued]
  all_goals unfold txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Option.bind_map, Function.comp_def]

theorem enqueue_pipe (pid : PeerId) (item : List SkbId) (d : Device) (p : Peer)
    (hp : d.peers[pid]? = some p) (hq : p.txQueue.count < MAX_QUEUED_PACKETS)
    (hf : d.encryptQueue.full = true) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ enqueuePerDeviceAndPeer pid item
    ⦃⇓? ret w => ⌜ret = -WG.EPIPE ∧ txQueues w pid = some (p.txQueue.enqueue item) ∧
      TxRing.nativeCell w = some (d.ifindex, d.encryptQueue)⌝⦄ := by
  let P (w : WGWorld) := w.dev.map (fun x => (x.peers, x.ifindex, x.encryptQueue)) =
    some (d.peers, d.ifindex, d.encryptQueue)
  have skb {α : Type} (a : SkbM α) :
      Hoare (liftSkb a) P (fun _ => P) := by
    apply hoare_liftSkb
    intro w z store hi hz
    simpa [P, hz] using hi
  unfold Hoare at skb
  mvcgen [enqueuePerDeviceAndPeer, setTxSkb, skb, getPeer, getDev,
    modifyDev, setPeer, cpumaskNextOnlineFrom, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try unfold txQueues at *
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try simp_all [wgStoreView, PeerBorrow.resident, TxRing.nativeCell]
  all_goals subst_vars
  all_goals try simp_all []
  all_goals omega

/-- Full normal original createData endpoint for an entry ring refusal.
Publication can Stop before reaching this endpoint; no affiliation premise is used. -/
theorem create_pipe (pid : PeerId) (first : SkbId) (rest : List SkbId)
    (d : Device) (p : Peer) (hp : d.peers[pid]? = some p) (hl : p.isDead = false)
    (hq : p.txQueue.count < MAX_QUEUED_PACKETS) (hf : d.encryptQueue.full = true) :
    ⦃fun w => ⌜w.dev = some d⌝⦄ createData pid (first :: rest)
    ⦃⇓? _ w => ⌜txQueues w pid = some (p.txQueue.enqueue (first :: rest)) ∧
      HeadState first .dead w ∧ TxRing.nativeCell w = some (d.ifindex, d.encryptQueue)⌝⦄ := by
  have pub : ⦃fun w => ⌜txQueues w pid = some (p.txQueue.enqueue (first :: rest)) ∧
      TxRing.nativeCell w = some (d.ifindex, d.encryptQueue)⌝⦄ enqueuePerPeerTx (first :: rest) .dead
      ⦃⇓? _ w => ⌜txQueues w pid = some (p.txQueue.enqueue (first :: rest)) ∧
        HeadState first .dead w ∧ TxRing.nativeCell w = some (d.ifindex, d.encryptQueue)⌝⦄ := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient u v ambient' hb hr
    exact ⟨by rw [(Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp (publication_queues _ _) w ambient u v ambient' hr]; exact hb.1,
      (hoare_iff_run_ambient _ _ _).mp (publication_head first rest .dead) w ambient u v ambient' trivial hr,
      ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp (TxRing.enqueuePeer_frame _ _) w ambient u v ambient' hr).trans hb.2⟩
  rw [createSource_factor]
  have enq := enqueue_pipe pid (first :: rest) d p hp hq hf
  mvcgen [createTailSource, enq, pub, getPeer, getDev, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold txQueues HeadState txPackets TxRing.nativeCell at *
  all_goals simp_all [WG.EPIPE, PeerBorrow.resident]

theorem dispose_endpoint (pid : PeerId) (item : List SkbId) (key : KeypairId) (sent : List SentDatagram) :
    ⦃fun w => ⌜w.sent = sent⌝⦄ disposeSource pid item key
    ⦃⇓? result w => ⌜result = true ∧ (∀ id ∈ item, txPackets w id = none) ∧ w.sent = sent⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hs hr
  obtain ⟨ht, ha⟩ := (hoare_iff_run_ambient _ _ _).mp (dispose_packets pid item key) w ambient result v ambient' trivial hr
  exact ⟨ht, ha, ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp (dispose_no_send pid item key) w ambient result v ambient' hr).trans hs⟩

/-- The actual body re-reads a DEAD head before dropping and disposing its
whole item. Normal completion frees every item slot and emits no socket packet. -/
theorem dead_body_endpoint (pid : PeerId) (first : SkbId) (rest : List SkbId) (sent : List SentDatagram) :
    ⦃fun w => ⌜HeadState first .dead w ∧ w.sent = sent⌝⦄ bodySource pid (some (first :: rest))
    ⦃⇓? result w => ⌜result = true ∧ (∀ id ∈ first :: rest, txPackets w id = none) ∧ w.sent = sent⌝⦄ := by
  have hn : (PacketState.dead != PacketState.uncrypted) = true := rfl
  have hc : (PacketState.dead == PacketState.crypted) = false := rfl
  have read :
      Hoare (getTxSkb first) (fun w => HeadState first .dead w ∧ w.sent = sent)
        (fun p w => p.state = .dead ∧ HeadState first .dead w ∧ w.sent = sent) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient p v ambient' pre hr
    obtain ⟨rfl, _, d, hd, hp⟩ := Packets.getTxSkb_current first w v p ambient ambient' hr
    obtain ⟨old, hold, hs⟩ := pre.1
    have he : p = old := by simpa [txPackets, hd, hp] using hold
    subst old
    exact ⟨hs, pre⟩
  unfold Hoare at read
  simp only [bodySource, WG.andM, List.head?_cons]
  mvcgen [dispose_endpoint, read, getPeer, getDev,
    setPeer, modifyDev, branch, invariant, AmbientM.branch, AmbientM.invariant]
  all_goals unfold HeadState txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals subst_vars
  all_goals try simp_all

/-- A normal peek returns the actual logical queue head and preserves the
WG store; malformed tails retain their original Stop instead of gaining totality. -/
theorem peek_head_wp (q : PrevQueue (List SkbId)) (item : List SkbId)
    (hh : q.all.head? = some item) (initial : WGStoreView) :
    ⦃fun w => ⌜(wgStoreView w) = initial⌝⦄ q.peek
    ⦃⇓? out w => ⌜out.1 = some item ∧ (wgStoreView w) = initial⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  rintro w ambient ⟨out, queue⟩ v ambient' hk hr
  have he := prev_peek_normal q w v ambient ambient' out queue hr
  exact ⟨he.1.trans hh, (congrArg wgStoreView he.2.2.2).trans hk⟩

/-- Disposal linkage at the real txStep entry. This does not transport a
previous EPIPE mark through arbitrary intervening actions or prove scheduling. -/
theorem dead_step_endpoint (pid : PeerId) (first : SkbId) (rest : List SkbId) (sent : List SentDatagram) :
    ⦃fun w => ⌜(∃ p, PeerBorrow.resident (wgStoreView w) pid = some p ∧
      p.txQueue.all.head? = some (first :: rest)) ∧ HeadState first .dead w ∧ w.sent = sent⌝⦄ txStep pid
    ⦃⇓? result w => ⌜result = true ∧ (∀ id ∈ first :: rest, txPackets w id = none) ∧ w.sent = sent⌝⦄ := by
  rw [← stepSource_eq]
  have pk (q : PrevQueue (List SkbId)) :
      ⦃fun w => ⌜q.all.head? = some (first :: rest) ∧ HeadState first .dead w ∧ w.sent = sent⌝⦄ q.peek
      ⦃⇓? out w => ⌜out.1 = some (first :: rest) ∧ HeadState first .dead w ∧ w.sent = sent⌝⦄ := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    rintro w ambient ⟨out, queue⟩ v ambient' ⟨hh, hd, hs⟩ hr
    have he := prev_peek_normal q w v ambient ambient' out queue hr
    exact ⟨he.1.trans hh, he.2.2.2 ▸ hd, he.2.2.2 ▸ hs⟩
  have body (out : Option (List SkbId)) :
      ⦃fun w => ⌜out = some (first :: rest) ∧ HeadState first .dead w ∧ w.sent = sent⌝⦄ bodySource pid out
      ⦃⇓? result w => ⌜result = true ∧ (∀ id ∈ first :: rest, txPackets w id = none) ∧ w.sent = sent⌝⦄ := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient result v ambient' hb hr
    rcases hb with ⟨rfl, hb⟩
    exact (hoare_iff_run_ambient _ _ _).mp (dead_body_endpoint pid first rest sent) w ambient result v ambient' hb hr
  mvcgen [stepSource, pk, body, getPeer, getDev,
    setPeer, modifyDev, invariant]
  all_goals unfold HeadState txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [wgStoreView, PeerBorrow.resident]
  all_goals subst_vars
  all_goals try simp_all

end Leanux.Proofs.WG.Queues.TxDisposition
