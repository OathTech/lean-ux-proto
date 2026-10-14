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
  mvcgen [peerGet, requireNotPending, getPeer, getDev, getK, setPeer, modifyDev, modifyK,
    refcountInc, branch, branchCmp, branchCmpExcluded, invariant, unsupported]
  all_goals unfold txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all

theorem cpu_packets (pid : PeerId) : SameView txPackets (cpumaskChooseOnline pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [cpumaskChooseOnline, getPeer, getDev, getK, setPeer, modifyDev, modifyK, branch, invariant]
  all_goals try exact ((⇓? _ w => ⌜txPackets w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals unfold txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals subst_vars
  all_goals try simp_all

theorem packets_kernel (ha : SameKernel a) : SameView txPackets a := by
  intro w x v hr
  unfold txPackets
  rw [ha w x v hr]

def HeadState (first : SkbId) (state : PacketState) (w : World) : Prop :=
  ∃ p, txPackets w first = some p ∧ p.state = state

theorem publication_head (first : SkbId) (rest : List SkbId) (state : PacketState) :
    ⦃fun _ => ⌜True⌝⦄ enqueuePerPeerTx (first :: rest) state
    ⦃⇓? _ w => ⌜HeadState first state w⌝⦄ := by
  have hg := fun pid => (peerGet_packets pid).wp (fun _ => True)
  have hc := fun pid => (cpu_packets pid).wp (fun s => ∃ p, s first = some p ∧ p.state = state)
  have hp := fun pid => (peerPut_packets (some pid)).wp (fun s => ∃ p, s first = some p ∧ p.state = state)
  have hpeek := fun pid => (packets_kernel (peekQueuedUnit_sameKernel .txWorker pid)).wp
    (fun s => ∃ p, s first = some p ∧ p.state = state)
  have hrec := fun pid => (packets_kernel (Lifetimes.recordQueued_sameKernel .txWorker pid)).wp
    (fun s => ∃ p, s first = some p ∧ p.state = state)
  unfold HeadState
  rw [publication_factor]
  mvcgen [publicationMiddle, hg, hc, hp, hpeek, hrec, getTxSkb, getKeypair,
    getPeer, getDev, getK, setTxSkb, modifyDev, modifyK, invariant]
  all_goals unfold txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [Option.bind_map, Function.comp_def]

theorem enqueue_pipe (pid : PeerId) (item : List SkbId) (d : Device) (p : Peer)
    (hp : d.peers[pid]? = some p) (hq : p.txQueue.count < MAX_QUEUED_PACKETS)
    (hf : d.encryptQueue.full = true) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ enqueuePerDeviceAndPeer pid item
    ⦃⇓? ret w => ⌜ret = -WG.EPIPE ∧ txQueues w pid = some (p.txQueue.enqueue item) ∧
      TxRing.cell w = some (d.ifindex, d.encryptQueue)⌝⦄ := by
  mvcgen [enqueuePerDeviceAndPeer, setTxSkb, getTxSkb, getPeer, getDev, getK,
    modifyDev, modifyK, setPeer, cpumaskNextOnlineFrom, branch, invariant]
  all_goals unfold txQueues at *
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [PeerBorrow.resident, TxRing.cell]
  all_goals subst_vars
  all_goals simp_all [PeerBorrow.resident, TxRing.cell]
  all_goals omega

/-- Full normal original createData endpoint for an entry ring refusal.
Publication can Stop before reaching this endpoint; no affiliation premise is used. -/
theorem create_pipe (pid : PeerId) (first : SkbId) (rest : List SkbId)
    (d : Device) (p : Peer) (hp : d.peers[pid]? = some p) (hl : p.isDead = false)
    (hq : p.txQueue.count < MAX_QUEUED_PACKETS) (hf : d.encryptQueue.full = true) :
    ⦃fun w => ⌜w.k.wg = some d⌝⦄ createData pid (first :: rest)
    ⦃⇓? _ w => ⌜txQueues w pid = some (p.txQueue.enqueue (first :: rest)) ∧
      HeadState first .dead w ∧ TxRing.cell w = some (d.ifindex, d.encryptQueue)⌝⦄ := by
  have pub : ⦃fun w => ⌜txQueues w pid = some (p.txQueue.enqueue (first :: rest)) ∧
      TxRing.cell w = some (d.ifindex, d.encryptQueue)⌝⦄ enqueuePerPeerTx (first :: rest) .dead
      ⦃⇓? _ w => ⌜txQueues w pid = some (p.txQueue.enqueue (first :: rest)) ∧
        HeadState first .dead w ∧ TxRing.cell w = some (d.ifindex, d.encryptQueue)⌝⦄ := by
    apply (hoare_iff_triple _ _ _).mp
    intro w u v hb hr
    exact ⟨by rw [publication_queues _ _ w u v hr]; exact hb.1,
      (hoare_iff_triple _ _ _).mpr (publication_head first rest .dead) w u v trivial hr,
      (TxRing.enqueuePeer_frame _ _ w u v hr).trans hb.2⟩
  rw [createSource_factor]
  have enq := enqueue_pipe pid (first :: rest) d p hp hq hf
  mvcgen [createTailSource, enq, pub, getPeer, getDev, getK, branch, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold txQueues HeadState txPackets TxRing.cell at *
  all_goals simp_all [WG.EPIPE, EPIPE, PeerBorrow.resident]

theorem dispose_endpoint (pid : PeerId) (item : List SkbId) (key : KeypairId) (sent : List SentDatagram) :
    ⦃fun w => ⌜w.sent = sent⌝⦄ disposeSource pid item key
    ⦃⇓? result w => ⌜result = true ∧ (∀ id ∈ item, txPackets w id = none) ∧ w.sent = sent⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w result v hs hr
  obtain ⟨ht, ha⟩ := (hoare_iff_triple _ _ _).mpr (dispose_packets pid item key) w result v trivial hr
  exact ⟨ht, ha, (dispose_no_send pid item key w result v hr).trans hs⟩

/-- The actual body re-reads a DEAD head before dropping and disposing its
whole item. Normal completion frees every item slot and emits no socket packet. -/
theorem dead_body_endpoint (pid : PeerId) (first : SkbId) (rest : List SkbId) (sent : List SentDatagram) :
    ⦃fun w => ⌜HeadState first .dead w ∧ w.sent = sent⌝⦄ bodySource pid (some (first :: rest))
    ⦃⇓? result w => ⌜result = true ∧ (∀ id ∈ first :: rest, txPackets w id = none) ∧ w.sent = sent⌝⦄ := by
  have hn : (PacketState.dead != PacketState.uncrypted) = true := rfl
  have hc : (PacketState.dead == PacketState.crypted) = false := rfl
  mvcgen [bodySource, WG.andM, dispose_endpoint, getTxSkb, getPeer, getDev,
    getK, setPeer, modifyDev, modifyK, branch, invariant]
  all_goals unfold HeadState txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all
  all_goals subst_vars
  all_goals try simp_all

/-- A normal peek returns the actual logical queue head and preserves the
Kernel; malformed tails retain their original Stop instead of gaining totality. -/
theorem peek_head_wp (q : PrevQueue (List SkbId)) (item : List SkbId)
    (hh : q.all.head? = some item) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ q.peek
    ⦃⇓? out w => ⌜out.1 = some item ∧ w.k = initial⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  rintro w ⟨out, queue⟩ v hk hr
  have he := prev_peek_normal q w v out queue hr
  exact ⟨he.1.trans hh, he.2.2.2.trans hk⟩

/-- Disposal linkage at the real txStep entry. This does not transport a
previous EPIPE mark through arbitrary intervening actions or prove scheduling. -/
theorem dead_step_endpoint (pid : PeerId) (first : SkbId) (rest : List SkbId) (sent : List SentDatagram) :
    ⦃fun w => ⌜(∃ p, PeerBorrow.resident w.k pid = some p ∧
      p.txQueue.all.head? = some (first :: rest)) ∧ HeadState first .dead w ∧ w.sent = sent⌝⦄ txStep pid
    ⦃⇓? result w => ⌜result = true ∧ (∀ id ∈ first :: rest, txPackets w id = none) ∧ w.sent = sent⌝⦄ := by
  rw [← stepSource_eq]
  have pk (q : PrevQueue (List SkbId)) :
      ⦃fun w => ⌜q.all.head? = some (first :: rest) ∧ HeadState first .dead w ∧ w.sent = sent⌝⦄ q.peek
      ⦃⇓? out w => ⌜out.1 = some (first :: rest) ∧ HeadState first .dead w ∧ w.sent = sent⌝⦄ := by
    apply (hoare_iff_triple _ _ _).mp
    rintro w ⟨out, queue⟩ v ⟨hh, hd, hs⟩ hr
    have he := prev_peek_normal q w v out queue hr
    have sentFrame : SameView (fun w => w.sent) q.peek := by
      apply SameView.of_wp
      intro s
      mvcgen [PrevQueue.peek, PrevQueue.dequeue, branch, invariant, unsupported]
    exact ⟨he.1.trans hh, by simpa only [HeadState, txPackets, he.2.2.2] using hd,
      (sentFrame w (out, queue) v hr).trans hs⟩
  have body (out : Option (List SkbId)) :
      ⦃fun w => ⌜out = some (first :: rest) ∧ HeadState first .dead w ∧ w.sent = sent⌝⦄ bodySource pid out
      ⦃⇓? result w => ⌜result = true ∧ (∀ id ∈ first :: rest, txPackets w id = none) ∧ w.sent = sent⌝⦄ := by
    apply (hoare_iff_triple _ _ _).mp
    intro w result v hb hr
    rcases hb with ⟨rfl, hb⟩
    exact (hoare_iff_triple _ _ _).mpr (dead_body_endpoint pid first rest sent) w result v hb hr
  mvcgen [stepSource, pk, body, getPeer, getDev, getK,
    setPeer, modifyDev, modifyK, invariant]
  all_goals unfold HeadState txPackets at *
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [PeerBorrow.resident, Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals try simp_all

end Leanux.Proofs.WG.Queues.TxDisposition
