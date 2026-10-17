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
  intro initial
  let P := fun w : WGWorld => txPackets w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have write (f : Device → Device) (hf : ∀ d, (f d).txSkbs = d.txSkbs) :
      Preserves P (modifyDev f) := by
    unfold modifyDev
    apply hoare_modify
    intro w h
    change txPackets _ = initial
    funext id
    have point := congrFun h id
    simpa [txPackets, Option.bind_map, Function.comp_def, hf] using point
  change Preserves P (peerGet pid)
  unfold peerGet getPeer getDev setPeer
  simp only [branch, branchCmp, refcountInc, invariant, unsupported, requireNotPending]
  repeat' first
    | (allocation_release_head modifyDev; apply write; intro; rfl)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step
  all_goals exact read

theorem cpu_packets (pid : PeerId) : SameView txPackets (cpumaskChooseOnline pid) := by
  intro initial
  let P := fun w : WGWorld => txPackets w = initial
  have ambient {α : Type} (a : AmbientM α) :
      Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have read : Preserves P (get : WG.M WGWorld) :=
    hoare_consequence (hoare_get P) (fun _ h => h) (fun _ _ h => h.2)
  have write (f : Device → Device) (hf : ∀ d, (f d).txSkbs = d.txSkbs) :
      Preserves P (modifyDev f) := by
    unfold modifyDev
    apply hoare_modify
    intro w h
    change txPackets _ = initial
    funext id
    have point := congrFun h id
    simpa [txPackets, Option.bind_map, Function.comp_def, hf] using point
  change Preserves P (cpumaskChooseOnline pid)
  unfold cpumaskChooseOnline getPeer getDev setPeer
  simp only [branch, invariant]
  repeat' first
    | (allocation_release_head modifyDev; apply write; intro; rfl)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | (allocation_release_head ForIn.forIn
       simp only [Nat.mod_one, Std.Legacy.Range.forIn_eq_forIn_range']
       exact preserves_pure _)
    | allocation_release_step
  all_goals exact read

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
  have getter (pid : PeerId) (P : WGWorld → Prop) : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v a' hi hr
    rw [(Peers.getPeer_current pid w v p a a' hr).1]
    exact hi
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (HeadState first state) (monadLift a : WG.M α) := hoare_liftAmbient a _
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
  have tail (pid : PeerId) : Preserves (HeadState first state) (do
      _ ← cpumaskChooseOnline pid
      if !(← getDev).txWorkQueue.contains pid || (← peekQueuedUnit .txWorker pid) then
        recordQueued .txWorker pid
        modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}) := by
    have read : Preserves (HeadState first state) (get : WG.M WGWorld) :=
      hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
    unfold getDev
    simp only [peekQueuedUnit, recordQueued, invariant]
    repeat' first
      | (allocation_release_head cpumaskChooseOnline
         exact (cpu_packets pid).wp (fun s => ∃ p, s first = some p ∧ p.state = state))
      | (allocation_release_head modifyDev
         unfold modifyDev
         apply hoare_modify
         intro w hi
         simpa [HeadState, txPackets, Option.bind_map, Function.comp_def] using hi)
      | (allocation_release_lift_from AmbientM; exact ambient _)
      | allocation_release_step
    all_goals exact read
  have middle (pid : PeerId) : Hoare (publicationMiddle pid first state)
      (fun _ => True) (fun _ => HeadState first state) := by
    unfold publicationMiddle
    apply hoare_bind _ _ (getter pid (fun _ => True))
    intro peer
    split
    · apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a x v a' hi hr
      cases hr
    · exact hoare_bind _ _ written (fun _ => tail pid)
  rw [publication_factor]
  simp only [List.head?_cons]
  apply hoare_bind _ _ (skb (SkbStore.getTx first))
  intro packet
  apply hoare_bind _ _ (indexOwner_peerDeref_preserves (.keypair packet.keypair) (fun _ => True))
  intro pid
  apply hoare_bind _ _ ((peerGet_packets pid).wp (fun _ => True))
  intro _
  apply hoare_bind _ _ (middle pid)
  intro _
  exact (peerPut_packets (some pid)).wp (fun s => ∃ p, s first = some p ∧ p.state = state)

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
  have getter : Hoare (getPeer pid) P (fun peer w => peer = p ∧ P w) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a peer v a' hi hr
    cases hd : w.dev with
    | none => simp [P, hd] at hi
    | some z =>
      have shape : (z.peers, z.ifindex, z.encryptQueue) =
          (d.peers, d.ifindex, d.encryptQueue) := by simpa [P, hd] using hi
      have hpeers : z.peers = d.peers := congrArg Prod.fst shape
      simp [getPeer, getDev, hd, hpeers, hp] at hr
      rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨rfl, hi⟩
  apply hoare_consequence (P := P) (Q := fun ret w =>
    ret = -WG.EPIPE ∧ txQueues w pid = some (p.txQueue.enqueue item) ∧
    TxRing.nativeCell w = some (d.ifindex, d.encryptQueue))
  · unfold enqueuePerDeviceAndPeer
    cases item.head? with
    | none =>
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a ret v a' hi hr
      cases hr
    | some first =>
      apply hoare_bind _ _ (skb (SkbStore.setTx first (fun p => {p with state := .uncrypted})))
      intro _
      apply hoare_bind _ _ getter
      intro peer
      apply (hoare_iff_run_ambient _ _ _).mpr
      intro w a ret v a' ⟨same, hi⟩ hr
      subst peer
      cases hd : w.dev with
      | none => simp [P, hd] at hi
      | some z =>
        have shape : (z.peers, z.ifindex, z.encryptQueue) =
            (d.peers, d.ifindex, d.encryptQueue) := by simpa [P, hd] using hi
        have hindex : z.ifindex = d.ifindex := congrArg (fun t => t.2.1) shape
        have hring : z.encryptQueue = d.encryptQueue := congrArg (fun t => t.2.2) shape
        have notfull : decide (p.txQueue.count ≥ MAX_QUEUED_PACKETS) = false := by
          simp only [decide_eq_false_iff_not]
          omega
        simp [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
          StateT.run_get, StateT.run_modify,
          Leanux.Proofs.WG.CounterWindow.except_ok_bind,
          Leanux.Proofs.WG.CounterWindow.except_pure,
          getDev, hd, branch, AmbientM.branch,
          notfull, setPeer, modifyDev, cpumaskNextOnlineFrom, hring, hf] at hr
        repeat' split at hr
        all_goals rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        all_goals simp [txQueues, PeerBorrow.resident, wgStoreView,
          TxRing.nativeCell, hindex]
  · intro w hd
    simp [P, hd]
  · exact fun _ _ h => h

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
  have getter : Hoare (getPeer pid) (fun w => w.dev = some d)
      (fun peer w => peer = p ∧ w.dev = some d) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a peer v a' hd hr
    simp [getPeer, getDev, hd, hp] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, hd⟩
  have branchRule {α : Type} (decision : Decision) (value : Bool)
      (P : WGWorld → Prop) (Q : α → WGWorld → Prop) (f : Bool → WG.M α)
      (hf : Hoare (f value) P Q) :
      Hoare ((branch decision value : WG.M Bool) >>= f) P Q := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hi hr
    change ((f value).run w).run _ = .ok ((x, v), ambient') at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
  rw [createSource_factor]
  simp only [List.head?_cons]
  apply hoare_bind _ _ getter
  intro peer
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v a' ⟨he, hd⟩ hr
  subst peer
  simp only [hl] at hr
  apply (hoare_iff_run_ambient _ (fun w => w.dev = some d) _).mp ?_
    w a x v a' hd hr
  apply branchRule .createDataDead false
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply hoare_bind _ _ (enqueue_pipe pid (first :: rest) d p hp hq hf)
  intro ret
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v a' ⟨he, hqueue, hring⟩ hr
  subst ret
  apply (hoare_iff_run_ambient _ (fun w =>
    txQueues w pid = some (p.txQueue.enqueue (first :: rest)) ∧
    TxRing.nativeCell w = some (d.ifindex, d.encryptQueue)) _).mp ?_
      w a x v a' ⟨hqueue, hring⟩ hr
  simp only [beq_self_eq_true]
  apply branchRule .createDataEpipe true
  simp only [↓reduceIte, pure_bind]
  apply hoare_bind _ _ pub
  intro _
  unfold createTailSource
  apply branchRule .createDataOk false
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply branchRule .createDataOkEpipe true
  simp only [↓reduceIte]
  exact preserves_pure _

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
  let P := fun w => HeadState first .dead w ∧ w.sent = sent
  have getter : Preserves P (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a peer v a' hi hr
    rw [(Peers.getPeer_current pid w v peer a a' hr).1]
    exact hi
  have setter (peer : Peer) : Preserves P (setPeer pid peer) := by
    unfold setPeer modifyDev
    apply hoare_modify
    intro w hi
    simpa [P, HeadState, txPackets, Option.bind_map, Function.comp_def] using hi
  have branchRule {α : Type} (decision : Decision) (value : Bool)
      (pre : WGWorld → Prop) (post : α → WGWorld → Prop) (f : Bool → WG.M α)
      (hf : Hoare (f value) pre post) :
      Hoare ((branch decision value : WG.M Bool) >>= f) pre post := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hi hr
    change ((f value).run w).run _ = .ok ((x, v), ambient') at hr
    exact (hoare_iff_run_ambient _ _ _).mp hf _ _ _ _ _ hi hr
  have go : Hoare (WG.andM (branch .txPacket true) (do
      let packet ← getTxSkb first
      branch .txNotUncrypted (packet.state != .uncrypted))) P
      (fun result w => result = true ∧ P w) := by
    unfold WG.andM
    apply branchRule .txPacket true
    simp only [↓reduceIte]
    apply hoare_bind _ _ read
    intro packet
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v a' ⟨hs, hi⟩ hr
    simp [branch, AmbientM.branch, hs, hn] at hr
    rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
    exact ⟨rfl, hi⟩
  have tail (head : DataPacket) (hs : head.state = .dead) : Hoare (do
      setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}
      if ← branch .txCrypted (head.state == PacketState.crypted) then createDataDone pid (first :: rest)
      disposeSource pid (first :: rest) head.keypair) P
      (fun result w => result = true ∧
        (∀ id ∈ first :: rest, txPackets w id = none) ∧ w.sent = sent) := by
    apply hoare_bind _ _ getter
    intro saved
    apply hoare_bind _ _ getter
    intro current
    apply hoare_bind _ _ (setter {saved with txQueue := current.txQueue.dropPeeked})
    intro _
    simp only [hs, hc]
    apply branchRule .txCrypted false
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hoare_consequence (dispose_endpoint pid (first :: rest) head.keypair sent)
      (fun _ h => h.2) (fun _ _ h => h)
  unfold bodySource
  apply hoare_bind _ _ go
  intro goResult
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v a' ⟨he, hi⟩ hr
  subst goResult
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, List.head?_cons, bind_assoc] at hr
  apply (hoare_iff_run_ambient _ P _).mp ?_ w a result v a' hi hr
  apply hoare_bind _ _ read
  intro head
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v a' ⟨hs, hi⟩ hr
  exact (hoare_iff_run_ambient _ _ _).mp (tail head hs) w a result v a' hi hr

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
  let P := fun w => HeadState first .dead w ∧ w.sent = sent
  have getter : Hoare (getPeer pid)
      (fun w => (∃ p, PeerBorrow.resident (wgStoreView w) pid = some p ∧
        p.txQueue.all.head? = some (first :: rest)) ∧ P w)
      (fun p w => p.txQueue.all.head? = some (first :: rest) ∧ P w) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a peer v a' hi hr
    cases hd : w.dev with
    | none =>
      simp [getPeer, getDev, hd, invariant, AmbientM.invariant] at hr
      cases hr
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at hr
        cases hr
      | some p =>
        simp [getPeer, getDev, hd, hp] at hr
        rcases hr with ⟨⟨rfl, rfl⟩, rfl⟩
        obtain ⟨⟨old, hold, hhead⟩, hrest⟩ := hi
        have he : old = p := by
          simpa [PeerBorrow.resident, wgStoreView, hd, hp] using hold.symm
        subst old
        exact ⟨hhead, hrest⟩
  have read (Q : WGWorld → Prop) : Preserves Q (getPeer pid) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a peer v a' hi hr
    rw [(Peers.getPeer_current pid w v peer a a' hr).1]
    exact hi
  have write (peer : Peer) (out : Option (List SkbId)) :
      Preserves (fun w => out = some (first :: rest) ∧ P w) (setPeer pid peer) := by
    unfold setPeer modifyDev
    apply hoare_modify
    intro w hi
    simpa [P, HeadState, txPackets, Option.bind_map, Function.comp_def] using hi
  unfold stepSource
  simp only [bind_assoc]
  apply hoare_bind _ _ getter
  intro peer
  apply hoare_bind _ _ (pk peer.txQueue)
  rintro ⟨out, queue⟩
  apply hoare_bind _ _ (read (fun w => out = some (first :: rest) ∧ P w))
  intro current
  apply hoare_bind _ _ (write {current with txQueue := queue} out)
  intro _
  exact body out

end Leanux.Proofs.WG.Queues.TxDisposition
