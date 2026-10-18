import Leanux.Proofs.WG.Queues.TxLiveNapi
import Leanux.Proofs.WG.Queues.TxLiveMaintenance
import Leanux.Proofs.WG.Queues.CurrentSlotWorkers
import Leanux.Proofs.WG.Queues.HolderScheduler

/-! Actual worker iterations preserve the existing bound on live encryption
items and its physical ring refinement. No packet residency or owner-funding
invariant is added; normal rejection and source Stops keep their original scope. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.LiveWorkers
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open LiveFrontier

theorem product_store {action : Leanux.M α} (frame : SameProductStore action) :
    Preserves (fun w : World=>Ready w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStack.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.product_transport)
    ((ProjectedAction.iff_run _ _ _).mp frame w result v run) hi

private theorem get_tx (id : SkbId) : Preserves Ready (getTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact (Packets.getTxSkb_current id w v result a b run).1 ▸ hi

private theorem get_rx (id : SkbId) : Preserves Ready (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact (Packets.getRxSkb_current id w v result a b run).1 ▸ hi

private theorem set_tx (id : SkbId) (f : DataPacket→DataPacket) : Preserves Ready (setTxSkb id f) :=
  ready_frame (setTxSkb_metadata id f)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStaging.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.packet_ring) _)

private theorem set_rx (id : SkbId) (f : RxPacket→RxPacket) : Preserves Ready (setRxSkb id f) :=
  ready_frame (setRxSkb_metadata id f)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStaging.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.packet_ring) _)

private theorem free_tx (id : SkbId) : Preserves Ready (freeTxSkb id) := by
  apply ready_frame
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    exact (freeTxSkb_retention id w v a b run).metadata
  · exact (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveStaging.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.packet_ring) _

macro "live_worker_step" : tactic => `(tactic| first
  | (allocation_release_head getTxSkb; exact get_tx _)
  | (allocation_release_head getRxSkb; exact get_rx _)
  | (allocation_release_head setTxSkb; exact set_tx _ _)
  | (allocation_release_head setRxSkb; exact set_rx _ _)
  | (allocation_release_head freeTxSkb; exact free_tx _)
  | (allocation_release_head peerGet; exact peer_get _)
  | (allocation_release_head peerPut; exact peer_put _)
  | live_handshake_step)

private theorem cpu (pid : PeerId) : Preserves Ready (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' live_worker_step

private theorem publish_tx (item : List SkbId) (state : PacketState) :
    Preserves Ready (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp only [peekQueuedUnit,recordQueued]
  repeat' first
    | (allocation_release_head cpumaskChooseOnline; exact cpu _)
    | live_worker_step

private theorem publish_rx (id : SkbId) (state : PacketState) :
    Preserves Ready (RxWorkers.publishSource id state) := by
  unfold RxWorkers.publishSource
  repeat' live_worker_step

theorem decrypt_packet (pkt : RxPacket) : Preserves Ready (decryptPacket pkt) := by
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' live_worker_step

theorem prepare : Preserves Ready RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head decryptPacket; exact decrypt_packet _)
    | (allocation_release_head RxWorkers.publishSource; exact publish_rx _ _)
    | live_worker_step

/-- Both actual softirq placements surround the original native prepare cut. -/
theorem decrypt_step : Preserves (fun w : World=>Ready w.wg)
    (decryptStep Env.napiSoftirq Env.napiIrqExit) := by
  rw [← RxWorkers.decrypt_source]
  unfold RxWorkers.decryptSource
  apply preserves_bind LiveNapi.softirq
  intro _
  apply preserves_bind (PublicationPoll.native_product Ready _ prepare)
  intro result
  cases result with
  | none=>exact preserves_pure false
  | some pid=>exact preserves_bind LiveNapi.irqExit fun _=>
      preserves_bind (PublicationPoll.native_product Ready _ (peer_put (some pid))) fun _=>
        preserves_bind LiveNapi.softirq (fun _=>preserves_pure true)

theorem encrypt_packet (key : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World=>Ready w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  let P := fun w : World=>Ready w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product Ready _ ((calculateSkbPadding_sameWGWorld _ _).wp Ready)
  have checksum (p : WG.Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) :=
    PublicationPoll.native_product Ready _
      ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveSend.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.read_key) key)
  routing_tx_source [encryptPacket] using [padding,checksum,keySpec,ambient]

theorem encrypt_tail (item : Option (List SkbId)) :
    Preserves (fun w : World=>Ready w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World=>Ready w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product Ready _ (get_tx id)
  have write (id : SkbId) (f : DataPacket→DataPacket) :
      Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    PublicationPoll.native_product Ready _ (set_tx id f)
  have publish (xs : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product Ready _ (publish_tx xs state)
  have packet := encrypt_packet
  have stepSpec : Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]
  have need : Preserves P (Env.condResched .encryptWorker) := product_store (condResched_sameKernel _)
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [stepSpec,need,ambient]

/-- Ring consume precedes the concrete callback and retains the saved item. -/
theorem encrypt : Preserves (fun w : World=>Ready w.wg)
    (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  rw [RxWorkers.encrypt_source]
  exact preserves_bind (PublicationPoll.native_product Ready _ poll_ready)
    (fun item=>preserves_bind LiveNapi.softirq (fun _=>encrypt_tail item))

/-- Journal transport uses the actual observer's erasure and append contracts. -/
theorem observed {E α : Type} (g : PrefixM E α) (a : Leanux.M α)
    (appends : Appends g) (erases : ErasesPrefix g a)
    (keeps : Preserves (fun w : World => Ready w.wg) a) :
    PrefixPreserves (fun _ w => Ready w.wg) (fun _ => True) g :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveNapi.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveNapi.observed)
    g a appends erases keeps

theorem decrypt : Preserves (fun w : World=>Ready w.wg)
    (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) := by
  let P := fun w : World=>Ready w.wg
  have step : Preserves P (decryptStep Env.napiSoftirq Env.napiIrqExit) := decrypt_step
  have need : Preserves P (Env.condResched .decryptWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  routing_tx_source [decryptIter,workerIter] using [step,need,ambient]

private theorem send_skb (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Preserves Ready (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeer
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head send4; exact socket4 _ _ _ _ _)
    | (allocation_release_head send6; exact socket6 _ _ _ _ _)
    | live_worker_step

private theorem fresh (pid : PeerId) : Preserves Ready (keepKeyFresh pid) := by
  unfold keepKeyFresh WG.andM WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (allocation_release_head sendQueuedHandshakeInitiation; exact queued _ _)
    | live_worker_step

private theorem complete (pid : PeerId) (item : List SkbId) :
    Preserves Ready (createDataDone pid item) := by
  have ambient {α : Type} (a : AmbientM α) : Preserves Ready (monadLift a : WG.M α) := hoare_liftAmbient a Ready
  have traversal := LiveFrontier.traversal pid
  have authenticated := authenticated_sent pid
  have send := send_skb pid
  have dataSent := data_sent pid
  have fresh := fresh pid
  have read := get_tx
  routing_tx_source [createDataDone] using [traversal,authenticated,send,dataSent,fresh,read,ambient]

theorem tx_step (pid : PeerId) : Preserves Ready (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  have ambient {α : Type} (a : AmbientM α) : Preserves Ready (monadLift a : WG.M α) := hoare_liftAmbient a Ready
  have complete := complete pid
  have key (kp : Option KeypairId) : Preserves Ready (keypairPut kp false) := key_put kp false
  have put : Preserves Ready (peerPut (some pid)) := peer_put _
  have dispose (item : List SkbId) (kp : KeypairId) : Preserves Ready (TxDisposition.disposeSource pid item kp) := by
    routing_tx_source [TxDisposition.disposeSource] using [free_tx,key,put]
  have drop : Preserves Ready (do let p ← getPeer pid; setPeer pid {p with txQueue := p.txQueue.dropPeeked}) := by
    repeat' live_worker_step
  have body (first : Option (List SkbId)) : Preserves Ready (TxDisposition.bodySource pid first) := by
    unfold TxDisposition.bodySource
    simp only [getPeer_twice]
    apply preserves_bind
    · routing_tx_source [WG.andM] using [get_tx,ambient]
    · intro go
      cases go with
      | false => exact preserves_pure false
      | true =>
        simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
        cases first with
        | none => exact ambient (AmbientM.invariant "unreachable")
        | some item =>
          cases hh : item.head? with
          | none => simp only [hh]; exact ambient (AmbientM.invariant "an empty ring item")
          | some headId =>
            simp only [hh]
            apply preserves_bind (get_tx headId)
            intro head
            apply preserves_bind drop
            intro _
            routing_tx_source [] using [complete,dispose,ambient]
  unfold TxDisposition.stepSource
  apply preserves_bind (show Preserves Ready (getPeer pid) from by live_worker_step)
  intro p
  apply preserves_bind (store_ready _ (prevQueuePeek_sameWGStore p.txQueue))
  intro out
  rcases out with ⟨first,queue⟩
  apply preserves_bind (show Preserves Ready (do
    let p ← getPeer pid
    setPeer pid {p with txQueue := queue}) from by repeat' live_worker_step)
  intro _
  exact body first

theorem tx (pid : PeerId) : Preserves (fun w : World=>Ready w.wg)
    (txIter pid (Env.condResched .txWorker)) := by
  let P := fun w : World=>Ready w.wg
  have step : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product Ready _ (tx_step pid)
  have need : Preserves P (Env.condResched .txWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  routing_tx_source [txIter,workerIter] using [step,need,ambient]

theorem decrypt_observed : PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True)
    RxHistory.decryptIteration :=
  observed _ _
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.decryptIteration_appends)
    RxHistory.decryptIteration_erases decrypt

theorem encrypt_observed : PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True)
    RxHistory.encryptIteration :=
  observed _ _
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptIteration_appends)
    RxHistory.encryptIteration_erases encrypt

theorem tx_observed (pid : PeerId) : PrefixPreserves (fun _ w=>Ready w.wg) (fun _=>True)
    (RxHistory.mixed (txIterPrefix pid (liftPrefix (Env.condResched .txWorker)))) :=
  observed _ _ (Appends.focus _ _ _)
    (RxHistory.mixed_erases (txIterPrefix_erases pid (erasesPrefix_lift _))) (tx pid)

end Leanux.Proofs.WG.Queues.TxDisposition.LiveWorkers
