import Leanux.Proofs.WG.RetirementSecurity.FinalRxSelection
import Leanux.Proofs.WG.RetirementSecurity.ZeroTimerDispatch
import Leanux.Proofs.WG.RetirementSecurity.ZeroTimerQueued
import Leanux.Proofs.WG.RetirementSecurity.InitializedRetirement
import Leanux.Proofs.WG.RetirementSecurity.HolderInitialized
import Leanux.Proofs.WG.RetirementSecurity.HolderDumpDispatch
import Leanux.Proofs.WG.RetirementSecurity.HolderOuterControls
import Leanux.Proofs.WG.RetirementSecurity.HolderOuterTraffic
import Leanux.Proofs.WG.RetirementSecurity.HolderScheduledTimers
import Leanux.Proofs.WG.RetirementSecurity.HolderScheduler
import Leanux.Proofs.WG.RetirementSecurity.HolderScheduledRx
import Leanux.Proofs.WG.RetirementSecurity.HolderPoll
import Leanux.Proofs.WG.RetirementSecurity.HolderReplayFrames
import Leanux.Proofs.WG.RetirementSecurity.HolderDeviceConfiguration
import Leanux.Proofs.WG.RetirementSecurity.HolderBoundary
import Leanux.Proofs.WG.RetirementSecurity.KeySlotInitialized
import Leanux.Proofs.WG.RetirementSecurity.KeySlotDeferred
import Leanux.Proofs.WG.RetirementSecurity.KeySlotDataCompletion
import Leanux.Proofs.WG.RetirementSecurity.KeySlotTimers
import Leanux.Proofs.WG.RetirementSecurity.KeySlotBulkRemoval
import Leanux.Proofs.WG.RetirementSecurity.KeySlotCreation
import Leanux.Proofs.WG.RetirementSecurity.SlotAnchorConsumers
import Leanux.Proofs.WG.RetirementSecurity.HolderConfigurationUpdate
import Leanux.Proofs.WG.RetirementSecurity.HolderConfigurationCommand
import Leanux.Proofs.WG.RetirementSecurity.HolderPeerCreationSlots
import Leanux.Proofs.WG.RetirementSecurity.HolderShutdown
import Leanux.Proofs.WG.RetirementSecurity.ConfiguredSessionFunding
import Leanux.Proofs.WG.RetirementSecurity.HolderBulkRemoval
import Leanux.Proofs.WG.RetirementSecurity.HolderRemovalConfiguration
import Leanux.Proofs.WG.RetirementSecurity.HolderRemoval
import Leanux.Proofs.WG.RetirementSecurity.HolderDrains
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceJournalOuter
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceJournalDeferred
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceJournalWorkers
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceEncryptionJournal
import Leanux.Proofs.WG.RetirementSecurity.HolderConsumeInitiation
import Leanux.Proofs.WG.RetirementSecurity.SessionPeerFunding
import Leanux.Proofs.WG.RetirementSecurity.HolderResponseSession
import Leanux.Proofs.WG.RetirementSecurity.HandshakeSendDispatch
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDriverCuts
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceInitialized
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDumpFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceLifecycle
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeviceConfiguration
import Leanux.Proofs.WG.RetirementSecurity.OccurrencePeerCreation
import Leanux.Proofs.WG.RetirementSecurity.OccurrencePeerRemoval
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceRemovalCore
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimerFrames
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDeferred
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceScheduler
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshakeWorkers
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceHandshake
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceWorkers
import Leanux.Proofs.WG.RetirementSecurity.RxPollOccurrences
import Leanux.Proofs.WG.RetirementSecurity.ReceiveEntryOwnership
import Leanux.Proofs.WG.RetirementSecurity.RxPeerFunding
import Leanux.Proofs.WG.RetirementSecurity.StackOwnership
import Leanux.Proofs.WG.RetirementSecurity.RemovalPeerFunding
import Leanux.Proofs.WG.RetirementSecurity.DriverOwnership
import Leanux.Proofs.WG.RetirementSecurity.Consequences
import Leanux.Proofs.WG.RetirementSecurity.Clear
import Leanux.Proofs.WG.RetirementSecurity.Payments
import Leanux.Proofs.WG.RetirementSecurity.PacketPayments
import Leanux.Proofs.WG.RetirementSecurity.Holders
import Leanux.Proofs.WG.RetirementSecurity.Confirmation
import Leanux.Proofs.WG.RetirementSecurity.Rotation
import Leanux.Proofs.WG.RetirementSecurity.SessionFunding
import Leanux.Proofs.WG.RetirementSecurity.Session
import Leanux.Proofs.WG.RetirementSecurity.HolderCreation
import Leanux.Proofs.WG.RetirementSecurity.HolderSession
import Leanux.Proofs.WG.RetirementSecurity.HolderClear
import Leanux.Proofs.WG.RetirementSecurity.SessionHolders
import Leanux.Proofs.WG.RetirementSecurity.WorkerRetirement
import Leanux.Proofs.WG.RetirementSecurity.TxEnqueueHolders
import Leanux.Proofs.WG.RetirementSecurity.TxDisposeHolders
import Leanux.Proofs.WG.RetirementSecurity.TxAcquireHolders
import Leanux.Proofs.WG.RetirementSecurity.TxAllocationHolders
import Leanux.Proofs.WG.RetirementSecurity.WorkerHolderClosure
import Leanux.Proofs.WG.RetirementSecurity.TxCreateHolders
import Leanux.Proofs.WG.RetirementSecurity.TxStagedHolders
import Leanux.Proofs.WG.RetirementSecurity.TxPeekHolders
import Leanux.Proofs.WG.RetirementSecurity.KeyHolderFrames
import Leanux.Proofs.WG.RetirementSecurity.TxStoppedHolders
import Leanux.Proofs.WG.RetirementSecurity.OwnershipCompletionFrames
import Leanux.Proofs.WG.RetirementSecurity.TxWorkerHolders
import Leanux.Proofs.WG.RetirementSecurity.RxPublishHolders
import Leanux.Proofs.WG.RetirementSecurity.RxCleanupHolders
import Leanux.Proofs.WG.RetirementSecurity.RxConsumeHolders
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceWorker
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceCreate
import Leanux.Proofs.WG.RetirementSecurity.TxOccurrenceStaging
import Leanux.Proofs.WG.RetirementSecurity.TxCryptAdmission
import Leanux.Proofs.WG.RetirementSecurity.TxCryptCompletion
import Leanux.Proofs.WG.RetirementSecurity.TxCryptCreate
import Leanux.Proofs.WG.RetirementSecurity.TxCryptAllocation
import Leanux.Proofs.WG.RetirementSecurity.TxCryptWorker
import Leanux.Proofs.WG.RetirementSecurity.TxCryptStaging
import Leanux.Proofs.WG.RetirementSecurity.TxStagingFunding
import Leanux.Proofs.WG.RetirementSecurity.HolderHandshakePeerFrames
import Leanux.Proofs.WG.RetirementSecurity.HolderReceiveStep

/-! Campaign 3, T6: local original-operation retirement contracts. The
initialized key-reference ledger, complete caller coverage and conditional
timer/worker progress remain separate obligations. No complete T6 outcome is
claimed by these exports. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

/-- The full native createData caller consumes its unpublished physical
batch: normal/EPIPE admission queues it, while dead-peer/ENOSPC rejection
frees it. It preserves uniqueness and residency of all remaining owned
occurrences, without a separate batch-disjointness or peer-funding premise. -/
theorem original_tx_creation_occurrences
    (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (a b : Ambient)
    (run : ((createData pid items).run w).run a = .ok (((),v),b)) :
    TxInventory locals v := inventory.create a b run

/-- The normal fixture begins with no TX packet occurrences. This is the
physical separation base case; whole Runner transport and completeness of
resident packet representation remain separate obligations. -/
theorem initialized_tx_occurrence_inventory (net bare : Bool) :
    TxInventory [] (Runner.initialWG net bare) := initial_tx_inventory net bare

/-- Native TX allocation creates a fresh unpublished occurrence for every
packet in its batch. Actual queued and caller-held packets stay resident and
pairwise distinct, using the campaign 1 packet frontier at allocation. -/
theorem original_tx_allocation_occurrences (inventory : TxInventory locals w)
    (bounded : Packets.Inv w) (device : w.dev = some d) (pid : PeerId)
    (packets : List DataPacket) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    TxInventory (⟨.unpublished,pid,items⟩ :: locals) v :=
  inventory.allocate bounded device pid packets a b run

/-- Native enqueue transfers the unpublished batch into its actual peer
queue once, including EPIPE; ENOSPC retains the batch for caller cleanup.
Device-ring aliases add no authoritative packet or key-reference occurrence. -/
theorem original_tx_enqueue_occurrences
    (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((ret,v),b)) :
    (ret = -Leanux.ENOSPC ∧ TxInventory (⟨.unpublished,pid,items⟩ :: locals) v) ∨
      ((ret = 0 ∨ ret = -Leanux.EPIPE) ∧ TxInventory locals v) := inventory.enqueue_native a b run

/-- The complete native TX worker preserves packet occurrence uniqueness
and key-reference funding. Its actual cached queue selection derives the
separation needed for disposal; peer-release funding remains explicit.
This does not yet assert orphan completeness or unique ring encryption. -/
theorem original_tx_worker_occurrence_account (account : HolderAccount temporary w)
    (inventory : TxInventory locals w) (funded : PeerReleaseFunded pid w)
    (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v ∧ TxInventory locals v := account.tx_step_inventory inventory funded a b run

/-- Native data receive transfers one actual key acquisition into its RX
queue or pays it on rejection, preserving all other physical key holders.
Lookup borrowing, fresh packet detachment and cleanup funding are derived
from the original caller. The incoming holder account and campaign 1 packet
frontier are explicit; initialized Runner coverage is a separate obligation. -/
theorem original_consume_data_holder_account (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (msg : List UInt8) (src : SkbSource) (ds : Nat)
    (a b : Ambient)
    (run : ((consumeData msg src ds).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.consume_data bounded msg src ds a b run

/-- Native RX allocation creates no extra key credit and cannot replace
a queued holder's cell. Its detached status follows from the concrete holder
account and campaign 1 packet frontier, independently of future enqueue. -/
theorem original_rx_allocation_holder_account {id : SkbId}
    (account : HolderAccount temporary w) (bounded : Packets.Inv w)
    (packet : RxPacket) (a b : Ambient)
    (run : ((newRxSkb packet).run w).run a = .ok ((id,v),b)) :
    HolderAccount temporary v ∧ RxDetached id v ∧
      (v.dev.bind fun d => d.rxSkbs[id]?) = some packet :=
  account.allocate_rx bounded packet a b run

/-- Original RX enqueue transfers one saved key reference into its actual
peer queue on admission, including decrypt-ring EPIPE; peer-queue ENOSPC
retains that reference for cleanup. The saved allocation, actual packet and
peer lookup are explicit incoming source facts. -/
theorem original_rx_enqueue_holder_account {id : SkbId}
    (account : HolderAccount (allocation :: temporary) w)
    (device : w.dev = some d) (packet : d.rxSkbs[id]? = some pkt)
    (peer : d.peers[pkt.peer]? = some p)
    (loan : receiveLoan w pkt.peer id = some ⟨.receive pkt.peer id,allocation⟩)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeerRx id).run w).run a = .ok ((ret,v),b)) :
    (ret = -WG.ENOSPC ∧ HolderAccount (allocation :: temporary) v ∧ holderStore v = holderStore w) ∨
      ((ret = 0 ∨ ret = -WG.EPIPE) ∧ HolderAccount temporary v) :=
  account.enqueue_rx_native device packet peer loan a b run

/-- Original RX publication with the native empty IRQ callback preserves
all key holders while changing packet readiness and NAPI state. Its own peer
borrow prevents the final put from deleting a holder group. -/
theorem original_rx_publication_holder_account (account : HolderAccount temporary w)
    (id : SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerRx (pure () : WG.M Unit) id state).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.publish_rx id state a b run

/-- Native RX cleanup pays the saved packet's key reference once before
freeing its detached cell. Key alignment, concrete queue detachment and
peer-release readiness remain explicit; full initialized poll closure is
separate from this original cleanup cut. -/
theorem original_rx_cleanup_holder_account {id : SkbId}
    (account : HolderAccount (allocation :: temporary) w)
    (pkt : RxPacket) (key : pkt.keypair = allocation.slot) (flag : Bool)
    (detached : RxDetached id w) (ready : PeerReleaseReady pkt.peer w)
    (a b : Ambient)
    (run : ((Queues.RxCredits.cleanup id pkt flag).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.cleanup_rx pkt key flag detached ready a b run

/-- The complete original TX worker preserves physical key-reference
funding: a stopped iteration retains its queued reference; a completed one
moves the cached batch into its actual source-local credit, retains that
credit through send/rekey effects, then pays it once. Incoming packet-head
separation and peer-release funding remain explicit caller obligations. -/
theorem original_tx_worker_holder_account (account : HolderAccount temporary w)
    (separated : TxSeparated pid w) (funded : PeerReleaseFunded pid w)
    (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) : HolderAccount temporary v :=
  account.tx_step separated funded a b run

/-- Native completed-send bookkeeping preserves all physical key holders
and their exact reference funding, including socket failures and a rekey
handshake queued afterward. The latter owns a peer work reference and does
not create a key credit. The incoming account remains an explicit premise. -/
theorem original_tx_completion_holder_account (account : HolderAccount temporary w)
    (pid : PeerId) (items : List SkbId) (a b : Ambient)
    (run : ((createDataDone pid items).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.complete_tx pid items a b run

/-- An original TX worker iteration that stops retains every key-reference
holder. The source may cache its head but cannot enter disposal and return
false; no assumption about later worker progress or packet separation is
needed for this branch. The incoming concrete account remains explicit. -/
theorem original_stopped_tx_holder_account (account : HolderAccount temporary w)
    (pid : PeerId) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((false,v),b)) : HolderAccount temporary v :=
  account.tx_stopped pid a b run

/-- The actual staged submission suffix transfers or pays its saved key
reference exactly once. Its peer acquisition derives nonfinal release and
its allocator derives packet separation before createData. The saved key
account, campaign 1 packet bound, key-to-peer affiliation and head packet's
key word remain visible inputs; this is not full sendStagedPackets closure. -/
theorem original_staged_submission_holder_account
    (account : HolderAccount (allocation :: temporary) w)
    (bounded : Packets.Inv w) (compatible : Queues.RxCredits.KeyCompatible pid allocation.slot w)
    (packet : DataPacket) (packets : List DataPacket) (key : packet.keypair = allocation.slot)
    (a b : Ambient)
    (run : ((do
      Affiliation.sendAcquire allocation.slot
      let items ← (packet :: packets).mapM newTxSkb
      createData pid items).run w).run a = .ok (((),v),b)) : HolderAccount temporary v :=
  account.staged_submit bounded compatible packet packets key a b run

/-- The original TX worker peek keeps all batch references while moving
its logical head into the queue's cached field. A subsequent worker stop
at an uncrypted head therefore has not paid that batch's key reference. -/
theorem original_tx_peek_holder_account (account : HolderAccount temporary w)
    (pid : PeerId) (a b : Ambient)
    (run : ((txPeekSource pid).run w).run a = .ok ((first,v),b)) :
    HolderAccount temporary v ∧ ∃ before after,
      peerAt w pid = some before ∧ peerAt v pid = some after ∧
      first = before.txQueue.all.head? ∧ after.txQueue.all = before.txQueue.all ∧
      after.txQueue.peeked = first := account.peek_tx pid a b run

/-- Actual TX publication changes no key-reference ownership: its temporary
peer borrow is acquired and repaid without deleting any physical holder.
No extra key credit is attributed to a device-ring or worker alias. -/
theorem original_tx_publication_holder_account (account : HolderAccount temporary w)
    (items : List SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx items state).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.publish_tx items state a b run

/-- Full original createData either publishes its one saved key reference
to the peer queue or pays it in rejection cleanup; no reference is lost or
counted twice. Actual batch alignment, detached packet heads and final-peer
slot readiness remain explicit incoming caller facts. -/
theorem original_create_data_holder_account
    (account : HolderAccount (allocation :: temporary) w)
    (batch : transmitLoan w pid items = some ⟨.transmit pid items,allocation⟩)
    (detached : TxDetached items w) (ready : PeerReleaseReady pid w) (a b : Ambient)
    (run : ((createData pid items).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.create_tx batch detached ready a b run

/-- The actual current slot funds staged acquisition: a normal get adds one
saved reference to that allocation, and a null current slot adds none. The
positive count is derived from the concrete holder account, not assumed as
reference-count slack. Saturation remains the source's explicit failure. -/
theorem original_current_key_acquisition (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (a b : Ambient)
    (run : ((keypairGet p.keypairCurrent).run w).run a = .ok ((result,v),b)) :
    ∃ saved : Option Credits.Allocation,
      result = p.keypairCurrent ∧ saved.map (·.slot) = result ∧
      HolderAccount (saved.toList ++ temporary) v := account.current_get found a b run

/-- Original staged TX allocation cannot overwrite any existing batch
holder, and its new packet IDs are separate from every queued batch head.
This source theorem derives separation using campaign 1's packet bound;
the incoming concrete key-holder account remains visible. -/
theorem original_tx_allocation_holder_account (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (packets : List DataPacket) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    HolderAccount temporary v ∧ TxDetached items v := account.allocate_tx bounded packets a b run

/-- A normally completed actual clear-worker dispatch pays the selected
peer's slot references, preserves queued/transient references, and leaves
the slots empty. Native clearing itself discharges final-peer slot readiness.
The incoming holder account is explicit; this does not assert elapsed-time
progress or complete initialized Runner transport. -/
theorem original_dispatched_retirement_holder_account
    (account : HolderAccount temporary w.wg)
    (run : Env.runOneClearWorker.run w = .ok ((),v)) :
    HolderAccount temporary v.wg ∧ ∃ d pid,
      w.wg.dev = some d ∧ pid ∈ d.clearWorkQueue ∧
      SlotsCleared pid v.wg ∧ Retains w.wg v.wg := account.dispatched_zero run

/-- Original TX disposal pays exactly its saved batch reference while
preserving every remaining concrete key holder. Its visible entry premises
require that freed packet IDs are not other queued batch heads and that any
final peer release has already cleared that peer's key slots. Initialized
transport of those caller facts is a separate obligation. -/
theorem original_tx_disposal_holder_account
    (account : HolderAccount (allocation :: temporary) w)
    (detached : TxDetached items w) (ready : PeerReleaseReady pid w) (a b : Ambient)
    (run : ((Queues.TxDisposition.disposeSource pid items allocation.slot).run w).run a =
      .ok ((result,v),b)) : result = true ∧ HolderAccount temporary v :=
  account.dispose_tx detached ready a b run

/-- A native peer put cannot discard key-reference holders when its final
release has cleared all key slots; the source's own normal path checks empty
packet queues. Peer credit and key credit remain distinct, and the final-slot
condition is an explicit caller premise. -/
theorem original_peer_put_holder_account (account : HolderAccount temporary w)
    (ready : PeerReleaseReady pid w) (a b : Ambient)
    (run : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.peer_put ready a b run

/-- Native TX enqueue transfers exactly one saved key reference into its
peer queue, including the device-ring-full path; this prevents either losing
that reference or charging packet aliases as additional references. The
concrete input holder account and saved batch loan remain explicit. -/
theorem original_tx_enqueue_holder_account
    (account : HolderAccount (allocation :: temporary) w)
    (batch : transmitLoan w pid item = some ⟨.transmit pid item,allocation⟩)
    (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid item).run w).run a = .ok ((ret,v),b)) :
    (ret = -ENOSPC ∧ HolderAccount (allocation :: temporary) v) ∨
      ((ret = 0 ∨ ret = -EPIPE) ∧ HolderAccount temporary v) :=
  account.enqueue batch a b run

/-- Dropping the actual cached TX batch moves its one key reference to the
worker's saved local, so subsequent retirement cannot pay a still-queued
reference. This claim is the original reached setter cut, with the native
peer record and cached batch visible as premises. -/
theorem original_tx_drop_holder_account (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (peeked : p.txQueue.peeked = some item)
    (a b : Ambient)
    (run : ((setPeer pid {p with txQueue := p.txQueue.dropPeeked}).run w).run a =
      .ok (((),v),b)) :
    ∃ allocation, transmitLoan w pid item = some ⟨.transmit pid item,allocation⟩ ∧
      HolderAccount (allocation :: temporary) v :=
  account.drop_tx found peeked a b run

/-- A successful original keypair put pays exactly one reference, so local
retirement cannot silently consume additional packet-held references. Zero
counts and NULL-owner failures are excluded by the actual normal-run premise,
not by a claimed initialized ownership invariant. -/
theorem original_reference_payment (id : KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient) (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (run : ((keypairPut (some id) now).run w).run a = .ok (((),v),b)) :
    references v id + 1 = k.refcount :=
  (put_effect id now w v a b d k device resident run).payment

/-- A nonfinal original put retains the same allocation, sending material
and sending nonce counter; paying a reference does not reset cryptographic
state. This local claim assumes the actual normal call and its entry count. -/
theorem original_nonfinal_put (id : KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient) (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (more : 1 < k.refcount)
    (run : ((keypairPut (some id) now).run w).run a = .ok (((),v),b)) :
    keyAt v id = some {k with refcount := k.refcount - 1} :=
  (put_effect id now w v a b d k device resident run).nonfinal more

/-- The final successful original put removes both the allocation and its
index entries, so lookup cannot recover retired material from this store.
This is the final-payment boundary, not a proof that all holders have paid. -/
theorem original_final_put (id : KeypairId) (now : Bool) (w v : WGWorld)
    (a b : Ambient) (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (last : k.refcount = 1)
    (run : ((keypairPut (some id) now).run w).run a = .ok (((),v),b)) :
    keyAt v id = none ∧ Unpublished id v := by
  have effect := put_effect id now w v a b d k device resident run
  exact ⟨effect.final last,effect.unpublished (Or.inr last)⟩

/-- Immediate unreference removes index publication even when packet-held
references retain the key allocation; later lookup and retained use are
different security boundaries. The normal native call is explicit. -/
theorem original_unpublication (id : KeypairId) (w v : WGWorld)
    (a b : Ambient) (d : Device) (k : Keypair)
    (device : w.dev = some d) (resident : d.keypairs[id]? = some k)
    (run : ((keypairPut (some id) true).run w).run a = .ok (((),v),b)) :
    Unpublished id v :=
  (put_effect id true w v a b d k device resident run).unpublished (Or.inl rfl)

/-- No successful original put invents a key allocation or resets a surviving
sending nonce counter. This frame covers nullable calls and needs no key-credit
premise; it does not assert that any particular allocation must survive. -/
theorem original_put_nonce_retention (kp : Option KeypairId) (now : Bool)
    (w v : WGWorld) (a b : Ambient)
    (run : ((keypairPut kp now).run w).run a = .ok (((),v),b)) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ id k, keyAt v id = some k → ∃ old, keyAt w id = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter :=
  put_nonce_projection kp now w v a b run

/-- A normally completed original clear empties all three peer slots while
preserving every surviving key's material and nonce counter. Queued work may
retain allocations; this local theorem does not promise final-store emptiness
or timer/worker progress. -/
theorem original_clear_retirement (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((keypairsClear pid).run w).run a = .ok (((),v),b)) :
    SlotsCleared pid v ∧ Retains w v :=
  ⟨(hoare_iff_run_ambient _ _ _).mp (clear_slots pid) w a () v b True.intro run,
    clear_retains pid w v a b run⟩

/-- Reference acquisition cannot reset a surviving sending nonce counter or
invent a key allocation. This local frame includes nullable input and normal
refusal, without assuming a key-reference ledger. -/
theorem original_get_nonce_retention (kp : Option KeypairId) (w v : WGWorld)
    (a b : Ambient) (result : Option KeypairId)
    (run : ((keypairGet kp).run w).run a = .ok ((result,v),b)) :
    v.keypairCounter = w.keypairCounter ∧
      ∀ id k, keyAt v id = some k → ∃ old, keyAt w id = some old ∧
        k.internalId = old.internalId ∧ k.sendingCounter = old.sendingCounter :=
  get_nonce_projection kp w v a b result run

/-- Successful original acquisition adds exactly one reference occurrence for
the same allocation, preventing retention from being justified by unaccounted
count slack. The supplied exact ledger is local; source-holder alignment and
initialized preservation are separate obligations. -/
theorem original_key_credit_acquisition (account : Credits.Exact credits w)
    (id : KeypairId) (k : Keypair) (found : keyAt w id = some k) (a b : Ambient)
    (run : ((keypairGet (some id)).run w).run a = .ok ((some id,v),b)) :
    Credits.Exact (⟨id,k.internalId⟩ :: credits) v :=
  account.get id k found a b run

/-- Original creation starts exactly one key-reference occurrence at the new
allocation stamp. Existing allocation safety supplies slot vacancy, preventing
an overwrite from silently discarding another allocation's outstanding credits.
This is a local creation contract, not initialized ledger closure. -/
theorem original_key_credit_creation (account : Credits.Exact credits w)
    (allocation : Lifetimes.AllocationInv history w) (word : Option PeerId)
    (id : KeypairId) (a b : Ambient)
    (run : ((keypairCreate word).run w).run a = .ok ((some id,v),b)) :
    Credits.Exact (⟨id,w.keypairCounter + 1⟩ :: credits) v :=
  account.create allocation word id a b run

/-- A successful original put pays its selected key-reference occurrence and
leaves all remaining occurrences exactly funded. The explicit incoming ledger
does not itself identify slots, packet holders or saved worker references. -/
theorem original_key_credit_payment (account : Credits.Exact (allocation :: credits) w)
    (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b)) :
    Credits.Exact credits v :=
  account.put now a b run

/-- Paying the last occurrence in a supplied exact key ledger removes the
allocation and index publication. This derives the native last-reference test
from accounting; initialized source-holder completeness remains unproved. -/
theorem original_last_credit_retirement (account : Credits.Exact (allocation :: credits) w)
    (last : allocation ∉ credits) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b)) :
    keyAt v allocation.slot = none ∧ Unpublished allocation.slot v :=
  account.put_last last now a b run

/-- An outstanding occurrence in a supplied exact key ledger prevents a
successful original put from deleting its allocation or changing its material
and nonce counter. Transport from actual source holders is still required. -/
theorem original_outstanding_credit_retention (account : Credits.Exact (allocation :: credits) w)
    (outstanding : allocation ∈ credits) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some allocation.slot) now).run w).run a = .ok (((),v),b)) :
    ∃ k, keyAt w allocation.slot = some k ∧ k.internalId = allocation.stamp ∧
      keyAt v allocation.slot = some {k with refcount := k.refcount - 1} :=
  account.put_outstanding outstanding now a b run

/-- The original clear pays the references in the peer's actual three
publication slots, preserving exact funding and cryptographic state for every
remaining occurrence. This source-local result permits aliased slots and
assumes their explicit stamped account; initialized holder transport remains
an obligation. -/
theorem original_clear_slot_credits (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (remaining : Credits.Ledger) (aligned : loans.Aligned p)
    (account : PeerAccount pid p (loans.credits ++ remaining) w) (a b : Ambient)
    (run : ((keypairsClear pid).run w).run a = .ok (((),v),b)) :
    Credits.Exact remaining v ∧ SlotsCleared pid v ∧
      ∀ allocation ∈ remaining, ∃ before after,
        keyAt w allocation.slot = some before ∧ keyAt v allocation.slot = some after ∧
        after.internalId = allocation.stamp ∧ keyCore after = keyCore before := by
  have funded := (hoare_iff_run_ambient _ _ _).mp
    (clear_slot_account pid p loans remaining aligned) w a () v b account run
  have retained := clear_retains pid w v a b run
  refine ⟨funded.2,(original_clear_retirement pid w v a b run).1,?_⟩
  intro allocation held
  obtain ⟨after,found,stamp,_⟩ := funded.2.resident held
  obtain ⟨before,old,same⟩ := retained.keys allocation.slot after found
  exact ⟨before,after,old,found,stamp,same⟩

/-- Native TX disposal pays one key reference for the batch, even when it
contains multiple skbs, preventing packet count from consuming other holders'
references. The paid allocation is the supplied saved head loan; its transfer
from the original TX selection is still a caller obligation. -/
theorem original_tx_batch_credit_disposal (pid : PeerId) (items : List SkbId)
    (allocation : Credits.Allocation) (remaining : Credits.Ledger)
    (account : Credits.Exact (allocation :: remaining) w) (a b : Ambient)
    (run : ((Queues.TxDisposition.disposeSource pid items allocation.slot).run w).run a =
      .ok ((result,v),b)) : Credits.Exact remaining v :=
  (hoare_iff_run_ambient _ _ _).mp (Credits.tx_dispose_account pid items allocation remaining)
    w a result v b account run

/-- The literal RX cleanup pays exactly the saved packet's key occurrence;
the separate peer payment and packet free cannot spend another key reference.
The selected packet's stamped loan and the exact incoming account are explicit
local premises, not an initialized ownership claim. -/
theorem original_rx_credit_cleanup (id : SkbId) (pkt : RxPacket) (flag : Bool)
    (allocation : Credits.Allocation) (remaining : Credits.Ledger)
    (key : pkt.keypair = allocation.slot) (account : Credits.Exact (allocation :: remaining) w)
    (a b : Ambient)
    (run : ((Queues.RxCredits.cleanup id pkt flag).run w).run a = .ok (((),v),b)) :
    Credits.Exact remaining v :=
  (hoare_iff_run_ambient _ _ _).mp (Credits.rx_cleanup_account id pkt flag allocation remaining key)
    w a () v b account run

/-- The initialized fixture has no unaccounted key holders: its actual slots,
RX queues and TX batches project to an empty funded ledger. This establishes
only the initialized base case; whole-run preservation is not claimed. -/
theorem initialized_key_holders (net bare : Bool) :
    HolderAccount [] (Runner.initialWG net bare) := initial_holder_account net bare

/-- Native confirmation transfers existing next/current references and pays
only the displaced previous reference, preserving funding for packet holders.
The actual next slot selects this branch. Authentication of the caller and
initialized account preservation remain separate obligations. -/
theorem original_confirmation_credit_transfer (pid : PeerId) (p : Peer)
    (loans : SlotLoans) (remaining : Credits.Ledger) (received : KeypairId)
    (aligned : loans.Aligned p) (next : p.keypairNext = some received)
    (account : PeerAccount pid p (loans.credits ++ remaining) w) (a b : Ambient)
    (run : ((receivedWithKeypair pid received).run w).run a = .ok ((result,v),b)) :
    result = true ∧ loans.confirm.Aligned (confirmedPeer p received) ∧
      PeerAccount pid (confirmedPeer p received) (loans.confirm.credits ++ remaining) v := by
  have effect := (hoare_iff_run_ambient _ _ _).mp
    (confirmation_account pid p loans remaining received aligned next) w a result v b account run
  exact ⟨effect.1,SlotLoans.confirm_aligned aligned next,effect.2⟩

/-- A native confirmation attempt for a non-next key spends no reference
and changes no slot. This local refusal cannot accidentally retire another
session's material; the supplied account is not an initialized closure claim. -/
theorem original_confirmation_credit_refusal (pid : PeerId) (p : Peer)
    (credits : Credits.Ledger) (received : KeypairId)
    (different : p.keypairNext ≠ some received) (account : PeerAccount pid p credits w)
    (a b : Ambient)
    (run : ((receivedWithKeypair pid received).run w).run a = .ok ((result,v),b)) :
    result = false ∧ PeerAccount pid p credits v :=
  (hoare_iff_run_ambient _ _ _).mp
    (confirmation_refused_account pid p credits received different) w a result v b account run

/-- Original key insertion transfers the caller's one new-key occurrence
into the initiator/current or responder/next slot and pays exactly the native
displaced occurrences. Aliases are counted separately; source acquisition of
the incoming loan and whole-run account preservation are explicit boundaries. -/
theorem original_new_key_credit_transfer (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (newKey : Credits.Allocation) (remaining : Credits.Ledger) (k : Keypair)
    (aligned : loans.Aligned p)
    (account : PeerAccount pid p (newKey :: loans.credits ++ remaining) w)
    (resident : keyAt w newKey.slot = some k) (a b : Ambient)
    (run : ((addNewKeypair pid newKey.slot).run w).run a = .ok (((),v),b)) :
    (loans.rotate newKey k.iAmTheInitiator p.keypairNext.isSome).Aligned
        (rotatedPeer p newKey.slot k.iAmTheInitiator) ∧
      PeerAccount pid (rotatedPeer p newKey.slot k.iAmTheInitiator)
        ((loans.rotate newKey k.iAmTheInitiator p.keypairNext.isSome).credits ++ remaining) v :=
  ⟨SlotLoans.rotate_aligned aligned newKey k.iAmTheInitiator,
    rotation_account pid p loans newKey remaining k aligned account resident a b run⟩

/-- Native key expiry changes validity without resetting a sending nonce or
spending a key reference. Retained packet references therefore keep their
funding and allocation identity; admission and timer progress are separate. -/
theorem original_expiry_reference_nonce_frame (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((expireCurrentPeerKeypairs pid).run w).run a = .ok (((),v),b)) :
    referenceNonceView v = referenceNonceView w :=
  (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp (expire_referenceNonce pid) w a () v b run

/-- Native derivation installs material without resetting the allocated
sending nonce or changing key-reference funding. This excludes a bookkeeping
reset at derivation; the cipher and KDF security remain outside the claim. -/
theorem original_derivation_reference_nonce_frame (id : KeypairId) (initiator : Bool)
    (ck : List UInt8) (w v : WGWorld) (a b : Ambient)
    (run : ((deriveKeys id initiator ck).run w).run a = .ok (((),v),b)) :
    referenceNonceView v = referenceNonceView w :=
  (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (deriveKeys_referenceNonce id initiator ck) w a () v b run

/-- A successful original session front funds exactly one new allocation
occurrence through creation, initialization and derivation, preventing a new
session from being justified by a fabricated caller loan. Existing R2 supplies
vacancy; initialized incoming funding and later holder transport remain open. -/
theorem original_session_front_credit_creation (pid : PeerId) (p : Peer)
    (ctx : SessionOrigin.Context) (w v : WGWorld) (a b : Ambient)
    (account : PeerAccount pid p credits w) (allocation : Lifetimes.AllocationInv history w)
    (run : ((SessionOrigin.front pid).run w).run a = .ok ((some ctx,v),b)) :
    PeerAccount pid p (⟨ctx.slot,w.keypairCounter + 1⟩ :: credits) v :=
  Credits.front_peer_account pid p ctx w v a b account allocation run

/-- A complete successful native session funds its new key from the actual
allocation, then transfers that occurrence into the actual slot rotation and
pays the displaced references. No caller-owned new-key loan is assumed. The
incoming slot account and R2 allocation invariant remain explicit premises;
initialized global holder preservation and Noise security are separate. -/
theorem original_session_credit_transfer (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (remaining : Credits.Ledger) (w v : WGWorld) (a b : Ambient)
    (aligned : loans.Aligned p) (account : PeerAccount pid p (loans.credits ++ remaining) w)
    (allocation : Lifetimes.AllocationInv history w)
    (run : ((beginSession pid).run w).run a = .ok ((true,v),b)) :
    ∃ ctx middle middleAmbient k,
      ((SessionOrigin.front pid).run w).run a = .ok ((some ctx,middle),middleAmbient) ∧
      keyAt middle ctx.slot = some k ∧ k.internalId = w.keypairCounter + 1 ∧
      PeerAccount pid (rotatedPeer (zeroedPeer p) ctx.slot k.iAmTheInitiator)
        ((loans.rotate ⟨ctx.slot,w.keypairCounter + 1⟩ k.iAmTheInitiator p.keypairNext.isSome).credits ++ remaining) v :=
  session_account pid p loans remaining w v a b aligned account allocation run

/-- A normal native session refusal leaves the world and key-reference
account unchanged; a false result cannot conceal consumed slot references.
The source proof retains its explicit incoming account and R2 premises. -/
theorem original_session_credit_refusal (pid : PeerId) (p : Peer) (loans : SlotLoans)
    (remaining : Credits.Ledger) (w v : WGWorld) (a b : Ambient)
    (aligned : loans.Aligned p) (account : PeerAccount pid p (loans.credits ++ remaining) w)
    (allocation : Lifetimes.AllocationInv history w)
    (run : ((beginSession pid).run w).run a = .ok ((false,v),b)) :
    v = w ∧ PeerAccount pid p (loans.credits ++ remaining) v :=
  session_refused_account pid p loans remaining w v a b aligned account allocation run

/-- Native creation contributes one temporary reference while preserving the
exact funding of actual slots, RX entries and TX batches. R2 vacancy and the
incoming concrete-holder account remain visible; complete initialized caller
coverage is not assumed proved. -/
theorem original_holder_creation (account : HolderAccount temporary w)
    (allocation : Lifetimes.AllocationInv history w) (word : Option PeerId)
    (id : KeypairId) (a b : Ambient)
    (run : ((keypairCreate word).run w).run a = .ok ((some id,v),b)) :
    HolderAccount (⟨id,w.keypairCounter + 1⟩ :: temporary) v :=
  account.create allocation word id a b run

/-- Native acquisition adds one temporary reference to the same allocation
without changing actual durable holders or relying on unaccounted count slack.
The concrete-holder account is an explicit incoming invariant. -/
theorem original_holder_acquisition (account : HolderAccount temporary w)
    (id : KeypairId) (k : Keypair) (found : keyAt w id = some k) (a b : Ambient)
    (run : ((keypairGet (some id)).run w).run a = .ok ((some id,v),b)) :
    HolderAccount (⟨id,k.internalId⟩ :: temporary) v :=
  account.get id k found a b run

/-- Native payment of a temporary reference leaves every actual slot, RX
entry and TX batch exactly funded. Retained holder residency is derived from
the remaining occurrences, including when the selected put is final. The
incoming concrete-holder account still needs whole-execution closure. -/
theorem original_holder_payment (account : HolderAccount (paid :: temporary) w)
    (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some paid.slot) now).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v :=
  account.put now a b run

/-- A real durable holder prevents another temporary reference's release
from deleting its allocation or resetting its sending state. The holder is
read from the native slot/queue projection, with the incoming account explicit. -/
theorem original_durable_holder_retention (account : HolderAccount (paid :: temporary) w)
    (projected : durableLoans w = some loans) (loan : KeyLoan) (member : loan ∈ loans)
    (same : loan.allocation = paid) (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some paid.slot) now).run w).run a = .ok (((),v),b)) :
    ∃ k, keyAt w paid.slot = some k ∧ k.internalId = paid.stamp ∧
      keyAt v paid.slot = some {k with refcount := k.refcount - 1} :=
  account.put_durable projected loan member same now a b run

/-- When no actual durable holder and no other temporary occurrence owns an
allocation, the native successful final payment removes its store cell and
index publication. Complete source-holder accounting is an explicit premise. -/
theorem original_holder_final_retirement (account : HolderAccount (paid :: temporary) w)
    (last : ∀ loans, durableLoans w = some loans →
      paid ∉ loans.map (·.allocation) ++ temporary)
    (now : Bool) (a b : Ambient)
    (run : ((keypairPut (some paid.slot) now).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v ∧ keyAt v paid.slot = none ∧ Unpublished paid.slot v :=
  account.put_last last now a b run

/-- Actual slots supply the entry references for native clear, including
aliased slot occurrences; clearing cannot spend an unrelated arbitrary loan.
This derives the post-payment reference equation from a concrete incoming
holder account, with post-state projection reassembly still outstanding. -/
theorem original_holder_clear_funding (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (a b : Ambient)
    (run : ((keypairsClear pid).run w).run a = .ok (((),v),b)) :
    ∃ slots : SlotLoans, ∃ remaining : Credits.Ledger,
      slots.Aligned p ∧ PeerAccount pid p (slots.credits ++ remaining) w ∧
      PeerAccount pid {p with keypairNext := none, keypairPrevious := none, keypairCurrent := none} remaining v :=
  account.clear_funded found a b run

/-- The whole native session obtains its old-slot funding from actual
holders and its new reference from actual creation, so rotation cannot invent
or silently discard references. R2 allocation safety and the incoming holder
account remain explicit; complete initialized projection transport is separate. -/
theorem original_holder_session_funding (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (allocation : Lifetimes.AllocationInv history w)
    (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((true,v),b)) :
    ∃ slots : SlotLoans, ∃ remaining : Credits.Ledger,
      slots.Aligned p ∧ PeerAccount pid p (slots.credits ++ remaining) w ∧
      ∃ ctx middle middleAmbient k,
        ((SessionOrigin.front pid).run w).run a = .ok ((some ctx,middle),middleAmbient) ∧
        keyAt middle ctx.slot = some k ∧ k.internalId = w.keypairCounter + 1 ∧
        PeerAccount pid (rotatedPeer (zeroedPeer p) ctx.slot k.iAmTheInitiator)
          ((slots.rotate ⟨ctx.slot,w.keypairCounter + 1⟩ k.iAmTheInitiator
            p.keypairNext.isSome).credits ++ remaining) v :=
  account.session_funded found allocation a b run

/-- Native clearing removes and pays each actual peer-slot reference while
preserving exact funding of the actual post-state RX/TX holders and temporary
locals. Slot multiplicity is retained, and no final-store emptiness or worker
progress is asserted. Whole initialized caller closure remains separate. -/
theorem original_clear_holder_account (pid : PeerId) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (keypairsClear pid) :=
  clear_holders pid temporary

/-- Native responder confirmation preserves exact funding of the actual
post-state holders while moving next/current ownership and paying displaced
previous ownership. Intermediate pointer copies add no references. The
incoming holder account is explicit, and authentication belongs to T5. -/
theorem original_confirmation_holder_account (account : HolderAccount temporary w)
    (pid : PeerId) (key : KeypairId) (a b : Ambient)
    (run : ((receivedWithKeypair pid key).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := account.confirm pid key a b run

/-- Native key insertion consumes its caller's one temporary reference and
reconstructs exact funding of the actual rotated slots and retained queues.
This is the original source group, including displaced-key payments, without
assuming that intermediate pointer copies are new references. -/
theorem original_rotation_holder_account (account : HolderAccount (newKey :: temporary) w)
    (pid : PeerId) (a b : Ambient)
    (run : ((addNewKeypair pid newKey.slot).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.rotate pid a b run

/-- The complete native session preserves exact key-reference funding of
actual slots and queued packets, deriving its new reference from creation and
accounting for rotation and retirement. The incoming concrete holder account
and named R2 allocation invariant remain explicit; whole initialized caller
coverage is still required. -/
theorem original_session_holder_account (account : HolderAccount temporary w)
    (allocation : Lifetimes.AllocationInv history w) (pid : PeerId) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := account.session allocation pid a b run

/-- Completion of the actual zero-material worker clears all three peer key
slots and cannot reset surviving sending material or nonce counters. Packet
references may retain allocations; this conclusion needs no incoming ledger
or initialization invariant and makes no elapsed-time progress claim. -/
theorem original_zero_worker_retirement (pid : PeerId) (w v : WGWorld) (a b : Ambient)
    (run : ((queuedExpiredZeroKeyMaterial pid).run w).run a = .ok (((),v),b)) :
    SlotsCleared pid v ∧ Retains w v := zero_worker_retirement pid w v a b run

/-- A normally completed actual clear-worker dispatch retires the slots of
a peer selected from its real work queue, including record-selected dispatch,
without changing any surviving allocation's material or nonce counter. The
native completion premise is explicit; a timer deadline alone is insufficient. -/
theorem original_dispatched_key_retirement (w v : World)
    (run : Env.runOneClearWorker.run w = .ok ((),v)) :
    ∃ d pid, w.wg.dev = some d ∧ pid ∈ d.clearWorkQueue ∧
      SlotsCleared pid v.wg ∧ Retains w.wg v.wg := dispatched_retirement w v run


/-- Full native staging cannot duplicate an existing physical TX occurrence:
its nonce loop and refusal paths preserve the incoming inventory, and its
fresh allocation is either published or freed by the actual createData path.
The incoming occurrence inventory and packet frontier bound remain explicit;
whole initialized caller transport and ring-phase authorization are separate. -/
theorem original_staged_tx_occurrences (inventory : TxInventory locals w)
    (bounded : Packets.Inv w) (pid : PeerId) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) :
    TxInventory locals v := inventory.staged bounded pid a b run


/-- Initialized encryption has no live or active packet aliases. The later
native admission and poll contracts track actual peer-owned batches, with
UNCRYPTED heads and no duplicate IDs across live and active encryption. -/
theorem initialized_tx_crypt_occurrences (net bare : Bool) :
    TxCryptInventory [] (Runner.initialWG net bare) := initial_tx_crypt_inventory net bare

/-- Native admission cannot make a physical packet available to two
concurrent encryption selections. Only successful ring admission adds an
alias; ENOSPC retains the local, and EPIPE installs only peer ownership.
Incoming concrete occurrence and encryption-phase inventories are explicit;
whole initialized caller transport remains separate. -/
theorem original_tx_crypt_admission (crypt : TxCryptInventory active w)
    (owned : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (device : w.dev = some d) (a b : Ambient)
    (run : ((enqueuePerDeviceAndPeer pid items).run w).run a = .ok ((ret,v),b)) :
    TxCryptInventory active v := crypt.enqueue owned device a b run

/-- Native ring consumption transfers one live alias into the selected
local and preserves its queued owner, UNCRYPTED head and exclusive packet
occurrences. Stale occupied slots are excluded. This is a source-cut claim;
callback and whole initialized driver transport remain explicit work. -/
theorem original_tx_crypt_selection (crypt : TxCryptInventory active w) (a b : Ambient)
    (run : ((Queues.TxRing.pollSource).run w).run a = .ok ((out,v),b)) :
    TxCryptInventory (out.toList ++ active) v := crypt.poll a b run


/-- The whole selected native encryption continuation preserves exact
key-reference funding and physical packet ownership: reading cryptographic
material and writing ciphertext creates no new owner. Incoming concrete
holder and occurrence inventories remain explicit, and this cut starts after
the native ring poll and softirq callback. -/
theorem original_encryption_holder_account (items : Option (List SkbId)) :
    Preserves (fun w : World => HolderAccount temporary w.wg ∧ TxInventory locals w.wg)
      (Queues.RxWorkers.encryptStepTailSource items) := encrypt_tail_accounts items

/-- Completed native encryption consumes only its active encryption alias;
the peer queue retains its owning occurrence until TX disposal, and every
other live or active batch keeps its UNCRYPTED head and unique packet IDs.
The incoming phase invariant is explicit; whole initialized callback and
driver transport is still required. -/
theorem original_encryption_phase_completion (crypt : TxCryptInventory (items :: active) w.wg)
    (run : (Queues.RxWorkers.encryptStepTailSource (some items)).run w = .ok (result,v)) :
    TxCryptInventory active v.wg := crypt.complete run


/-- A normal original peer put cannot delete an owning TX queue: the
native final-reference guard rejects release while a packet batch remains.
This forward ownership fact needs no reference-funding assumption; it does
not assert that an unfunded execution avoids a Stop. -/
theorem original_peer_put_keeps_tx_owner (owned : TxQueuedBatch w items)
    (target : Option PeerId) (a b : Ambient)
    (run : ((peerPut target).run w).run a = .ok (((),v),b)) : TxQueuedBatch v items :=
  owned.peer_put target a b run

/-- Full native creation preserves exclusive live/active encryption aliases
through success, peer refusal, ring refusal and final cleanup. Rejection can
free only the unpublished local batch, never a pending encryption packet.
Incoming physical occurrence and encryption-phase inventories remain explicit;
initialized staging and callback transport remains separate. -/
theorem original_tx_creation_crypt_occurrences (crypt : TxCryptInventory active w)
    (owned : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w) (a b : Ambient)
    (run : ((createData pid items).run w).run a = .ok (((),v),b)) :
    TxCryptInventory active v := crypt.create owned a b run

/-- Original batch allocation followed by creation cannot duplicate a
physical packet or make it available to two encryption selections. Fresh IDs
preserve existing aliases; publication installs the new ownership and rejection
disposes only its local batch. The incoming concrete inventories and campaign 1
packet frontier remain explicit until whole initialized caller transport. -/
theorem original_tx_allocate_create_occurrences (inventory : TxInventory locals w)
    (crypt : TxCryptInventory active w) (bounded : Packets.Inv w)
    (device : w.dev = some d) (pid : PeerId) (packets : List DataPacket) (a b : Ambient)
    (run : ((do let items ← packets.mapM newTxSkb; createData pid items).run w).run a =
      .ok (((),v),b)) : TxInventory locals v ∧ TxCryptInventory active v :=
  allocate_create_occurrences inventory crypt bounded device pid packets a b run

/-- The original TX worker cannot dispose a packet still pending encryption
or duplicate a surviving physical occurrence. Its actual readiness guard and
queue uniqueness discharge disposal separation; socket/timer completion and
final reference payments retain every other pending encryption owner. Incoming
inventories remain explicit until their whole initialized driver transport. -/
theorem original_tx_worker_crypt_occurrences (inventory : TxInventory locals w)
    (crypt : TxCryptInventory active w) (pid : PeerId) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    TxInventory locals v ∧ TxCryptInventory active v :=
  ⟨inventory.step pid a b run,crypt.step inventory pid a b run⟩

/-- With its actual key-holder account and peer-release funding, the original
TX worker also preserves exact remaining key-reference credit while removing
only its selected batch. Peer funding is a distinct visible premise; it is
never substituted for a key credit. Whole initialized funding remains open. -/
theorem original_tx_worker_joint_account (account : HolderAccount temporary w)
    (inventory : TxInventory locals w) (crypt : TxCryptInventory active w)
    (funded : PeerReleaseFunded pid w) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v ∧ TxInventory locals v ∧ TxCryptInventory active v :=
  ⟨account.tx_step (inventory.separated pid) funded a b run,
   inventory.step pid a b run,crypt.step inventory pid a b run⟩

/-- Full original staged send preserves exclusive physical occurrences and
pending/active encryption aliases through the nonce loop, key refusal,
restaging, allocation and native publication. Fresh allocation supplies
separation; no packet-disjointness premise is added. Incoming inventories and
the campaign 1 frontier are explicit until initialized driver closure. -/
theorem original_staged_tx_crypt_occurrences (inventory : TxInventory locals w)
    (crypt : TxCryptInventory active w) (bounded : Packets.Inv w) (pid : PeerId) (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) :
    TxInventory locals v ∧ TxCryptInventory active v :=
  CryptStaging.staged ⟨⟨bounded,inventory⟩,crypt⟩ pid a b run

/-- Full original staged send cannot leak or fabricate a key reference:
the real current-slot acquisition funds its temporary occurrence, which is
repaid on rejection or transferred to the actual submitted batch. The nonce
loop's generated packets carry that same key slot. Current-key affiliation
and the packet frontier are independent visible inputs; whole initialized
transport of the incoming holder account is still a separate obligation. -/
theorem original_staged_key_holder_account (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (compatible : Queues.RxCredits.CurrentCompatible pid w)
    (a b : Ambient)
    (run : ((sendStagedPackets pid).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := account.staged bounded compatible a b run

/-- Original receive completion preserves exact key-reference ownership:
authenticated confirmation transfers existing slots, and its conditional
staged send pays or publishes its current-key acquisition. Packet boundedness
and incoming key affiliation remain explicit, as does the incoming account;
this local source result does not assert initialized driver closure. -/
theorem original_receive_completion_key_holder_account (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (compatible : Queues.RxCredits.KeyCompatible pid pkt.keypair w)
    (endpoint : Endpoint) (a b : Ambient)
    (run : ((consumeDataDone pid pkt endpoint).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v := account.receive_done bounded compatible endpoint a b run

/-- The shared campaign driver's actual staged-send cut preserves key
reference accounting and exclusive physical/encryption occurrences. Exact
projection recovers the native run; it is not used to infer an event order.
The named incoming inventories, frontier and affiliation remain visible
until whole initialized driver transport is proved. -/
theorem shared_driver_staging_ownership {E : Type}
    {ρ : E → Option TransmitSecurity.Nonce.Allocation}
    {hooks : TransmitSecurity.Driver.Hooks E}
    (projects : TransmitSecurity.Driver.HooksProjects ρ hooks TransmitSecurity.Driver.nonceHooks)
    (before : DriverOwnership.Boundary temporary locals active w)
    (bounded : Packets.Inv w) (compatible : Queues.RxCredits.CurrentCompatible pid w)
    (a b : Ambient) (h : List E)
    (run : (Leanux.Proofs.Logged.runWGPrefix
      (TransmitSecurity.Driver.stagingObserved hooks pid) w a h).1 = .ok (((),v),b)) :
    DriverOwnership.Boundary temporary locals active v :=
  DriverOwnership.staging projects before bounded compatible a b h run

/-- Original receive completion cannot duplicate a TX packet or discard
pending encryption ownership. Confirmation's conditional staged send adds
only freshly allocated occurrences; endpoint, timer and lookup bookkeeping
retain all existing occurrences. The packet frontier and incoming physical
inventories are explicit until initialized driver transport is complete. -/
theorem original_receive_completion_tx_occurrences (before : TxOccurrences locals active w)
    (bounded : Packets.Inv w) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) (a b : Ambient)
    (run : ((consumeDataDone pid pkt ep).run w).run a = .ok ((result,v),b)) :
    TxOccurrences locals active v := receive_done_occurrences before bounded pid pkt ep a b run

/-- The actual TX worker cannot destroy a peer with published key slots
while paying its queued-batch peer reference: the real durable-holder ledger
funds that batch separately from its base/caller protection. This discharges
the previous release-funding premise on completed iterations; idle iterations
require no release premise. Initialized transport of the named concrete
accounts and slot protection remains open. -/
theorem original_tx_worker_peer_funded_key_account (account : HolderAccount temporary w)
    (inventory : TxInventory locals w)
    (funded : holders.Funded carriers loans w) (stable : Queues.RxCredits.StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (pid : PeerId) (a b : Ambient)
    (run : ((txStep pid).run w).run a = .ok ((result,v),b)) : HolderAccount temporary v :=
  account.tx_step_holders inventory funded stable anchors pid a b run

/-- Native peer unpublication retains the actual key holders and moves its
base peer reference to the caller's detached loans. Published slots remain
protected through that source cut; unpublication cannot be mistaken for final
key destruction. All incoming concrete accounts remain visible. -/
theorem original_peer_unpublication_accounts (keys : HolderAccount temporary w)
    (peers : holders.Funded carriers loans w) (stable : Queues.RxCredits.StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (pid : PeerId) (a b : Ambient)
    (run : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v ∧
      (holders.withoutBase (Queues.RxCredits.BaseRemoval.live holders.base pid)).Funded carriers
        (Queues.RxCredits.BaseRemoval.detached holders.base pid ++ loans) v ∧
      Queues.RxCredits.StableRx carriers v ∧
      SlotPeerReferences (holders.withoutBase (Queues.RxCredits.BaseRemoval.live holders.base pid))
        (Queues.RxCredits.BaseRemoval.detached holders.base pid ++ loans) v :=
  make_dead_accounts keys peers stable anchors pid a b run

/-- Every native transmit-entry outcome retains exact key references and
exclusive physical/encryption occurrences. Destination lookup supplies its
real temporary peer reference, which selection or the final payment repays;
staging adds only fresh packet occurrences. Current-key affiliation and the
packet frontier remain explicit until initialized caller transport. -/
theorem original_transmit_entry_ownership (keys : HolderAccount temporary w)
    (inventory : TxInventory locals w) (crypt : TxCryptInventory active w)
    (bounded : Packets.Inv w) (compatible : Queues.RxCredits.CurrentsCompatible w)
    (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) (a b : Ambient)
    (run : ((wgXmit family addr packets mtu).run w).run a = .ok ((result,v),b)) :
    HolderAccount temporary v ∧ TxInventory locals v ∧ TxCryptInventory active v :=
  ⟨keys.transmit bounded compatible family addr packets mtu a b run,
    TransmitOccurrences.transmit ⟨bounded,inventory,crypt⟩ family addr packets mtu a b run⟩

/-- The shared driver's native transmit entry retains its concrete key,
physical-packet and pending-encryption ownership accounts on every normal
result. The checked projection supplies the original execution; the native
lookup supplies payment funding. This is a caller contract, not a claim of
whole initialized Runner transport. -/
theorem shared_driver_transmit_entry_ownership {E : Type}
    {ρ : E → Option TransmitSecurity.Nonce.Allocation}
    {hooks : TransmitSecurity.Driver.Hooks E}
    (projects : TransmitSecurity.Driver.HooksProjects ρ hooks TransmitSecurity.Driver.nonceHooks)
    (before : DriverOwnership.Boundary temporary locals active w)
    (bounded : Packets.Inv w) (compatible : Queues.RxCredits.CurrentsCompatible w)
    (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) (a b : Ambient) (h : List E)
    (run : (Leanux.Proofs.Logged.runWGPrefix
      (TransmitSecurity.Driver.transmitObserved hooks family addr packets mtu) w a h).1 =
      .ok ((result,v),b)) : DriverOwnership.Boundary temporary locals active v :=
  DriverOwnership.transmit_entry projects before bounded compatible family addr packets mtu a b h run

/-- Actual native Stack replies preserve key references and exclusive TX
packet/encryption ownership, including nested transmit errors and repeated
callback batches. Campaign 1's allocation witness supplies the packet frontier;
current-key affiliation is transported by its native lookup/staging contracts.
These concrete incoming invariants are initialized separately; full Runner
transport is still required. -/
theorem original_stack_batch_ownership
    (before : StackOwnership.Ready temporary locals active w.wg)
    (packets : List (List UInt8))
    (run : (packets.forM Env.deliverInner).run w = .ok ((),v)) :
    StackOwnership.Ready temporary locals active v.wg :=
  (hoare_iff_run _ _ _).mp (StackOwnership.stackForM_stack packets) w () v before run

/-- The normally empty fixture supplies the actual key, physical-packet,
pending-encryption and allocation accounts required by native Stack transport.
This establishes its base case without an assumed ownership invariant. -/
theorem initialized_stack_ownership (net bare : Bool) :
    StackOwnership.Ready [] [] [] (Runner.initialWG net bare) := StackOwnership.initial net bare

/-- Original RX dequeue moves exactly the selected packet's queued key
reference into the poll local. Actual carrier uniqueness and queue counts
establish that it is detached; no assumed packet-disjointness premise is used.
Initialized transport of the incoming concrete accounts remains separate. -/
theorem original_rx_dequeue_accounts {id : SkbId} (keys : HolderAccount temporary w)
    (carriers : Queues.RxCredits.CarrierState entries loans w)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (peeked : p.rxQueue.peeked = some id) (a b : Ambient)
    (run : ((Queues.dropRxQueue pid).run w).run a = .ok (((),v),b)) :
    ∃ allocation, receiveLoan w pid id = some ⟨.receive pid id,allocation⟩ ∧
      HolderAccount (allocation :: temporary) v ∧
      Queues.RxCredits.CarrierState
        (⟨⟨d.ifindex,id⟩,⟨d.ifindex,pid,p.internalId⟩,.selected⟩ ::
          Queues.RxCredits.remaining entries [⟨d.ifindex,id⟩]) loans v ∧ RxDetached id v :=
  keys.drop_rx_carrier carriers device peer peeked a b run

/-- Native RX cleanup pays the selected key credit once and frees its actual
packet. The carrier ledger supplies detachment and the selected peer credit;
base/caller protection prevents final peer destruction with published key
slots. These remain distinct visible accounts until initialized transport. -/
theorem original_rx_carrier_cleanup_account {selected : Queues.RxCredits.Carrier}
    {holders : Queues.RxCredits.DurableHolders}
    (keys : HolderAccount (allocation :: temporary) w)
    (carriers : Queues.RxCredits.CarrierState (selected :: rest) (holders.owners ++ loans) w)
    (anchors : SlotPeerReferences holders loans w) (phase : selected.phase = .selected)
    (packet : Queues.RxCredits.packetAt w selected.packet = some pkt)
    (key : pkt.keypair = allocation.slot) (flag : Bool) (a b : Ambient)
    (run : ((Queues.RxCredits.cleanup selected.packet.slot pkt flag).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := keys.cleanup_rx_carrier carriers anchors phase packet key flag a b run

/-- Full native UDP receive retains exact key references and exclusive TX
packet/encryption ownership through header refusal, handshake queuing, data
admission and original cleanup. The packet allocation witness is supplied by
campaign 1; this claim assumes neither authentication nor successful delivery.
Whole initialized Runner transport remains a separate obligation. -/
theorem original_receive_entry_ownership
    (before : ReceiveEntry.Joint temporary locals active w)
    (msg : List UInt8) (src : SkbSource) (a b : Ambient)
    (run : ((wgReceive msg src).run w).run a = .ok (((),v),b)) :
    ReceiveEntry.Joint temporary locals active v := ReceiveEntry.joint before msg src a b run

/-- The shared driver's actual receive-entry leaf preserves the concrete
key and TX occurrence accounts, with campaign 1 allocation freshness. Native
RX allocation and decrypt aliases cannot duplicate a TX occurrence. The
incoming accounts remain visible until their complete initialized transport. -/
theorem shared_driver_receive_entry_ownership {E : Type}
    (before : ReceiveEntry.Joint temporary locals active w.wg)
    (msg : List UInt8) (src : SkbSource) (h : List E)
    (run : (Leanux.Proofs.Logged.runPrefix
      (TransmitSecurity.Driver.receiveEntryObserved msg src) w h).1 = .ok ((),v)) :
    ReceiveEntry.Joint temporary locals active v.wg := ReceiveEntry.shared before msg src h run

/-- Native RX polling preserves exclusive TX packet occurrences and pending
cipher-work aliases, including authenticated staging and GRO stack replies.
No key-holder or current-key-affiliation hypothesis is needed. Allocation
freshness is the independent campaign-1 invariant; full initialized driver
transport remains separate. -/
theorem original_rx_poll_tx_ownership
    (before : OccurrenceStack.Ready locals active w.wg) (pid : PeerId) (budget : Nat)
    (run : (rxPoll pid budget (fun packets => packets.forM Env.deliverInner)).run w = .ok (result,v)) :
    OccurrenceStack.Ready locals active v.wg :=
  (hoare_iff_run _ _ _).mp (RxPollOccurrences.stack pid budget) w result v before run

/-- The shared driver's actual RX-poll cut preserves the physical TX
ownership and encryption-phase invariant through its checked native source
projection. Its state contract does not infer event chronology from erasure;
whole initialized driver transport is still required. -/
theorem shared_driver_rx_poll_tx_ownership {E : Type}
    {ρ : E → Option TransmitSecurity.Nonce.Allocation}
    {hooks : TransmitSecurity.Driver.Hooks E}
    (projects : TransmitSecurity.Driver.HooksProjects ρ hooks TransmitSecurity.Driver.nonceHooks)
    (before : OccurrenceStack.Ready locals active w.wg) (pid : PeerId) (budget : Nat) (h : List E)
    (run : (Leanux.Proofs.Logged.runPrefix
      (TransmitSecurity.Driver.nativePollObserved hooks pid budget) w h).1 = .ok (result,v)) :
    OccurrenceStack.Ready locals active v.wg := RxPollOccurrences.shared projects before pid budget h run

/-- A complete native encryption iteration preserves exclusive TX
ownership: the consumed ring batch remains an explicit active alias during
softirq, then is removed after its one selected continuation. The actual RX
callbacks may stage new packets; independent allocation freshness prevents
collisions. Whole initialized driver transport is still required. -/
theorem original_encrypt_iteration_tx_ownership
    (before : OccurrenceStack.Ready locals active w.wg)
    (run : (encryptIter Env.checksumHelp Env.napiSoftirq
      (Env.condResched .encryptWorker)).run w = .ok (result,v)) :
    OccurrenceStack.Ready locals active v.wg :=
  (hoare_iff_run _ _ _).mp OccurrenceEncrypt.iteration w result v before run

/-- A complete native decrypt iteration preserves TX physical ownership
and pending cipher-work aliases across preparation, publication, IRQ exit,
NAPI and scheduler callbacks. This does not assume key-holder accounting;
normal source completion and the incoming packet inventory stay explicit. -/
theorem original_decrypt_iteration_tx_ownership
    (before : OccurrenceStack.Ready locals active w.wg)
    (run : (decryptIter Env.napiSoftirq Env.napiIrqExit
      (Env.condResched .decryptWorker)).run w = .ok (result,v)) :
    OccurrenceStack.Ready locals active v.wg :=
  (hoare_iff_run _ _ _).mp OccurrenceDecrypt.iteration w result v before run

/-- Native TX disposal preserves physical and cipher-work exclusivity
using its actual readiness guard and derived queue separation. This packet
claim needs no extra key/peer-credit assumption; initialized whole-driver
transport and key-reference accounting remain distinct obligations. -/
theorem original_tx_iteration_occurrences
    (before : OccurrenceStack.Ready locals active w.wg) (pid : PeerId)
    (run : (txIter pid (Env.condResched .txWorker)).run w = .ok (result,v)) :
    OccurrenceStack.Ready locals active v.wg :=
  (hoare_iff_run _ _ _).mp (OccurrenceTx.iteration pid) w result v before run

/-- The shared campaign driver transports the concrete occurrence
invariant through its complete native encryption iteration. The exact native
projection links this source cut without a second scheduler or journal. This
is a caller closure, not the still-open initialized Runner invariant. -/
theorem shared_driver_encrypt_iteration_tx_ownership {E : Type}
    {ρ : E → Option TransmitSecurity.Nonce.Allocation}
    {hooks : TransmitSecurity.Driver.Hooks E}
    (projects : TransmitSecurity.Driver.HooksProjects ρ hooks TransmitSecurity.Driver.nonceHooks)
    (before : OccurrenceStack.Ready locals active w.wg) (h : List E)
    (run : (Leanux.Proofs.Logged.runPrefix
      (TransmitSecurity.Driver.encryptIterObserved hooks) w h).1 = .ok (result,v)) :
    OccurrenceStack.Ready locals active v.wg := OccurrenceWorkers.encrypt projects before h run

/-- Native Noise construction/consumption and MAC computation preserve
exclusive physical TX ownership and pending cipher aliases. Rejected
handshakes may release an empty peer; the proof retains every nonempty
owning queue and the complete TX packet store. Initialized driver transport
remains a separate obligation. -/
theorem original_noise_helpers_tx_ownership (call : Lifetimes.HandshakeCall) {result : call.Result}
    (before : OccurrenceStack.Ready locals active w) (a b : Ambient)
    (run : ((call.original.run w).run a) = .ok ((result,v),b)) :
    OccurrenceStack.Ready locals active v :=
  (hoare_iff_run_ambient _ _ _).mp (OccurrenceHandshake.call call) w a result v b before run

/-- Session creation, key derivation and rotation do not mutate queued TX
packet records or cipher aliases. This full packet frame supports historical
material tracking; it does not itself guarantee that a referenced key
allocation survives, which requires the separate reference ledger. -/
theorem original_session_tx_packets (pid : PeerId) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    Queues.TxDisposition.txPackets v = Queues.TxDisposition.txPackets w :=
  congrArg Prod.snd ((Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (OccurrenceKeys.session_wire pid) w a result v b run)

/-- A normally completed native peer release preserves every ordered TX
queue after treating an absent peer as an empty queue. The native final
reference checks justify deletion; no ownership or separation premise is
assumed to make a nonempty queue disappear. -/
theorem original_peer_release_queue_contents (pid : Option PeerId) (a b : Ambient)
    (run : ((peerPut pid).run w).run a = .ok (((),v),b)) :
    txQueueContents v = txQueueContents w :=
  (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp (queueContents_peer_put pid) w a () v b run

/-- The full native handshake receive path preserves exclusive TX packet
ownership and pending encryption aliases, including successful response
keepalive staging, cookie replies and final peer release. This is concrete
caller closure; the initialized scheduler/configuration transport remains open. -/
theorem original_handshake_receive_tx_ownership
    (before : OccurrenceStack.Ready locals active w) (msg : List UInt8) (src : SkbSource)
    (a b : Ambient) (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    OccurrenceStack.Ready locals active v :=
  (hoare_iff_run_ambient _ _ _).mp (OccurrenceHandshake.receive msg src) w a () v b before run

/-- The original handshake-send worker changes neither complete TX packet
records nor ordered owning queues, including its final reference payment.
It therefore cannot replay or manufacture queued ciphertext work. Key
material survival remains governed by the separate actual reference ledger. -/
theorem original_handshake_send_tx_ownership
    (before : OccurrenceStack.Ready locals active w) (pid : PeerId) (a b : Ambient)
    (run : ((handshakeSendWorker pid).run w).run a = .ok (((),v),b)) :
    OccurrenceStack.Ready locals active v :=
  (hoare_iff_run_ambient _ _ _).mp (OccurrenceHandshake.send_call (.worker pid)) w a () v b before run

/-- The shared driver's complete handshake iteration preserves physical TX
ownership through its checked native specialization, including actual
keepalive allocation. It uses the same driver as the nonce journal; event
chronology and initialized whole-driver ownership are separate obligations. -/
theorem shared_driver_handshake_iteration_tx_ownership {E : Type}
    {ρ : E → Option TransmitSecurity.Nonce.Allocation} {hooks : TransmitSecurity.Driver.Hooks E}
    (projects : TransmitSecurity.Driver.HooksProjects ρ hooks TransmitSecurity.Driver.nonceHooks)
    (before : OccurrenceStack.Ready locals active w.wg) (h : List E)
    (run : (Leanux.Proofs.Logged.runPrefix
      (TransmitSecurity.Driver.receiveIterObserved hooks) w h).1 = .ok (result,v)) :
    OccurrenceStack.Ready locals active v.wg := OccurrenceHandshake.shared projects before h run

/-- The actual scheduler preserves physical TX ownership and pending
cipher aliases across every normal draining activation, including recorded
resumptions, crypt-ahead completion and NAPI. The existing source scheduler
factor supplies the loop; timer/configuration and initialized outer-Runner
coverage remain distinct obligations. -/
theorem original_scheduler_tx_ownership
    (before : OccurrenceStack.Ready locals active w.wg) (stack : Option Worker)
    (run : (Env.schedule stack).run w = .ok ((),v)) :
    OccurrenceStack.Ready locals active v.wg :=
  (hoare_iff_run _ _ _).mp (OccurrenceScheduler.schedule stack) w () v before run

/-- The shared campaign driver's real scheduler preserves the concrete
TX ownership/phase invariant. The source-projection premise identifies the
same native scheduling run; it adds no queue-uniqueness or reference-credit
hypothesis. Initial configuration and retirement accounting remain open. -/
theorem shared_driver_scheduler_tx_ownership {E : Type}
    {ρ : E → Option TransmitSecurity.Nonce.Allocation} {hooks : TransmitSecurity.Driver.Hooks E}
    (projects : TransmitSecurity.Driver.HooksProjects ρ hooks TransmitSecurity.Driver.nonceHooks)
    (before : OccurrenceStack.Ready locals active w.wg) (stack : Option Worker) (h : List E)
    (run : (Leanux.Proofs.Logged.runPrefix
      (TransmitSecurity.Driver.scheduleObserved hooks stack) w h).1 = .ok ((),v)) :
    OccurrenceStack.Ready locals active v.wg := OccurrenceScheduler.shared projects before stack h run

/-- Every normal native deferred-worker or timer call preserves exclusive
TX packet ownership and pending encryption aliases, including wheel-selected
callbacks, placeholder timers, crypt/send draining and queued key clearing.
Initialized configuration transport and the complete key-credit ledger remain
separate obligations; this theorem assumes only its displayed entry invariant. -/
theorem original_deferred_tx_ownership (call : Lifetimes.EnvDeferredCall)
    {result : call.Result} (before : OccurrenceStack.Ready locals active w.wg)
    (run : call.original.run w = .ok (result,v)) :
    OccurrenceStack.Ready locals active v.wg :=
  (hoare_iff_run _ _ _).mp (OccurrenceDeferred.original call) w result v before run

/-- Actual queued handshake-send dispatch preserves complete TX packet
records and the encryption ring. This exact native frame supports packet
provenance across control traffic without assuming numeric key-slot survival. -/
theorem original_send_dispatch_tx_wire
    (run : Env.runOneSendWorker.run w = .ok ((),v)) :
    txCryptWire v.wg = txCryptWire w.wg :=
  (Lifetimes.ProjectedAction.iff_run _ _ _).mp OccurrenceDeferred.send_one_wire w () v run

/-- Actual queued zero-key dispatch preserves complete TX packet records
and the encryption ring, despite removing published keys. Key-material
survival must be derived separately from live reference credits. -/
theorem original_clear_dispatch_tx_wire
    (run : Env.runOneClearWorker.run w = .ok ((),v)) :
    txCryptWire v.wg = txCryptWire w.wg :=
  (Lifetimes.ProjectedAction.iff_run _ _ _).mp OccurrenceDeferred.clear_one_wire w () v run

/-- Native retransmit, new-handshake and zero-material timer callbacks
preserve every TX packet record and encryption-ring entry. Their control
traffic cannot substitute data packets; the two keepalive timers use the
separate concrete staging contract instead of this exact frame. -/
theorem original_nonstaging_timer_tx_wire (pid : PeerId) (timer : PeerTimer)
    (notKeepalive : timer ≠ .sendKeepalive) (notPersistent : timer ≠ .persistentKeepalive)
    (a b : Ambient) (run : ((timerCallback pid timer).run w).run a = .ok (((),v),b)) :
    txCryptWire v = txCryptWire w :=
  (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (OccurrenceTimers.callback_wire pid timer notKeepalive notPersistent) w a () v b run

/-- The native post-dead peer-removal tail preserves physical TX ownership
through both workqueue flushes, key clearing and final peer release. Native
pending-crypt guards remain in the source; this is conditional on normal
completion and supplies no termination or whole-Runner hypothesis. -/
theorem original_peer_removal_tail_tx_ownership
    (before : OccurrenceStack.Ready locals active w) (pid : PeerId) (a b : Ambient)
    (run : ((peerRemoveAfterDead pid).run w).run a = .ok (((),v),b)) :
    OccurrenceStack.Ready locals active v :=
  (hoare_iff_run_ambient _ _ _).mp (OccurrenceRemoval.after_dead pid) w a () v b before run

/-- The real bounded handshake-workqueue flush preserves complete TX packet
records and the pending encryption ring, including recorded worker selection
and queued zero-material execution. This exact packet frame assumes no key
residency or unpublication restriction. -/
theorem original_handshake_flush_tx_wire (upTo : Option PeerId) (a b : Ambient)
    (run : ((drainHandshakeSendWq upTo).run w).run a = .ok (((),v),b)) :
    txCryptWire v = txCryptWire w :=
  (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (OccurrenceRemoval.drain_wire upTo) w a () v b run

/-- Complete native removal of every peer preserves exclusive TX ownership
and pending encryption aliases, through actual allowed-IP teardown, marking
peers dead, workqueue flushes and final releases. Successful removal never
silently drops an owned packet; native queued-work guards remain required. -/
theorem original_remove_all_tx_ownership
    (before : OccurrenceStack.Ready locals active w) (a b : Ambient)
    (run : (peerRemoveAll.run w).run a = .ok (((),v),b)) :
    OccurrenceStack.Ready locals active v :=
  (hoare_iff_run_ambient _ _ _).mp OccurrenceRemoval.remove_all w a () v b before run

/-- Complete native peer removal preserves the full TX packet store and
pending encryption ring, including route-list cleanup and final peer release.
This packet provenance frame supplies no key-material lifetime assumption. -/
theorem original_peer_remove_tx_wire (peer : Option PeerId) (a b : Ambient)
    (run : ((peerRemove peer).run w).run a = .ok (((),v),b)) :
    txCryptWire v = txCryptWire w :=
  (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (OccurrenceRemoval.remove_wire peer) w a () v b run

/-- Native peer creation preserves exclusive TX ownership and pending
encryption aliases. The actual next-peer slot is proved empty from the
allocation bound already carried by the entry invariant; the theorem adds
no vacant-slot assumption and includes allocation refusal and errno returns. -/
theorem original_peer_creation_tx_ownership
    (before : OccurrenceStack.Ready locals active w) (key : Key) (psk : Option Key)
    (a b : Ambient) (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    OccurrenceStack.Ready locals active v :=
  (hoare_iff_run_ambient _ _ _).mp (OccurrenceCreation.create key psk) w a result v b before run

/-- Complete native device configuration preserves exclusive TX ownership
and pending encryption aliases, through allowed-IP changes, fresh peer creation,
removal, key replacement and actual staged/keepalive sends. No queue-separation,
vacant-slot or frozen-configuration premise is added beyond the entry invariant.
Initialized outer execution, historical phase uniqueness and key credits remain
separate claims. -/
theorem original_device_configuration_tx_ownership
    (before : OccurrenceStack.Ready locals active w) (attrs : DeviceAttrs) (a b : Ambient)
    (run : ((wgSetDevice attrs).run w).run a = .ok ((result,v),b)) :
    OccurrenceStack.Ready locals active v :=
  (hoare_iff_run_ambient _ _ _).mp (OccurrenceConfiguration.set_device attrs) w a result v b before run

/-- Native device creation preserves physical TX ownership at an empty
local-packet boundary, establishing an empty physical encryption ring on the
new allocation and retaining existing-device/refusal outcomes. Numeric slots
may restart in the new device epoch; no cross-epoch packet identity is assumed. -/
theorem original_device_creation_tx_ownership
    (before : OccurrenceStack.Ready [] [] w) (a b : Ambient)
    (run : (wgCreate.run w).run a = .ok ((result,v),b)) : OccurrenceStack.Ready [] [] v :=
  (hoare_iff_run_ambient _ _ _).mp OccurrenceLifecycle.create w a result v b before run

/-- Native destruction preserves physical TX ownership at an empty local
boundary through actual peer releases and final device removal. Source guards
still reject queued work; no fairness, progress or complete key-ledger result
is inferred from this normal-return contract. -/
theorem original_device_destruction_tx_ownership
    (before : OccurrenceStack.Ready [] [] w) (a b : Ambient)
    (run : (wgDestruct.run w).run a = .ok (((),v),b)) : OccurrenceStack.Ready [] [] v :=
  (hoare_iff_run_ambient _ _ _).mp OccurrenceLifecycle.destruct w a () v b before run

/-- Every normally returning original syscall and its deferred suffix preserves
exclusive physical TX owners, resident queued packets and uncrypted live-ring
aliases. This is an empty-local caller contract; it does not assert historical
one-encryption-per-allocation or complete reference-credit accounting. -/
theorem original_syscall_tx_ownership (call : Syscall)
    (before : OccurrenceStack.Ready [] [] w.wg)
    (run : (Leanux.syscall call).run w = .ok (result,v)) :
    OccurrenceStack.Ready [] [] v.wg :=
  (hoare_iff_run _ _ _).mp (OccurrenceSyscall.syscall_native call) w result v before run

/-- Executable acceptance of the original initialized Runner derives exclusive
physical TX ownership, residency and pending encryption-alias discipline at the
returned world and every actual syscall entry. No input inventory or per-call
preservation premise is assumed. This does not yet assert historical AEAD
uniqueness, allocation-to-key coherence or the initialized key-credit ledger. -/
theorem initialized_runner_tx_ownership (trace : Runner.Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders = .ok result) :
    ∃ w h,
      Leanux.Proofs.Logged.runPrefixOuter
        (Queues.RxCredits.RunnerAccount.observed trace placeholders) [] = (.ok (result,w),h) ∧
      OccurrenceStack.Ready [] [] w.wg ∧
      ∀ index, index < trace.ops.size → OccurrenceRunner.OperationEntry trace placeholders index := by
  obtain ⟨w,h,source,ready,entries⟩ := OccurrenceInitialized.accepted trace placeholders run
  exact ⟨w,h,source,ready.2,entries⟩

/-- Native dump cursors retain every TX packet record and pending encryption
ring through peer borrowing and release, so observation cannot replace a staged
packet's selected material. This is a state frame, not an egress claim. -/
theorem original_device_dump_tx_wire (ref : DeviceRef) (a b : Ambient)
    (run : ((wgGetDevice ref).run w).run a = .ok ((result,v),b)) :
    txCryptWire v = txCryptWire w :=
  (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (OccurrenceDump.dump_device_wire ref) w a result v b run

/-- The shared driver's actual ring poll and intervening softirq derive a
resident, unique selected encryption batch with an uncrypted head, disjoint from all
other pending aliases, at the exact tail entry. The complete remaining run
uses that same world and journal, even when the encryption tail Stops. The
entry inventory is explicit; historical AEAD uniqueness is a separate claim. -/
theorem shared_encryption_selection_cut {E : Type}
    {w u v : World} {h j k : List E} {items : List SkbId}
    {ρ : E → Option TransmitSecurity.Nonce.Allocation}
    {hooks : TransmitSecurity.Driver.Hooks E}
    (projects : TransmitSecurity.Driver.HooksProjects ρ hooks TransmitSecurity.Driver.nonceHooks)
    (before : OccurrenceStack.Ready locals active w.wg)
    (polled : Leanux.Proofs.Logged.runPrefix hooks.poll w h = (.ok (some items,u),j))
    (callback : Leanux.Proofs.Logged.runPrefix
      (TransmitSecurity.Driver.softirqObserved hooks) u j = (.ok ((),v),k)) :
    OccurrenceStack.Ready locals (items :: active) v.wg ∧
    OccurrenceDriverCuts.Selected active items v.wg ∧
    Leanux.Proofs.Logged.runPrefix (TransmitSecurity.Driver.encryptIterObserved hooks) w h =
      Leanux.Proofs.Logged.runPrefix (TransmitSecurity.Driver.encryptTailObserved hooks (some items)) v k :=
  OccurrenceDriverCuts.entry projects before polled callback

/-- Actual deferred handshake-send dispatch retains the exact key-reference
ledger while paying the selected peer work reference. Source-funded peer
holders and independent base/caller protection of published key slots are
explicit inputs; peer funding is not a substitute for the key ledger, whose
initialized whole-run transport remains open. -/
theorem original_queued_handshake_key_account
    (account : HolderAccount temporary w.wg)
    (funded : holders.Funded carriers loans w.wg)
    (stable : Queues.RxCredits.StableRx carriers w.wg)
    (anchors : SlotPeerReferences holders loans w.wg)
    (run : Env.runOneSendWorker.run w = .ok ((),v)) : HolderAccount temporary v.wg :=
  account.dispatched_send funded stable anchors run

/-- Native handshake-response production preserves the exact key-reference
ledger through allocation, derivation, slot rotation and the socket/timer suffix,
including normal refusal. The incoming allocation witness and key account stay
explicit until the initialized key-credit invariant is closed. -/
theorem original_handshake_response_key_account
    (before : ReceiveEntry.Ready temporary w) (pid : PeerId) (a b : Ambient)
    (run : ((sendHandshakeResponse pid).run w).run a = .ok (((),v),b)) :
    ReceiveEntry.Ready temporary v :=
  (hoare_iff_run_ambient _ _ _).mp (HolderResponse.response pid) w a () v b before run

/-- Native session publication preserves the independent peer reference that
protects its key slots. The selected real base occurrence and the exact incoming
key account remain visible; the temporary handshake loan cannot fund both
obligations. Whole initialized key-credit transport is a separate obligation. -/
theorem original_session_reference_accounts
    (before : ReceiveEntry.Ready temporary w)
    (anchors : SlotPeerReferences holders loans w)
    (funded : holders.Funded carriers loans w)
    (selected : pid ∈ holders.base.map Queues.RxCredits.Owner.slot) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    ReceiveEntry.Ready temporary v ∧ SlotPeerReferences holders loans v :=
  ⟨(hoare_iff_run_ambient _ _ _).mp (HolderResponse.session pid) w a result v b before run,
    anchors.session_from_base funded selected a b run⟩

/-- Original initiation and response consumption preserve exact key-reference
accounting on authentication success and rejection. Each failed authentication
pays its own actual nonzero peer acquisition, which cannot be a final peer
release; no independent peer-credit premise is required. Initialized transport
of the incoming key account remains a separate campaign obligation. -/
theorem original_handshake_consumption_key_accounts (msg : List UInt8) :
    Preserves (HolderAccount temporary) (consumeInitiation msg) ∧
    Preserves (HolderAccount temporary) (consumeResponse msg) :=
  ⟨HolderConsume.initiation msg,HolderConsume.response msg⟩

/-- A shared-journal encryption iteration records only actual polls from
physically owned input states, preserves the detached batch through softirq,
and consumes it in the native encryption tail. Already emitted certificates
survive Stop. The incoming physical boundary remains explicit until shared
scheduler and initialized-driver coverage is joined to this source contract. -/
theorem shared_encryption_poll_certificates :
    Leanux.Proofs.Logged.PrefixPreserves (OccurrencePollJournal.Inv [])
      OccurrencePollJournal.Safe
      (TransmitSecurity.Driver.encryptIterObserved TransmitSecurity.Journal.hooks) :=
  OccurrencePollJournal.encryption_iteration

/-- Every actual encryption poll performed by the shared scheduler has a
physically owned input and a native execution certificate, including polls
triggered from TX crypt-ahead. The scheduler derives each iteration's input
from its preceding source steps; only its incoming boundary remains explicit
until outer initialized-driver composition is complete. -/
theorem shared_scheduler_poll_certificates (stack : Option Worker) :
    Leanux.Proofs.Logged.PrefixPreserves (OccurrencePollJournal.Inv [])
      OccurrencePollJournal.Safe
      (TransmitSecurity.Driver.scheduleObserved TransmitSecurity.Journal.hooks stack) :=
  OccurrencePollJournal.schedule stack

/-- Native shared-driver deferred work retains encryption poll certificates
with physically owned inputs through actual timer-wheel dispatch, send-worker callbacks
and draining. Each scheduler input is derived from its preceding source path;
the outer initialized-driver boundary remains to be composed. -/
theorem shared_deferred_poll_certificates (j : UInt64) :
    OccurrencePollJournal.ProductSafe (TransmitSecurity.Driver.sendWorkersObserved TransmitSecurity.Journal.hooks) ∧
    OccurrencePollJournal.ProductSafe (TransmitSecurity.Driver.afterXmitObserved TransmitSecurity.Journal.hooks) ∧
    OccurrencePollJournal.ProductSafe (TransmitSecurity.Driver.timersObserved TransmitSecurity.Journal.hooks j) ∧
    OccurrencePollJournal.ProductSafe (TransmitSecurity.Driver.afterAdvanceObserved TransmitSecurity.Journal.hooks) :=
  ⟨OccurrencePollJournal.send_workers,OccurrencePollJournal.after_xmit,
    OccurrencePollJournal.timers j,OccurrencePollJournal.after_advance⟩

/-- Every actual encryption poll recorded by the initialized shared runner
starts with unique, resident, owned pending TX occurrences and transfers its
selected batch into the corresponding explicit local inventory. Its receipt
describes the original native poll; later Stop retains the certificate. No
incoming ownership invariant or per-call safety premise is assumed. This
physical result remains separate from initialized exact key-reference credit. -/
theorem initialized_shared_poll_ownership (trace : Runner.Trace) (placeholders : Bool)
    (receipt : Leanux.Proofs.Logged.RunWitness (Option (List SkbId)))
    (member : TransmitSecurity.Journal.Event.polled receipt ∈
      (Leanux.Proofs.Logged.runPrefixOuter
        (TransmitSecurity.Journal.execute trace placeholders) []).2) :
    OccurrencePollJournal.Certificate receipt := by
  apply OccurrencePollJournal.initialized trace placeholders receipt
  exact List.mem_filterMap.mpr ⟨.polled receipt,member,rfl⟩


/-- Actual successful initiation or response consumption retains more than
one reference to the selected peer, alongside the exact key-holder account.
This spare reference is derived from the native nonzero acquisition and
preserved by the authentication path; it is not assumed as caller funding. -/
theorem original_handshake_consumers_acquired (msg : List UInt8) :
    Hoare (consumeInitiation msg) (HolderAccount temporary) (HolderConsume.Acquired temporary) ∧
    Hoare (consumeResponse msg) (HolderAccount temporary) (HolderConsume.Acquired temporary) :=
  ⟨HolderConsume.initiation_acquired msg,HolderConsume.response_acquired msg⟩

/-- Native keepalive staging preserves exact key credit and a selected
handshake peer's nonfinal reference count. Actual admission and rejection
are included through the source handoff count equation; incoming allocation
and three-slot compatibility remain separately named local prerequisites. -/
theorem original_keepalive_acquired_peer (pid selected : PeerId) :
    Preserves (HolderKeepalive.Selected temporary selected) (sendKeepalive pid) :=
  HolderKeepalive.keepalive_selected pid


/-- Native handshake receive preserves exact key-reference credit through
both Noise arms, their session/socket/keepalive calls, cookies and the real
final peer payments. The source's own nonzero acquisition discharges those
payments. Allocation and configured/current-slot session support remain
explicit incoming prerequisites until whole-run key-account closure. -/
theorem original_handshake_receive_key_accounts (msg : List UInt8) (src : SkbSource) :
    Preserves (HolderReceive.Ready temporary) (receiveHandshakePacket msg src) ∧
    Preserves (HolderReceive.Ready temporary) receiveStep :=
  ⟨HolderReceive.receive msg src,HolderReceive.step⟩

/-- The original cookie consumer preserves the exact key ledger for success,
authentication rejection and lookup miss. Its own acquired peer reference
protects every actual final put; no separate peer-funding premise is assumed. -/
theorem original_cookie_consumer_key_account (msg : List UInt8) :
    Preserves (HolderAccount temporary) (cookieMessageConsume msg) :=
  HolderConsume.cookie msg

/-- Native workqueue draining preserves the exact key-reference account while
paying only selected peer work references. Published key slots keep their
independent base/caller anchors. Incoming key and peer accounts are explicit;
initialized whole-driver closure is a separate obligation. -/
theorem original_work_drain_key_accounts
    (keys : HolderAccount temporary w)
    (peers : holders.Funded carriers loans w)
    (stable : Queues.RxCredits.StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (upTo : Option PeerId)
    (a b : Ambient)
    (run : ((drainHandshakeSendWq upTo).run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready holders carriers loans temporary v :=
  (hoare_iff_run_ambient _ _ _).mp (HolderDrain.drain upTo) w a () v b
    (HolderDrain.initial keys peers stable anchors) run

/-- Deleting a peer's timers and flushing its pending clear work retain the
same exact key account and independent slot anchors through the actual native
queue selections; elapsed time alone is not asserted to complete retirement. -/
theorem original_timers_stop_key_accounts
    (keys : HolderAccount temporary w)
    (peers : holders.Funded carriers loans w)
    (stable : Queues.RxCredits.StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (pid : PeerId)
    (a b : Ambient)
    (run : ((timersStop pid).run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready holders carriers loans temporary v :=
  (hoare_iff_run_ambient _ _ _).mp (HolderDrain.timers_stop pid) w a () v b
    (HolderDrain.initial keys peers stable anchors) run

/-- Native post-dead peer removal clears publication slots before its actual
inline drains and pays the detached peer occurrence exactly once. The exact
key account retains all remaining physical key holders, so unpublication is
not confused with allocation destruction. Incoming accounts remain explicit. -/
theorem original_after_dead_key_accounts
    (before : HolderDrain.Ready original carriers (o :: loans) temporary w)
    (a b : Ambient)
    (run : ((peerRemoveAfterDead o.slot).run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready original carriers loans temporary v ∧ SlotsCleared o.slot v :=
  HolderRemoval.after_dead before a b run

/-- Native configuration removal pays its selected base reference and its
separate acquired caller reference, preserving the exact key account of all
remaining physical holders. Selection and caller funding come from the actual
successful lookup; initial list coherence and both ledgers remain visible. -/
theorem original_lookup_removal_key_accounts
    (key : Key) (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (keys : HolderAccount temporary w) (peers : holders.Funded carriers loans w)
    (stable : Queues.RxCredits.StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w)
    (coherent : Queues.RxCredits.BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (remove : (flags &&& WGPEER_F_REMOVE_ME != 0) = true) (a middle b : Ambient)
    (lookup : ((pubkeyLookup key).run w).run a = .ok ((some pid,u),middle))
    (update : ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run middle =
      .ok ((result,v),b)) :
    result = 0 ∧ HolderDrain.Ready
      (holders.withoutBase (Queues.RxCredits.BaseRemoval.live holders.base pid))
      carriers loans temporary v :=
  HolderRemoval.lookup_update_remove key attrs flags psk keys peers stable anchors coherent configured remove
    a middle b lookup update

/-- Native bulk removal detaches and pays every actual saved base occurrence
while retaining exact credit for physical key holders. Inline drains may pay
work occurrences; equal saved slots retain their multiplicities. No immediate
allocation destruction or initialized whole-driver invariant is assumed. -/
theorem original_bulk_removal_key_accounts
    (keys : HolderAccount temporary w) (peers : holders.Funded carriers loans w)
    (stable : Queues.RxCredits.StableRx carriers w)
    (anchors : SlotPeerReferences holders loans w) (a b : Ambient)
    (run : (peerRemoveAll.run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready (holders.withoutBase []) carriers loans temporary v :=
  HolderRemoval.all_peers keys peers stable anchors a b run

/-- Normal native session publication derives the selected peer's independent
base reference from the configured registry and actual funded base list. The
caller need not assume selected-slot membership; global initialization of the
stated registry and ledgers remains a separate obligation. -/
theorem original_session_configured_slot_protection
    (anchors : SlotPeerReferences holders loans w)
    (peers : holders.Funded carriers loans w)
    (coherent : Queues.RxCredits.BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (pid : PeerId) (a b : Ambient)
    (run : ((beginSession pid).run w).run a = .ok ((result,v),b)) :
    SlotPeerReferences holders loans v :=
  anchors.session_configured peers coherent configured pid a b run

/-- Native device-down clears publication slots and pays actual queued work
without losing key credit held by pending RX/TX packets. A normal return retains
both exact ledgers and independent slot protection; it does not assert immediate
key destruction or complete initialization of the supplied accounts. -/
theorem original_device_down_key_accounts
    (before : HolderDrain.Ready original carriers loans temporary w) (a b : Ambient)
    (run : (wgDown.run w).run a = .ok (((),v),b)) :
    HolderDrain.Ready original carriers loans temporary v :=
  (hoare_iff_run_ambient _ _ _).mp HolderShutdown.down w a () v b before run

/-- Native peer creation retains exact key credit and independently accounts
for its actual new peer reference. Freshness follows from the configured
registry; allocation refusal preserves the old holders. This is a native caller
cut, with initialized transport of its incoming ledgers still explicit. -/
theorem original_peer_creation_key_accounts (key : Key) (psk : Option Key)
    (keys : HolderAccount temporary w) (peers : holders.Funded carriers loans w)
    (stable : Queues.RxCredits.StableRx carriers w) (anchors : SlotPeerReferences holders loans w)
    (configured : ConfiguredIdentity.Inv w) (a b : Ambient)
    (run : ((peerCreate key psk).run w).run a = .ok ((result,v),b)) :
    match result with
    | .error _ => HolderDrain.Ready holders carriers loans temporary v
    | .ok pid => ∃ d,w.dev=some d ∧ pid=d.nextPeer ∧
        HolderDrain.Ready (Queues.RxCredits.HolderCreation.addBase holders
          (Queues.RxCredits.BaseCreation.owner w d)) carriers loans temporary v :=
  HolderPeerCreation.accounts key psk keys peers stable anchors configured a b run

/-- Native handshake consumers preserve the independent stamped protection of
every surviving peer with a published key slot, including failed authentication
and replay rejection. This is slot protection, not cryptographic authentication
or initialized key-credit accounting. -/
theorem original_handshake_consumers_slot_protection
    (anchors : SlotPeerReferences holders loans w) (msg : List UInt8) (response : Bool)
    (a b : Ambient)
    (run : (((if response then consumeResponse msg else consumeInitiation msg) : WG.M (Option PeerId)).run w).run a =
      .ok ((result,v),b)) : SlotPeerReferences holders loans v := by
  cases response with
  | false => exact (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.consume_initiation msg) w a result v b anchors run
  | true => exact (hoare_iff_run_ambient _ _ _).mp (SlotAnchors.consume_response msg) w a result v b anchors run

/-- Actual peer lookup followed by native configuration preserves exact key
credit on both ordinary and removal arms. Keepalive staging, allowed-IP error
cleanup, slot clearing, work drains and caller payment are included. The
independent initialized holder and allocation premises remain visible. -/
theorem original_lookup_configuration_key_accounts
    (key : Key) (attrs : PeerAttrs) (flags : UInt32) (psk : Option Key)
    (before : HolderKeepalive.Ready temporary w) (peers : holders.Funded carriers loans w)
    (stable : Queues.RxCredits.StableRx carriers w) (anchors : SlotPeerReferences holders loans w)
    (coherent : Queues.RxCredits.BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w)
    (a middle b : Ambient)
    (lookup : ((pubkeyLookup key).run w).run a=.ok ((some pid,u),middle))
    (run : ((Configuration.peerConfigUpdateSource attrs (some pid) flags psk pid).run u).run middle=
      .ok ((result,v),b)) : HolderAccount temporary v :=
  HolderConfiguration.lookup_update key attrs flags psk before peers stable anchors coherent configured
    a middle b lookup run

/-- The complete native peer command retains exact key credit through actual
creation, lookup, strict acquisition, both update arms and early cleanup. No
intermediate caller-funding assumption is supplied; initialized transport of
the stated entry boundary remains to be established. -/
theorem original_peer_command_key_accounts (attrs : PeerAttrs)
    (before : HolderConfiguration.Entry temporary carriers loans w) (a b : Ambient)
    (run : ((WG.setPeerCmd attrs).run w).run a=.ok ((result,v),b)) : HolderAccount temporary v :=
  (hoare_iff_run_ambient _ _ _).mp (HolderConfiguration.command attrs) w a result v b before run

/-- A peer with a published key slot has independent stamped peer protection
when actual slot liveness, configured registry coherence and funded base
alignment hold. Peer credit does not supply key credit; initialized transport
of these boundary carriers remains a separate obligation. -/
theorem live_published_slots_have_peer_protection
    (live : KeySlotLiveness.Inv w) (funded : holders.Funded carriers loans w)
    (coherent : Queues.RxCredits.BaseCoherence.Inv w) (configured : ConfiguredIdentity.Inv w) :
    SlotPeerReferences holders loans w :=
  KeySlotLiveness.references live funded coherent configured

/-- Native single and bulk peer removal cannot leave a dead surviving peer
with published key slots outside the explicit incoming removal exceptions.
The make-dead interval is discharged by actual slot clear before work drains
and final peer payment; retained packet references are not claimed destroyed. -/
theorem original_removal_slot_liveness (word : Option PeerId) :
    Preserves (KeySlotLiveness.InvExcept pending) (peerRemove word) ∧
    Preserves (KeySlotLiveness.InvExcept pending) peerRemoveAll :=
  ⟨KeySlotLiveness.remove_peer word,KeySlotLiveness.all_peers⟩

/-- Native creation starts with empty key slots, while successful session
publication and responder confirmation preserve the relation between live
peers and published key slots. These are actual source contracts; the whole
initialized caller carrier is not assumed or asserted here. -/
theorem original_publication_slot_liveness (key : Key) (psk : Option Key)
    (pid : PeerId) (kid : KeypairId) :
    Preserves (KeySlotLiveness.InvExcept pending) (peerCreate key psk) ∧
    Preserves (KeySlotLiveness.InvExcept pending) (beginSession pid) ∧
    Preserves (KeySlotLiveness.InvExcept pending) (receivedWithKeypair pid kid) :=
  ⟨KeySlotLiveness.create key psk,KeySlotLiveness.session pid,KeySlotLiveness.confirmation pid kid⟩

/-- The original peer command preserves live publication through creation,
removal, cached keepalive writes, staging and early-error cleanup. This native
boundary closes configuration transport of slot liveness; initialized holder
and reference-credit closure remain separate obligations. -/
theorem original_configuration_slot_liveness (attrs : PeerAttrs) :
    Preserves (KeySlotLiveness.InvExcept pending) (setPeerCmd attrs) :=
  KeySlotLiveness.config_command attrs

/-- Actual receive admission, handshake completion and selected timer callbacks
retain live published slots. This includes native staging and refusal arms;
normal callback transport supplies neither authentication nor eventual drain. -/
theorem original_receive_timer_slot_liveness (msg : List UInt8) (src : SkbSource)
    (pid : PeerId) (timer : PeerTimer) :
    Preserves (KeySlotLiveness.InvExcept pending) (wgReceive msg src) ∧
    Preserves (KeySlotLiveness.InvExcept pending) WG.receiveStep ∧
    Preserves (KeySlotLiveness.InvExcept pending) (timerCallback pid timer) :=
  ⟨KeySlotLiveness.receive msg src,KeySlotLiveness.receive_step,KeySlotLiveness.timer pid timer⟩

/-- Native device configuration, lifecycle clearing and data completion retain
live published slots through cached writes, disposal and actual peer payments.
Fresh creation starts with empty peers. This is native boundary transport;
whole-run key-credit accounting and eventual retirement remain separate. -/
theorem original_device_data_slot_liveness (attrs : DeviceAttrs) (pid : PeerId)
    (pkt : RxPacket) (endpoint : Endpoint) :
    Preserves (KeySlotLiveness.InvExcept pending) (wgSetDevice attrs) ∧
    Preserves (KeySlotLiveness.InvExcept pending) wgDown ∧
    Preserves (KeySlotLiveness.InvExcept pending) (consumeDataDone pid pkt endpoint) ∧
    Preserves (KeySlotLiveness.InvExcept pending) (txStep pid) :=
  ⟨KeySlotLiveness.set_device attrs,KeySlotLiveness.down,
    KeySlotLiveness.consume_done pid pkt endpoint,KeySlotLiveness.tx_step pid⟩

/-- Actual worker scheduling, receive-stack callbacks and deferred timer/work
calls preserve live published key slots. The recorded source choices and stop
paths are retained; this safety contract does not turn dispatch fairness into
reference disposal or assert initialized credit ownership. -/
theorem original_scheduled_slot_liveness (stack : Option Worker)
    (call : Lifetimes.EnvDeferredCall) :
    Preserves (fun w : World=>KeySlotLiveness.InvExcept pending w.wg) (Env.schedule stack) ∧
    Preserves (fun w : World=>KeySlotLiveness.InvExcept pending w.wg) call.original :=
  ⟨KeySlotScheduler.schedule stack,KeySlotDeferred.original call⟩

/-- The original initialized runner derives independent stamped peer
protection for every surviving published key slot. Native configuration,
receive, cached writes, timer drains and deletion are discharged; no incoming
slot, peer-funding or coverage invariant is assumed. This is peer protection,
not the still-separate exact key-reference account. -/
theorem initialized_published_slots_have_peer_protection (trace : Runner.Trace) (placeholders : Bool)
    (run : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) :
    ∃carriers holders,holders.Funded carriers [] w.wg ∧ Queues.RxCredits.StableRx carriers w.wg ∧
      SlotPeerReferences holders [] w.wg :=
  KeySlotInitialized.slot_protection trace placeholders run

/-- A successful shared campaign-journal execution derives live published
slots at its actual returned World. The World is retained through the existing
runner result callback; the actual event journal and source execution agree.
This initialized carrier does not assert eventual reference disposal. -/
theorem initialized_shared_journal_slot_liveness (trace : Runner.Trace) (placeholders : Bool)
    (run : Leanux.Proofs.Logged.runPrefixOuter (TransmitSecurity.Journal.execute trace placeholders) []=(.ok result,h)) :
    ∃w,Leanux.Proofs.Logged.runPrefixOuter (Queues.RoutingJoint.executeTraceWith
      (TransmitSecurity.Driver.syscallObserved TransmitSecurity.Journal.hooks)
      (fun j w=>(j,w)) trace placeholders) []=(.ok (result,w),h) ∧ KeySlotInitialized.JournalInv h w :=
  KeySlotInitialized.journal_endpoint trace placeholders run

/-- The actual device peer-list stage retains exact key credit together with
its independent peer/slot support for each following command. Slot protection
is derived at each boundary from liveness and funded base references; whole
initialized key-credit transport remains an explicit separate obligation. -/
theorem original_peer_list_joint_accounts (attrs : DeviceAttrs) :
    Preserves (HolderBoundary.Entry temporary carriers loans) (Configuration.devicePeersSource attrs) :=
  HolderBoundary.peer_list attrs

/-- The original complete device command preserves exact key credit and its
independent peer/slot support through static-key conflict deletion, bulk peer
replacement, expiry, staging and all peer commands. Unpublication and expiry
are not treated as reference disposal. The initialized account closure is a
separate obligation, rather than a conclusion inferred from peer funding. -/
theorem original_device_joint_accounts (attrs : DeviceAttrs) :
    Preserves (HolderBoundary.Entry temporary carriers loans) (wgSetDevice attrs) :=
  HolderBoundary.device attrs

/-- Native TX disposal and handshake worker iterations transport exact key
credit on the existing scheduler accounting cut. Physical TX separation and
independent slot protection are derived at the real dequeue; authentication,
replay refusal and the actual peer payments retain the same key account.
Initialized scheduler and RX/NAPI closure remain separate obligations. -/
theorem original_tx_handshake_joint_accounts (pid : PeerId) :
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe
      (Queues.RxHistory.mixed (Lifetimes.txIterPrefix pid
        (Leanux.Proofs.Logged.liftPrefix (Env.condResched .txWorker)))) ∧
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe Origins.HistoryAdapters.receiveIteration :=
  ⟨HolderScheduled.tx pid,HolderScheduled.handshake⟩

/-- Actual replay-window writes and decryption-rejection invalidation do not
create or lose key references. This ownership projection assumes neither
successful authentication nor a well-shaped replay bitmap; a Stop has no
claimed successor state. -/
theorem original_replay_decrypt_key_accounts (kid : KeypairId) (nonce : Nat) (pkt : RxPacket) :
    Preserves (HolderAccount temporary) (counterValidate kid nonce) ∧
    Preserves (HolderAccount temporary) (decryptPacket pkt) :=
  ⟨HolderReplay.counter kid nonce,HolderReplay.decrypt pkt⟩

/-- Every normally completed original RX poll conserves exact key credit:
its actual selected packet transfers one allocation-stamped reference into
the poll local, replay/confirmation and GRO retain it, and cleanup pays it.
Independent physical, session, slot and peer funding are explicit incoming
support; initialized global key accounting is a separate obligation. -/
theorem original_rx_poll_joint_key_account (pid budget : Nat)
    (funded : Queues.RxCredits.DurableHolders.Boundary initial loans w.wg)
    (keys : HolderAccount temporary w.wg)
    (support : HolderPoll.Support sessions locals active w.wg)
    (run : (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)).run w=.ok (result,v)) :
    HolderAccount temporary v.wg ∧ HolderPoll.Support sessions locals active v.wg :=
  HolderPoll.normal pid budget funded keys support run

/-- Actual decrypt-worker and NAPI iterations conserve exact key credit
through every original poll placement. The publication peer loan remains
separately funded across IRQ callbacks; live-slot protection derives its
safe final payment. This joins the existing scheduler account and history,
with initialized global key accounting still a separate obligation. -/
theorem original_decrypt_napi_joint_key_accounts :
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe Queues.RxHistory.decryptIteration ∧
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe Queues.RxHistory.napiSoftirq :=
  ⟨HolderScheduled.decrypt,HolderScheduled.softirq⟩

/-- The original complete scheduler conserves exact key credit across every
actual worker kind, NAPI callback, copied trial and rescheduling path. Its
worker contracts are discharged from source, including the detached active
TX batch and selected RX loan; no universal scheduler-coverage premise is
assumed. Deriving the incoming account from initialization remains separate. -/
theorem original_scheduler_joint_key_account (stack : Option Worker) (worker : Worker) :
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe (Queues.RxHistory.schedule stack) ∧
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe (Queues.RxHistory.nestedResched worker) :=
  ⟨HolderScheduled.schedule stack,HolderScheduled.nested worker⟩

/-- Original deferred send and timer waits conserve exact key credit through
recorded wheel selection, all five callbacks, actual queued work payments
and nested crypt/RX drains. Refused clear work repays only its own peer loan;
slot clearing is not conflated with final key deallocation. The incoming
account remains explicit until the initialized outer-source join. -/
theorem original_deferred_joint_key_accounts (j : UInt64) :
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe Queues.RxHistory.runSendWorkers ∧
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe (Queues.RxHistory.runTimers j) ∧
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe (Queues.RxHistory.runTimersPlaceholder j) ∧
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe Queues.RxHistory.afterXmit ∧
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe Queues.RxHistory.idleTimers ∧
    Leanux.Proofs.Logged.PrefixPreserves
      (HolderScheduled.Inv initial loans before temporary locals active)
      OwnerChecks.Safe Queues.RxHistory.afterAdvance :=
  ⟨HolderScheduled.send_all,HolderScheduled.runTimers initial loans before j,
    HolderScheduled.runTimersPlaceholder initial loans before j,HolderScheduled.after_xmit,
    HolderScheduled.idleTimers initial loans before,HolderScheduled.afterAdvance initial loans before⟩

/-- Native fixture injection preserves exact key credit through actual
admission, NET_RX entry and the complete crypt drain. The same final guard
establishes the empty receive ledger; key credit is derived independently of
that emptiness. The input account is explicit pending outer initialization. -/
theorem original_inject_joint_key_account
    (entry : HolderOuter.Inv carriers loans temporary locals active h w)
    (run : Leanux.Proofs.Logged.runPrefix (Queues.RxHistory.inject family port msg tos ll dest) w h=
      (.ok (result,v),k)) : HolderOuter.Inv [] loans temporary locals active k v :=
  HolderOuter.inject_normal entry run

/-- Native flood processing conserves exact key credit for every ordered
packet occurrence and its inline poll, including partial placeholder drains.
The source outcome chooses the remaining receive ledger; no output funding
or drain-completeness premise is substituted for the actual execution. -/
theorem original_flood_joint_key_account
    (entry : HolderOuter.Inv carriers loans temporary locals active h w)
    (run : Leanux.Proofs.Logged.runPrefix (Queues.RxHistory.flood count port family messages) w h=
      (.ok (result,v),k)) :
    ∃next,Queues.RxCredits.FloodAccount.Outcome carriers next count port family messages w v h k result ∧
      HolderOuter.Inv next loans temporary locals active k v := HolderOuter.flood_normal entry run

/-- Original mixed TX/RX batches conserve exact key credit across actual
packetization, admission, inline polling and deferred work. The native source
certificate identifies the final receive ledger and preserves repeated equal
packets as distinct occurrences. Initialized outer closure remains separate. -/
theorem original_batch_joint_key_account (entries : List Env.BatchItem)
    (entry : HolderOuter.Inv carriers loans temporary locals active h w)
    (run : Leanux.Proofs.Logged.runPrefix (Queues.RxHistory.batch entries) w h=(.ok (result,v),k)) :
    ∃next,Queues.RxCredits.BatchAccount.Outcome carriers next entries w v h k result ∧
      HolderOuter.Inv next loans temporary locals active k v := HolderOuter.batch_normal entries entry run

/-- Actual device configuration and shutdown conserve allocation-stamped key
credit, including slot unpublication with retained packet references. The
native calls supply their own peer/slot transport; the incoming outer account
remains explicit until the complete initialized syscall composition. -/
theorem original_configuration_lifecycle_key_accounts (attrs : DeviceAttrs) :
    Leanux.Proofs.Logged.PrefixPreserves (HolderOuter.Inv carriers loans temporary [] [])
      OwnerChecks.Safe (Queues.RxHistory.mixed (Leanux.Proofs.Logged.liftWGObserver (Lifetimes.wgSetDevicePrefix attrs))) ∧
    Leanux.Proofs.Logged.PrefixPreserves (HolderOuter.Inv carriers loans temporary [] [])
      OwnerChecks.Safe (Queues.RxHistory.audit Lifetimes.envWgUpAudit) ∧
    Leanux.Proofs.Logged.PrefixPreserves (HolderOuter.Inv carriers loans temporary [] [])
      OwnerChecks.Safe (Queues.RxHistory.audit Lifetimes.envWgDownAudit) ∧
    Leanux.Proofs.Logged.PrefixPreserves (HolderOuter.Inv carriers loans temporary [] [])
      OwnerChecks.Safe (Queues.RxHistory.audit Lifetimes.envNetnsCleanupAudit) :=
  ⟨HolderOuter.configure attrs,HolderOuter.up,HolderOuter.down,HolderOuter.cleanup⟩

/-- Guarded device deletion reaches an absent device with no remaining
receive ledger and no key allocations. This exact source endpoint requires
empty caller-local key and packet ledgers; it does not promise that arbitrary
outstanding references survive device destruction. -/
theorem original_device_delete_key_account
    (entry : HolderOuter.Inv carriers [] [] [] [] h w)
    (run : Leanux.Proofs.Logged.runPrefix (Queues.RxHistory.audit Lifetimes.envWgDeleteAudit) w h=
      (.ok (result,v),k)) :
    carriers=[] ∧ v.wg.dev=none ∧ HolderOuter.Inv carriers [] [] [] [] k v :=
  HolderOuter.delete_normal entry run

/-- Full and stepped native dump syscalls preserve exact key credit while
exchanging their actual peer cursor loans. A cursor payment cannot erase a
peer with published key slots because the actual funded base/caller anchor
is independent of that cursor occurrence. Initial cursor emptiness and dump
completion are unnecessary; outer initialization remains a separate join. -/
theorem original_dump_joint_key_accounts (ref : DeviceRef) :
    Leanux.Proofs.Logged.PrefixPreserves (HolderOuter.Inv carriers loans temporary [] [])
      OwnerChecks.Safe (Queues.RxHistory.syscallDispatch (.wgGet ref)) ∧
    Leanux.Proofs.Logged.PrefixPreserves (HolderOuter.Inv carriers loans temporary [] [])
      OwnerChecks.Safe (Queues.RxHistory.syscallDispatch (.wgGetStart ref)) ∧
    Leanux.Proofs.Logged.PrefixPreserves (HolderOuter.Inv carriers loans temporary [] [])
      OwnerChecks.Safe (Queues.RxHistory.syscallDispatch .wgGetRecv) :=
  ⟨HolderOuter.dump_get ref,HolderOuter.dump_start ref,HolderOuter.dump_receive⟩


/-- Every normal initialized Runner endpoint accounts exactly for every
keypair reference using actual published slots, queued TX batches and queued
RX packets. No initial ownership, credit, slot-liveness or source-coverage
premise is assumed. Residual packet holders remain explicit retirement debts;
normal acceptance does not imply that all references have drained. -/
theorem initialized_exact_key_reference_account (trace : Runner.Trace) (placeholders : Bool)
    (run : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) : HolderAccount [] w.wg :=
  HolderInitialized.account trace placeholders run

/-- Acceptance by the original executable Runner yields its same actual
endpoint and exact native key-holder account. Device-ring aliases and work
notifications add no credit; the theorem assumes no separate ledger invariant. -/
theorem accepted_exact_key_reference_account (trace : Runner.Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h,Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h) ∧ HolderAccount [] w.wg :=
  HolderInitialized.accepted trace placeholders run


/-- Given actual queued-clear dispatch after a normal initialized execution,
the selected peer's three slots are cleared and every remaining key reference
is exactly accounted for by native packet/slot holders. Completion of that
worker is the explicit progress premise; elapsed time alone is insufficient. -/
theorem initialized_clear_worker_reference_retirement (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (dispatch : Env.runOneClearWorker.run w=.ok ((),v)) :
    HolderAccount [] v.wg ∧ ∃d pid,w.wg.dev=some d ∧ pid∈d.clearWorkQueue ∧
      SlotsCleared pid v.wg ∧ Retains w.wg v.wg :=
  InitializedRetirement.clear_worker trace placeholders initialized dispatch

/-- After initialization, a selected TX batch holding the sole remaining
reference retires its key allocation when the actual native worker consumes
that batch. A true normal worker return is the explicit scheduling/readiness
premise; both encrypted and DEAD batches use this same disposal path. -/
theorem initialized_final_tx_reference_removes_key (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (allocation : Credits.Allocation)
    (projected : durableLoans w.wg=some loans)
    (last : (loans.map (·.allocation)).count allocation=1)
    (pid : PeerId) (p : Peer) (items : List SkbId) (headId : SkbId) (head : DataPacket)
    (peer : peerAt w.wg pid=some p) (queued : p.txQueue.all.head?=some items)
    (first : items.head?=some headId) (packet : Queues.TxDisposition.txPackets w.wg headId=some head)
    (key : head.keypair=allocation.slot) (b : Ambient)
    (worker : ((txStep pid).run w.wg).run w.ambient=.ok ((true,v),b)) :
    keyAt v allocation.slot=none :=
  InitializedRetirement.final_tx trace placeholders initialized allocation projected last
    pid p items headId head peer queued first packet key b worker

/-- Native RX cleanup pays the saved packet's actual final key credit and
leaves its allocation absent after the subsequent peer release and skb free.
The exact incoming cleanup-cut ledger and last-credit condition are explicit;
this local statement does not assume that a fair TX schedule also drains RX. -/
theorem original_final_rx_cleanup_removes_key (allocation : Credits.Allocation) (remaining : Credits.Ledger)
    (account : Credits.Exact (allocation::remaining) w) (last : allocation∉remaining)
    (id : SkbId) (pkt : RxPacket) (flag : Bool) (key : pkt.keypair=allocation.slot) (a b : Ambient)
    (run : ((Queues.RxCredits.cleanup id pkt flag).run w).run a=.ok (((),v),b)) :
    keyAt v allocation.slot=none := FinalDisposal.rx allocation remaining account last id pkt flag key a b run

/-- Once the abstract allocation is removed, neither the native key getter
nor its reference-acquisition wrapper can return a key from that state. This
is store retirement, with no claim about physical-memory zeroisation. -/
theorem removed_key_cannot_be_obtained {id : KeypairId} (removed : keyAt w id=none) :
    (∀a b k v,((getKeypair id).run w).run a≠.ok ((k,v),b)) ∧
    (∀a b out v,((keypairGet (some id)).run w).run a≠.ok ((out,v),b)) :=
  ⟨fun a b _ _ run=>InitializedRetirement.removed_cannot_read removed a b run,
    fun a b _ _ run=>InitializedRetirement.removed_cannot_acquire removed a b run⟩


/-- The actual zero-key timer callback leaves a live peer queued for clear
work, including the coalesced queue arm. It keeps the initialized exact key
account and original key store; the timer callback itself does not erase keys. -/
theorem initialized_zero_timer_queues_clear (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (pid : PeerId) (p : Peer) (alive : p.isDead=false)
    (found : peerAt w.wg pid=some p) (b : Ambient)
    (run : ((expiredZeroKeyMaterial pid).run w.wg).run w.ambient=.ok (((),v),b)) :
    HolderAccount [] v ∧ KeyTimes.keypairStore v=KeyTimes.keypairStore w.wg ∧
      ∃d,v.dev=some d ∧ pid∈d.clearWorkQueue :=
  ZeroTimerQueued.initialized_callback trace placeholders initialized pid p alive found b run

/-- Conditional operational retirement executes the actual zero-key callback
and that peer's actual flushed clear work: all three slots are cleared while
remaining packet references stay exactly funded. These two native runs are
explicit progress premises, not a fairness theorem inferred from elapsed time. -/
theorem initialized_timer_worker_clears_slots (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (pid : PeerId) (p : Peer) (alive : p.isDead=false)
    (found : peerAt w.wg pid=some p) (b c : Ambient)
    (fired : ((expiredZeroKeyMaterial pid).run w.wg).run w.ambient=.ok (((),u),b))
    (dispatched : ((runFlushedClearWork pid).run u).run b=.ok (((),v),c)) :
    (∃d,u.dev=some d ∧ pid∈d.clearWorkQueue) ∧ HolderAccount [] v ∧ SlotsCleared pid v ∧ Retains u v :=
  ZeroTimerQueued.initialized_callback_then_worker trace placeholders initialized pid p alive found b c fired dispatched

/-- The actual recorded wheel dispatch queues a live peer's zero-key clear
work through all worker, address and bucket guards. Initialization and the
peer's published slot derive liveness and exact reference funding; normal
dispatch is the explicit clock/record progress premise. -/
theorem initialized_recorded_zero_dispatch (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (kind : Worker) (pid : PeerId) (entry : WheelEntry) (prior : Option UInt64)
    (p : Peer) (found : peerAt w.wg pid=some p) (published : HasKeySlot p)
    (run : (Leanux.Proofs.Logged.timerDispatchUnit kind pid .zeroKeyMaterial entry prior).run w=.ok ((),v)) :
    HolderAccount [] v.wg ∧ ZeroTimerDispatch.Queued pid v.wg :=
  ZeroTimerDispatch.initialized_dispatch trace placeholders initialized kind pid entry prior p found published run

/-- After the actual recorded zero-key timer dispatch and that peer's native
flushed clear work, its publication slots are empty and remaining packet
references stay exactly funded. Both concrete executions are required: queue
membership or elapsed wall-clock time alone supplies no worker-progress claim. -/
theorem initialized_recorded_timer_worker_retirement (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (kind : Worker) (pid : PeerId) (entry : WheelEntry) (prior : Option UInt64)
    (p : Peer) (found : peerAt w.wg pid=some p) (published : HasKeySlot p)
    (fired : (Leanux.Proofs.Logged.timerDispatchUnit kind pid .zeroKeyMaterial entry prior).run w=.ok ((),u))
    (b : Ambient) (worker : ((runFlushedClearWork pid).run u.wg).run u.ambient=.ok (((),v),b)) :
    ZeroTimerDispatch.Queued pid u.wg ∧ HolderAccount [] v ∧ SlotsCleared pid v ∧ Retains u.wg v := by
  obtain ⟨account,queued⟩ := ZeroTimerDispatch.initialized_dispatch trace placeholders initialized
    kind pid entry prior p found published fired
  exact ⟨queued,(hoare_iff_run_ambient _ _ _).mp (flushed_holders pid []) u.wg u.ambient () v b account worker,
    flushed_retirement pid u.wg v u.ambient b worker⟩

/-- Successive original RX peek, readiness, read and dequeue calls move the
selected packet's actual key occurrence into one detached local credit.
Initialization derives both physical uniqueness and exact key funding; these
four native runs expose the concrete poll-selection progress condition. -/
theorem initialized_rx_selection_key_credit (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (pid id : Nat) (pkt : RxPacket) (b c d e : Ambient)
    (peek : ((Queues.peekRxQueue pid).run w.wg).run w.ambient=.ok ((some id,u),b))
    (test : ((NativeRxSelection.ready (some id)).run u).run b=.ok ((true,t),c))
    (read : ((getRxSkb id).run t).run c=.ok ((pkt,s),d))
    (drop : ((Queues.dropRxQueue pid).run s).run d=.ok (((),v),e)) :
    ∃allocation,pkt.keypair=allocation.slot ∧ HolderAccount [allocation] v ∧
      RxDetached id v ∧ pkt.state≠.uncrypted ∧ NativeRxSelection.wire v=NativeRxSelection.wire w.wg :=
  NativeRxSelection.initialized_selected trace placeholders initialized pid id pkt b c d e peek test read drop

/-- An initialized queued DEAD RX packet holding the sole key reference
retires its allocation after the actual poll selection, recorded DEAD-state
comparison and literal cleanup. All native runs share their intermediate
states; progress and the sole-holder count are explicit, with no incoming
cleanup-cut invariant. This is the DEAD path, not a whole-poll fairness claim. -/
theorem initialized_final_dead_rx_reference_removes_key (trace : Runner.Trace) (placeholders : Bool)
    (initialized : Leanux.Proofs.Logged.runPrefixOuter (Queues.RxCredits.RunnerAccount.observed trace placeholders) []=
      (.ok (result,w),h)) (allocation : Credits.Allocation) (projected : durableLoans w.wg=some loans)
    (last : (loans.map (·.allocation)).count allocation=1)
    (pid id : Nat) (pkt : RxPacket) (owner : pkt.peer=pid) (key : pkt.keypair=allocation.slot)
    (dead : pkt.state=.dead) (b c d e f g : Ambient)
    (peek : ((Queues.peekRxQueue pid).run w.wg).run w.ambient=.ok ((some id,u),b))
    (test : ((NativeRxSelection.ready (some id)).run u).run b=.ok ((true,t),c))
    (read : ((getRxSkb id).run t).run c=.ok ((pkt,s),d))
    (drop : ((Queues.dropRxQueue pid).run s).run d=.ok (((),v),e))
    (stateCheck : ((branch .rxPollNotCrypted (pkt.state != .crypted) : WG.M Bool).run v).run e=
      .ok ((skip,z),f))
    (dispose : ((do
      keypairPut (some pkt.keypair) false
      peerPut (some pid)
      _←branch .rxPollFree true
      freeRxSkb id : WG.M Unit).run z).run f=.ok (((),final),g)) :
    skip=true ∧ keyAt final allocation.slot=none :=
  FinalRxSelection.initialized_dead trace placeholders initialized allocation projected last
    pid id pkt owner key dead b c d e f g peek test read drop stateCheck dispose

end Leanux.Proofs.WG.RetirementSecurity
