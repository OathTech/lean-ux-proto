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

/-! Campaign 3, T6: local original-operation retirement contracts. The
initialized key-reference ledger, complete caller coverage and conditional
timer/worker progress remain separate obligations. No complete T6 outcome is
claimed by these exports. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing

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

end Leanux.Proofs.WG.RetirementSecurity
