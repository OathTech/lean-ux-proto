import Leanux.Proofs.WG.TransmitSecurity.NonceStagingSafety
import Leanux.Proofs.WG.TransmitSecurity.NonceInitialized
import Leanux.Proofs.WG.TransmitSecurity.NonceTimers
import Leanux.Proofs.WG.TransmitSecurity.NonceHandshakeSafety
import Leanux.Proofs.WG.TransmitSecurity.WireNonce
import Leanux.Proofs.WG.TransmitSecurity.EncryptBinding
import Leanux.Proofs.WG.TransmitSecurity.Rekey

/-! Campaign 3, T1 initialized counter reservations and local AEAD contracts.
Transport from reservation through every actual AEAD invocation remains open. -/
namespace Leanux.Proofs.WG.TransmitSecurity
open Leanux Leanux.WG Leanux.Proofs.Logged

/-- Security: recording every native staging increment preserves the original
success or Stop exactly; rejected batches cannot be hidden by an observer that
only records successful sends. This is source erasure, not initialized safety. -/
theorem original_staging_nonce_observer (pid : PeerId) :
    ErasesStatePrefix (Nonce.stagingObserved pid) (sendStagedPackets pid) :=
  Nonce.stagingObserved_erases pid

/-- Security: an original nonce increment cannot reuse an allocation already
in the journal, assuming the explicit sending-counter invariant at entry.
The updated invariant and failure-prefix journal are preserved; initialized
caller coverage is a separate obligation. -/
theorem original_nonce_reservation (slot : KeypairId) :
    StatePrefixEnsures (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.reserveObserved slot) (fun _ h w _ => Nonce.Inv (Nonce.view w) h) :=
  Nonce.reserveObserved_safe slot

/-- Security: the nonce observer refers to the actual get/increment operation;
adding its receipt changes neither the native outcome nor either native state. -/
theorem original_nonce_reservation_erases (slot : KeypairId) :
    ErasesStatePrefix (Nonce.reserveObserved slot) (Nonce.reserveNative slot) :=
  Nonce.reserveObserved_erases slot

/-- Security: a complete original staged-send invocation cannot repeat any
recorded nonce allocation under its allocation-stamped sending key, assuming
the explicit entry invariant. Queue refusal and later Stop retain allocations;
caller initialization and allocation-to-AEAD transport are separate obligations. -/
theorem original_staging_nonce_safety (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.stagingObserved pid) :=
  Nonce.stagingObserved_safe pid

/-- Security: native key creation cannot reset the nonce history of an existing
allocation identity. Its fresh global stamp preserves the supplied allocation
invariant even if a device-local slot is reused. This is normal-call preservation. -/
theorem original_creation_nonce_safety (peer : Option PeerId)
    (history : List Nonce.Allocation) :
    Framing.Preserves (fun w => Nonce.Inv (Nonce.view w) history) (keypairCreate peer) :=
  Nonce.create_preserves peer history

/-- Security: the real runner starts with an empty sending-allocation history
and no active key, for either fixture flag. This establishes initialization,
not preservation by all later runner operations. -/
theorem initialized_nonce_projection (net bare : Bool) :
    Nonce.Inv (Nonce.view (Runner.initialWG net bare)) [] := by
  rw [Nonce.initial_view]
  exact Nonce.initial 0

/-- Security: distinct admitted sending counters cannot collide after the
native 64-bit serialization used by AEAD. The actual admission bound is enough;
no unbounded-Nat-to-wire injectivity assumption is used. Packet provenance and
single-use transport to encryption remain separate obligations. -/
theorem original_admitted_nonce_encoding {n m : Nat}
    (hn : n < REJECT_AFTER_MESSAGES) (hm : m < REJECT_AFTER_MESSAGES)
    (same : counterNonce n = counterNonce m) : n = m :=
  admitted_aead_nonce_injective hn hm same

/-- Security: each native encryption invocation records at most one actual
AEAD result with its original packet, preparation and key read; the observer
preserves every success and Stop. This local source coverage does not establish
that the worker selects each admitted packet only once. -/
theorem original_encryption_receipts (slot : KeypairId) (pkt : DataPacket)
    (w : World) (h : List Encryption.Receipt) :
    ErasesPrefix (Encryption.observe Env.checksumHelp slot pkt)
      (encryptPacket Env.checksumHelp slot pkt) ∧
    ∃ suffix, (runPrefix (Encryption.observe Env.checksumHelp slot pkt) w h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix,
        r.slot = slot ∧ r.packet = pkt ∧ r.Valid Env.checksumHelp :=
  ⟨Encryption.observe_erases Env.checksumHelp slot pkt,
    Encryption.observe_receipts Env.checksumHelp slot pkt w h⟩

/-- Security: native encryption uses the entry-resident key in the selected
slot and the packet's assigned nonce for both header and AEAD. Allocation,
checksum and padding preparation cannot substitute a different key. The source
premise is actual encryption success; staging authorization and queue provenance
must still connect that slot and packet to their earlier selection. -/
theorem original_ciphertext_key_binding (slot : KeypairId) (pkt : DataPacket)
    (w v : World) (bytes : List UInt8)
    (success : (encryptPacket Env.checksumHelp slot pkt).run w = .ok (some bytes,v)) :
    ∃ (k : Keypair) (p : Encryption.Prepared), Encryption.keyAt w slot = some k ∧
      bytes = dataMessage k.remoteIndex pkt.nonce k.sending.key
        (p.inner.bytes ++ List.replicate p.padding 0) :=
  Encryption.original_ciphertext_binding slot pkt w v bytes success

/-- Security: the rekey observer records only the actual guarded request to
the native handshake-queue helper, retaining that request through a later Stop.
A request does not promise that the helper's timeout/dead/pending guards queue
or transmit a handshake. -/
theorem original_rekey_requests (pid : PeerId) (w : WGWorld) (a : Ambient)
    (h : List Rekey.Request) :
    ErasesStatePrefix (Rekey.observe pid) (keepKeyFresh pid) ∧
    ∃ suffix, (runWGPrefix (Rekey.observe pid) w a h).2 = h ++ suffix ∧
      suffix.length ≤ 1 ∧ ∀ r ∈ suffix, r.peer = pid ∧ r.Valid :=
  ⟨Rekey.observe_erases pid,Rekey.observe_receipts pid w a h⟩

/-- Security: a valid current sending key above the rekey count causes the
original freshness check to call the native handshake-queue helper. The exact
helper result or Stop is preserved; source-state lookup premises are explicit. -/
theorem original_rekey_count_request (pid : PeerId) (slot : KeypairId) (p : Peer) (k : Keypair)
    (w : WGWorld) (d : Device) (a : Ambient)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (current : p.keypairCurrent = some slot) (key : d.keypairs[slot]? = some k)
    (valid : k.sending.isValid = true) (past : REKEY_AFTER_MESSAGES < k.sendingCounter) :
    ((keepKeyFresh pid).run w).run a =
      ((sendQueuedHandshakeInitiation pid false).run w).run (Rekey.countChecked a k) := by
  exact (Rekey.observe_erases pid w a []).symm.trans
    (congrArg Prod.fst (Rekey.count_request pid slot p k w d a [] device peer current key valid past))

/-- Security: when the count arm does not trigger, a valid current initiator
key whose actual recorded age test expires requests native handshake work.
The source clock-test run is explicit, so no unrecorded wall-clock or latency
assumption replaces the C's age check. -/
theorem original_rekey_age_request (pid : PeerId) (slot : KeypairId) (p : Peer) (k : Keypair)
    (w : WGWorld) (d : Device) (a b : Ambient)
    (device : w.dev = some d) (peer : d.peers[pid]? = some p)
    (current : p.keypairCurrent = some slot) (key : d.keypairs[slot]? = some k)
    (valid : k.sending.isValid = true) (count : k.sendingCounter ≤ REKEY_AFTER_MESSAGES)
    (initiator : k.iAmTheInitiator = true)
    (expired : ((branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME).run w).run
      (Rekey.ageEntry a k) = .ok ((true,w),b)) :
    ((keepKeyFresh pid).run w).run a =
      ((sendQueuedHandshakeInitiation pid false).run w).run (CounterWindow.record b .freshSend true) := by
  exact (Rekey.observe_erases pid w a []).symm.trans
    (congrArg Prod.fst (Rekey.age_request pid slot p k w d a b [] device peer current key valid count initiator expired))

/-- Security: original session establishment preserves all prior sending
nonce allocations while assigning a new global identity to its new key. Key
rotation and reference release cannot reset a surviving allocation's counter. -/
theorem original_session_nonce_safety (pid : PeerId) (history : List Nonce.Allocation) :
    Framing.Preserves (fun w => Nonce.Inv (Nonce.view w) history) (beginSession pid) :=
  Nonce.Frames.begin_session pid history

/-- Security: native keepalive sending records every staging allocation and
preserves nonce non-reuse from the explicit entry invariant, including allocation
failure and later Stop. The observer changes no native result or state. -/
theorem original_keepalive_nonce_safety (pid : PeerId) :
    ErasesStatePrefix (Nonce.keepaliveObserved pid) (sendKeepalive pid) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.keepaliveObserved pid) :=
  ⟨Nonce.keepaliveObserved_erases pid,Nonce.keepaliveObserved_safe pid⟩

/-- Security: the original transmit entry retains non-reuse across routing,
staging and final peer release, including refusal and Stop. Its entry invariant
is explicit; this caller contract is not initialized driver closure or a claim
that admitted packets have already reached AEAD. -/
theorem original_transmit_nonce_safety (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    ErasesStatePrefix (Nonce.transmitObserved family addr packets mtu) (wgXmit family addr packets mtu) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.transmitObserved family addr packets mtu) :=
  ⟨Nonce.transmitObserved_erases family addr packets mtu,
    Nonce.transmitObserved_safe family addr packets mtu⟩

/-- Security: every original timer callback preserves sending nonce non-reuse
from the explicit entry invariant and records its actual keepalive allocations,
including before Stop. This callback claim does not assume a timer was due;
wheel selection and driver transport are separate obligations. -/
theorem original_timer_nonce_safety (pid : PeerId) (timer : PeerTimer) :
    ErasesStatePrefix (Nonce.timerObserved pid timer) (timerCallback pid timer) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.timerObserved pid timer) :=
  ⟨Nonce.timerObserved_erases pid timer,Nonce.timerObserved_safe pid timer⟩

/-- Security: the complete original handshake receive worker preserves sending
nonce non-reuse through actual session creation and keepalive staging, with
allocations retained before later Stop. The source observer is exact; the
entry invariant and remaining initialized driver coverage stay explicit. -/
theorem original_handshake_worker_nonce_safety :
    ErasesStatePrefix Nonce.Handshake.observed receiveStep ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      Nonce.Handshake.observed :=
  ⟨Nonce.Handshake.erases,Nonce.Handshake.safe⟩


/-- Security: original data consumption cannot reuse a sending nonce when
confirmation releases staged packets. Exact source erasure retains allocations
before later receive failure; the incoming nonce invariant remains explicit. -/
theorem original_receive_nonce_safety (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ErasesStatePrefix (Nonce.consumeObserved pid pkt ep) (consumeDataDone pid pkt ep) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup
      (Nonce.consumeObserved pid pkt ep) :=
  ⟨Nonce.consumeObserved_erases pid pkt ep,Nonce.consumeObserved_safe pid pkt ep⟩

/-- Security: the actual receive poll preserves sending nonce non-reuse,
including replies generated by the real IPv4 stack callback and every earlier
allocation before Stop. No callback-silence premise replaces those sends;
initialized driver transport of the entry invariant remains open. -/
theorem original_native_poll_nonce_safety (pid : PeerId) (budget : Nat) :
    ErasesPrefix (Nonce.nativePollObserved pid budget)
      (rxPoll pid budget (fun packets => packets.forM Env.deliverInner)) ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
      (Nonce.nativePollObserved pid budget) :=
  ⟨Nonce.nativePollObserved_erases pid budget,Nonce.nativePollObserved_safe pid budget⟩

/-- Security: actual softirq scheduling preserves the sending nonce history
through every selected receive poll and stack reply, including before Stop.
The explicit incoming invariant is not an initialized scheduler claim. -/
theorem original_softirq_nonce_safety :
    ErasesPrefix Nonce.softirqObserved Env.napiSoftirq ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup Nonce.softirqObserved :=
  ⟨Nonce.softirqObserved_erases,Nonce.softirqObserved_safe⟩

/-- Security: direct inline polling preserves nonce non-reuse through the
same native poll and stack reply paths; the source placement records and
failed-prefix allocations remain unchanged. -/
theorem original_inline_poll_nonce_safety :
    ErasesPrefix Nonce.inlinePollObserved Env.pollScheduledInline ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup Nonce.inlinePollObserved :=
  ⟨Nonce.inlinePollObserved_erases,Nonce.inlinePollObserved_safe⟩

/-- Security: an IRQ-exit receive poll cannot reset or reuse the sending nonce
history, including replies it causes. Actual placement selection is retained;
whole-run initialization remains a separate obligation. -/
theorem original_irq_exit_nonce_safety :
    ErasesPrefix Nonce.irqExitObserved Env.napiIrqExit ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup Nonce.irqExitObserved :=
  ⟨Nonce.irqExitObserved_erases,Nonce.irqExitObserved_safe⟩

/-- Security: every committed iteration of the native crypt/receive scheduler
preserves sending nonce non-reuse, including the encryption-before-TX path,
NAPI callbacks and allocations before Stop. Consistency trials on copied states
emit no allocations. The incoming invariant and whole-run initialization remain
explicit; packet transport to AEAD is a separate obligation. -/
theorem original_scheduler_nonce_safety (stack : Option Worker) :
    ErasesPrefix (Nonce.scheduleObserved stack) (Env.schedule stack) ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
      (Nonce.scheduleObserved stack) :=
  ⟨Nonce.scheduleObserved_erases stack, Nonce.scheduleObserved_safe stack⟩

/-- Security: both actual wheel passes preserve the nonce allocation history
through selected timer callbacks, send/clear workers and crypt scheduling,
including allocations before Stop. Native bucket/order guards remain present;
this is preservation from the explicit incoming invariant, not eventual timer
progress or initialized packet-to-AEAD transport. -/
theorem original_timer_pass_nonce_safety (j : UInt64) :
    (ErasesPrefix (Nonce.timersObserved j) (Env.runTimers j) ∧
      PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
        (Nonce.timersObserved j)) ∧
    (ErasesPrefix (Nonce.placeholderTimersObserved j) (Env.runTimersPlaceholder j) ∧
      PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
        (Nonce.placeholderTimersObserved j)) :=
  ⟨⟨Nonce.timersObserved_erases j, Nonce.timersObserved_safe j⟩,
    ⟨Nonce.placeholderTimersObserved_erases j, Nonce.placeholderTimersObserved_safe j⟩⟩

/-- Fixture injection preserves the sending nonce journal through the actual
receive and deferred worker sequence; stopped prefixes cannot reuse a reservation. -/
theorem original_injection_nonce_safety (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (Nonce.injectObserved family port msg tos ll dest) (Env.inject family port msg tos ll dest) ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup
      (Nonce.injectObserved family port msg tos ll dest) :=
  ⟨Nonce.injectObserved_erases family port msg tos ll dest,
    Nonce.injectObserved_safe family port msg tos ll dest⟩

/-- Every native fixture batch retains nonce non-reuse through its actual
transmit, receive, inline poll and deferred callbacks, from the visible entry invariant. -/
theorem original_batch_nonce_safety (items : List Env.BatchItem) :
    ErasesPrefix (Nonce.batchObserved items) (Env.batch items) ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup (Nonce.batchObserved items) :=
  ⟨Nonce.batchObserved_erases items,Nonce.batchObserved_safe items⟩

/-- Device configuration cannot reset a retained sending allocation's nonce
frontier; keepalive and staging callbacks append their actual reservations before Stop. -/
theorem original_configuration_nonce_safety (attrs : DeviceAttrs) :
    ErasesStatePrefix (Nonce.configDevice attrs) (wgSetDevice attrs) ∧
    StatePrefixPreserves (fun h w _ => Nonce.Inv (Nonce.view w) h) List.Nodup (Nonce.configDevice attrs) :=
  ⟨Nonce.configDevice_erases attrs,Nonce.configDevice_safe attrs⟩

/-- Bringing up the interface preserves nonce non-reuse through its actual
queued packets and keepalives; fixture routing never resets the sending frontier. -/
theorem original_interface_up_nonce_safety :
    ErasesPrefix Nonce.envUpObserved Env.wgUp ∧
    PrefixPreserves (fun h w => Nonce.Inv (Nonce.view w.wg) h) List.Nodup Nonce.envUpObserved :=
  ⟨Nonce.envUpObserved_erases,Nonce.envUpObserved_safe⟩

/-- Security: every typed initialized Runner trace reserves each pair of key
allocation stamp and sending nonce at most once, including reservations in a
failed prefix. Actual fixture initialization discharges the entry invariant;
exact source erasure retains JSON and indexed Stop for either placeholder mode.
Connecting queued packet occurrences and AEAD invocations remains separate. -/
theorem initialized_nonce_reservations (trace : Runner.Trace) (placeholders : Bool) :
    ErasesOuter (Nonce.executeObserved trace placeholders) (Runner.executeTrace trace placeholders) ∧
    List.Nodup (runPrefixOuter (Nonce.executeObserved trace placeholders) []).2 :=
  ⟨Nonce.executeObserved_erases trace placeholders,Nonce.initialized_safe trace placeholders⟩

end Leanux.Proofs.WG.TransmitSecurity
