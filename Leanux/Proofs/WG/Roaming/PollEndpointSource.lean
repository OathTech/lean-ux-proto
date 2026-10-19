import Leanux.Proofs.WG.Roaming.PollCallbackSource
import Leanux.Proofs.WG.Roaming.PollEndpointModel
import Leanux.Proofs.WG.Roaming.PublicationClaims

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- One unchanged iteration of the current original poll, including GRO and cleanup. -/
def pollStep (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → Leanux.M Unit)
    (_ : Nat) (state : PollState) : Leanux.M (ForInStep PollState) :=
  PollHookRules.stepWith (fun {_} action=>action)
    (fun p pkt ep=>liftWG (consumeDataDone p pkt ep)) (napiGroReceive toStack)
    pid budget 0 state

def pollFinish (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → Leanux.M Unit)
    (state : PollState) : Leanux.M Nat :=
  PollHookRules.finishWith (fun {_} action=>action) (napiGroFlushAll toStack) pid budget state

/-- Exact current-source factorization, retaining every callback and error. -/
theorem rxPoll_source (pid : PeerId) (budget : Nat) (toStack : List (List UInt8) → Leanux.M Unit) :
    rxPoll pid budget toStack = (do
      if ← branch .rxPollNoBudget (budget == 0) then return 0
      let state ← forIn ([:MAX_QUEUED_PACKETS + 1] : Std.Legacy.Range)
        ((0, {}, false) : PollState) (pollStep pid budget toStack)
      pollFinish pid budget toStack state) := by
  unfold pollStep pollFinish PollHookRules.stepWith PollHookRules.finishWith rxPoll
  simp only [bind_assoc]
  rfl

/-- The exact remainder after consumeDataDone's first endpoint setter. -/
def consumeDataAfterEndpoint (pid : PeerId) (pkt : RxPacket) : WG.M (Option (List UInt8)) := do
  if ← branch .doneReceivedNew (← receivedWithKeypair pid pkt.keypair) then
    timersHandshakeComplete pid .walltimeLastHandshakeData
    sendStagedPackets pid
  keepKeyFreshRx pid
  timersAnyAuthenticatedPacketReceived pid
  timersTraversal pid
  let bytes := pkt.bytes
  let len := bytes.length   -- skb->len
  let reject (why : Dishonest) : WG.M (Option (List UInt8)) := do
    dishonest why   -- then packet_processed: dev_kfree_skb
    return none
  -- a packet with length 0 is a keepalive
  if ← branch .doneRxKeepalive (len == 0) then
    updateRxStats pid MESSAGE_DATA_LEN_0   -- message_data_len(0)
    return none
  timersDataReceived pid
  -- `skb_network_header(skb) < skb->head`: the decrypted skb's network header is its data
  if ← branch .doneNetworkBelowHead false then return ← reject .size
  -- `!(pskb_network_may_pull(skb, sizeof(struct iphdr)) && (version == 4 ||
  -- (version == 6 && pskb_network_may_pull(skb, sizeof(struct ipv6hdr)))))`
  let version := (bytes.headD 0).toNat / 16
  let honest ← WG.andM (branch .doneMayPullV4 (len ≥ 20)) do
    WG.orM (branch .doneVersion4 (version == 4)) do
      WG.andM (branch .doneVersion6 (version == 6)) (branch .doneMayPullV6 (len ≥ 40))
  if !honest then return ← reject .type
  -- skb->ip_summed = CHECKSUM_UNNECESSARY; csum_level = ~0
  let protocol := ipTunnelParseProtocol bytes
  let ds := pkt.ds   -- PACKET_CB(skb)->ds
  let mut ipLen := 0
  let mut bytes := bytes
  if ← branch .doneProtoIp (protocol == 4) then
    ipLen := beAt bytes 2 2   -- ntohs(ip_hdr(skb)->tot_len)
    if ← branch .doneV4TooShort (ipLen < 20) then return ← reject .size
    bytes ← inetEcnDecapsulate 4 ds bytes   -- INET_ECN_decapsulate(skb, ds, ip_hdr(skb)->tos)
  else if ← branch .doneProtoIpv6 (protocol == 6) then
    ipLen := beAt bytes 4 2 + 40   -- ntohs(payload_len) + sizeof(struct ipv6hdr)
    bytes ← inetEcnDecapsulate 6 ds bytes   -- ..., ipv6_get_dsfield(ipv6_hdr(skb))
  else return ← reject .type
  if ← branch .doneLenBeyond (ipLen > len) then return ← reject .size
  let lenBeforeTrim := len
  -- pskb_trim(skb, len) of a linear skb
  if ← branch .doneTrimFailed false then return none
  let routed ← lookupSrc protocol bytes
  peerPut routed   -- we don't need the extra reference
  if ← branch .doneDishonestPeer (routed != some pid) then return ← reject .peer
  -- napi_gro_receive(&peer->napi, skb) (a cut point)
  updateRxStats pid (lenBeforeTrim + MESSAGE_DATA_LEN_0)   -- message_data_len(len_before_trim)
  return some (bytes.take ipLen)


theorem consumeDataDone_source (pid : PeerId) (pkt : RxPacket) (e : Endpoint) :
    consumeDataDone pid pkt e = (do setPeerEndpoint pid e; consumeDataAfterEndpoint pid pkt) := rfl

/-- The original first-iteration prefix through the endpoint setter, with
state reads at the packet/counter/setter cuts. Rejected packets retain cleanup
context; a drained queue is distinct from a rejected packet. -/
def pollEndpointPrefix (pid : PeerId) : Leanux.M PollPrepared := do
  let (first, q) ← (← getPeer pid).rxQueue.peek
  setPeer pid { (← getPeer pid) with rxQueue := q }
  let go ← WG.andM (branch .rxPollPacket first.isSome) do
    let some f := first | invariant "unreachable"
    branch .rxPollNotUncrypted ((← getRxSkb f).state != .uncrypted)
  if !go then return .drained
  let some id := first | invariant "unreachable"
  let beforeRead ← Campaign2.Product.read
  let pkt ← getRxSkb id
  if pkt.peer != pid then invariant "a packet on another peer's rx_queue"
  setPeer pid { (← getPeer pid) with rxQueue := (← getPeer pid).rxQueue.dropPeeked }
  if ← branch .rxPollNotCrypted (pkt.state != .crypted) then return .rejected id pkt
  let beforeCounter ← Campaign2.Product.read
  let valid ← counterValidate pkt.keypair pkt.nonce
  let afterCounter ← Campaign2.Product.read
  if ← branch .rxPollCounterInvalid !valid then return .rejected id pkt
  let endpoint ← endpointFromSkb pkt.source
  if ← branch .rxPollEndpointFailed endpoint.isNone then return .rejected id pkt
  let some e := endpoint | invariant "unreachable"
  setPeerEndpoint pid e
  let atEndpoint ← Campaign2.Product.read
  return .endpoint ⟨id, pkt, e, beforeRead, beforeCounter, afterCounter,
    .ok (valid, afterCounter), atEndpoint⟩

def pollPacketCleanup (pid : PeerId) (budget : Nat) (state : PollState)
    (id : SkbId) (pkt : RxPacket) (free : Bool) : Leanux.M (ForInStep PollState) := do
  keypairPut (some pkt.keypair) false
  peerPut (some pid)
  _ ← branch .rxPollFree free
  freeRxSkb id
  let workDone := state.1 + 1
  if ← branch .rxPollBudgetDone (workDone ≥ budget) then
    return .done (workDone, state.2.1, state.2.2)
  return .yield (workDone, state.2.1, state.2.2)

/-- Every original operation after the prefix, including arbitrary stack
callbacks, reference release and skb freeing. -/
def pollEndpointSuffix (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (state : PollState)
    (prepared : PollPrepared) : Leanux.M (ForInStep PollState) := do
  match prepared with
  | .drained => return .done (state.1, state.2.1, true)
  | .rejected id pkt => pollPacketCleanup pid budget state id pkt true
  | .endpoint cut =>
    let mut gro := state.2.1
    for inner in (← consumeDataAfterEndpoint pid cut.packet).toList do
      gro ← napiGroReceive toStack gro inner
    pollPacketCleanup pid budget (state.1, gro, state.2.2) cut.id cut.packet false

theorem read_ignore {α : Type} (next : Leanux.M α) :
    (do let _ ← Campaign2.Product.read; next) = next := rfl

theorem bind_if {α β : Type} (condition : Prop) [Decidable condition]
    (yes no : Leanux.M α) (next : α → Leanux.M β) :
    ((if condition then yes else no) >>= next) =
      if condition then yes >>= next else no >>= next := by
  split <;> rfl

theorem invariant_bind {α β : Type} (message : String) (next : α → Leanux.M β) :
    ((invariant message : Leanux.M α) >>= next) = (invariant message : Leanux.M β) := rfl

theorem bind_option {α β γ : Type} (value : Option α)
    (noneCase : Leanux.M β) (someCase : α → Leanux.M β) (next : β → Leanux.M γ) :
    ((match value with | some a => someCase a | _ => noneCase) >>= next) =
      (match value with | some a => someCase a >>= next | _ => noneCase >>= next) := by
  cases value <;> rfl

/-- No original suffix is dropped by stopping the observation at the setter. -/
theorem pollStep_endpoint_source (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (turn : Nat) (state : PollState) :
    pollStep pid budget toStack turn state =
      (pollEndpointPrefix pid >>= pollEndpointSuffix pid budget toStack state) := by
  simp only [pollStep, PollHookRules.stepWith, pollEndpointPrefix, pollEndpointSuffix,
    consumeDataDone_source, bind_assoc, pure_bind, bind_if, invariant_bind]
  congr 1
  funext peer
  congr 1
  funext peek
  rcases peek with ⟨first, queue⟩
  congr 1
  funext peer
  congr 1
  funext stepUnit
  congr 1
  funext go
  cases go <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  cases first <;> simp only [bind_assoc, pure_bind, bind_if, invariant_bind, pollEndpointSuffix, pollPacketCleanup]
  all_goals try rfl
  apply Eq.trans (read_ignore _).symm
  congr 1
  funext beforeRead
  congr 1
  funext pkt
  split <;> try rfl
  all_goals try rfl
  congr 1
  funext peer
  congr 1
  funext peer2
  congr 1
  funext stepUnit
  congr 1
  funext crypted
  cases crypted <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  apply Eq.trans (read_ignore _).symm
  congr 1
  funext beforeCounter
  congr 1
  funext valid
  apply Eq.trans (read_ignore _).symm
  congr 1
  funext afterCounter
  congr 1
  funext rejected
  cases rejected <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  congr 1
  funext endpoint
  congr 1
  funext failed
  cases failed <;> simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
  all_goals try rfl
  cases endpoint <;> simp only [bind_assoc, pure_bind, invariant_bind, pollEndpointSuffix, pollPacketCleanup, read_ignore]
  all_goals first | rfl | (simp only [Leanux.Proofs.Framing.liftWG_bind, bind_assoc]; try rfl)

/-- Includes the original no-budget decision before touching the first queue item. -/
def pollInitialPrefix (pid : PeerId) (budget : Nat) : Leanux.M (Option PollPrepared) := do
  if ← branch .rxPollNoBudget (budget == 0) then return none
  return some (← pollEndpointPrefix pid)

def pollInitialSuffix (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) (prepared : Option PollPrepared) : Leanux.M Nat := do
  match prepared with
  | none => return 0
  | some prepared =>
    let step ← pollEndpointSuffix pid budget toStack (0, {}, false) prepared
    let state ← match step with
      | .done state => pure state
      | .yield state => forIn (List.range' 1 MAX_QUEUED_PACKETS) state (pollStep pid budget toStack)
    pollFinish pid budget toStack state

theorem rxPoll_first_source (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) :
    rxPoll pid budget toStack =
      (pollInitialPrefix pid budget >>= pollInitialSuffix pid budget toStack) := by
  rw [rxPoll_source]
  simp only [pollInitialPrefix, bind_assoc]
  congr 1
  funext noBudget
  cases noBudget <;> simp only [Bool.false_eq_true, ite_false, ite_true, pure_bind,
    bind_assoc, pollInitialSuffix]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.zero_add, Nat.sub_zero, Nat.div_one, List.range'_succ, List.forIn_cons,
    pollStep_endpoint_source, bind_assoc]
  congr 1
  funext prepared
  congr 1
  funext step
  cases step <;> rfl

def observedRxPoll (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) :
    Leanux.M (Nat × Campaign2.Product.Outcome (Option PollPrepared)) := do
  let observation ← Campaign2.Product.inspect (pollInitialPrefix pid budget)
  let count ← rxPoll pid budget toStack
  pure (count, observation)

theorem observedRxPoll_erase (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) :
    (do let result ← observedRxPoll pid budget toStack; pure result.1) =
      rxPoll pid budget toStack := by
  funext w
  change (((rxPoll pid budget toStack).run w >>= fun out =>
    Except.ok ((out.1, Campaign2.Product.observeResult ((pollInitialPrefix pid budget).run w)), out.2))
      >>= fun out => Except.ok (out.1.1, out.2)) = (rxPoll pid budget toStack).run w
  cases h : (rxPoll pid budget toStack).run w <;> rfl

/-- Decorate the actual original publication and its immediately invoked
poll callback. Later release/softirq operations are retained verbatim. -/
def observedDecryptPoll (softirq : Leanux.M Unit) (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) : Leanux.M PublicationPollResult := do
  let publication ← publicationPrefix softirq
  match publication with
  | none => pure (false, none)
  | some pub =>
    let poll ← observedRxPoll pid budget toStack
    peerPut (some pub.owner)
    softirq
    pure (true, some (pub, poll))

theorem observedDecryptPoll_erase (softirq : Leanux.M Unit) (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → Leanux.M Unit) :
    (do let result ← observedDecryptPoll softirq pid budget toStack; pure result.1) =
      decryptStep softirq (discard (rxPoll pid budget toStack)) := by
  rw [decryptStep_publication]
  simp only [observedDecryptPoll, bind_assoc]
  congr 1
  funext publication
  cases publication with
  | none => rfl
  | some pub =>
    simp only [publicationSuffix, bind_assoc, pure_bind]
    rw [← observedRxPoll_erase pid budget toStack]
    simp only [discard, map_const, Function.comp_apply, Function.const_apply,
      map_eq_pure_bind, bind_assoc, pure_bind]

end Leanux.Proofs.WG.Roaming
