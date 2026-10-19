import Leanux.Proofs.WG.TimerDiscipline.ReceiveHookModel
import Leanux.Proofs.WG.TimerDiscipline.HookJournalSource
import Leanux.Proofs.WG.Noise.ConsumeConfirmationSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.ReceiveHookJournal
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Queues
open HookJournal

/-- The original validation tail after the data-received hook; it contains no timer hook. -/
def afterData (_pid : PeerId) (pkt : RxPacket) : WG.M (Option Packets.RxReady) := do
  let bytes := pkt.bytes
  let len := bytes.length
  let reject (why : Dishonest) : WG.M (Option Packets.RxReady) := do
    dishonest why
    return none
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
  return some ⟨protocol, bytes, ipLen, lenBeforeTrim⟩


def prepareWith {m : Type → Type} [Monad m]
    (lift : ∀ {α : Type}, WG.M α → m α) (hook : Hook → PeerId → m Unit)
    (pid : PeerId) (pkt : RxPacket) : m (Option Packets.RxReady) := do
  lift (keepKeyFreshRx pid)
  hook .authenticatedReceived pid
  hook .traversal pid
  if ← lift (branch .doneRxKeepalive (pkt.bytes.length == 0)) then
    lift (updateRxStats pid MESSAGE_DATA_LEN_0)
    return none
  hook .dataReceived pid
  lift (afterData pid pkt)

theorem prepare_factor (pid : PeerId) (pkt : RxPacket) :
    RxCredits.prepareRest pid pkt =
      prepareWith (fun {_} action=>action) HookJournal.action pid pkt := rfl

def afterWith {m : Type → Type} [Monad m]
    (lift : ∀ {α : Type}, WG.M α → m α) (hook : Hook → PeerId → m Unit)
    (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) : m (Option (List UInt8)) := do
  if ← lift (branch .doneReceivedNew confirmed) then
    hook (.handshakeComplete .walltimeLastHandshakeData) pid
    lift (sendStagedPackets pid)
  let ready ← prepareWith lift hook pid pkt
  match ready with
  | none=>pure none
  | some ready=>lift (Packets.rxFinish pid ready)

theorem after_factor (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    ConsumeConfirmation.afterConfirmation pid pkt confirmed =
      afterWith (fun {_} action=>action) HookJournal.action pid pkt confirmed := by
  unfold ConsumeConfirmation.afterConfirmation afterWith
  rw [prepare_factor]
  rfl

def consumeWith {m : Type → Type} [Monad m]
    (lift : ∀ {α : Type}, WG.M α → m α) (hook : Hook → PeerId → m Unit)
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) : m (Option (List UInt8)) := do
  lift (setPeerEndpoint pid ep)
  let confirmed ← lift (receivedWithKeypair pid pkt.keypair)
  afterWith lift hook pid pkt confirmed

theorem consume_factor (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    consumeDataDone pid pkt ep = consumeWith (fun {_} action=>action) HookJournal.action pid pkt ep := by
  rw [ConsumeConfirmation.source]
  unfold consumeWith
  simp only [after_factor]

def prepare (pid : PeerId) (pkt : RxPacket) : WGPrefix Receipt (Option Packets.RxReady) :=
  prepareWith (fun {_} action=>liftWGPrefix action) HookJournal.observed pid pkt
def after (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    WGPrefix Receipt (Option (List UInt8)) :=
  afterWith (fun {_} action=>liftWGPrefix action) HookJournal.observed pid pkt confirmed
def consume (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    WGPrefix Receipt (Option (List UInt8)) :=
  consumeWith (fun {_} action=>liftWGPrefix action) HookJournal.observed pid pkt ep

theorem prepare_erases (pid : PeerId) (pkt : RxPacket) :
    ErasesStatePrefix (prepare pid pkt) (RxCredits.prepareRest pid pkt) := by
  rw [prepare_factor]
  unfold prepare prepareWith
  dsimp only
  repeat' first
    | exact HookJournal.observed_erases _ _
    | exact erasesStatePrefix_lift _
    | exact erasesStatePrefix_pure _
    | apply erasesStatePrefix_bind
    | split
    | (intro x; try dsimp only)

theorem after_erases (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    ErasesStatePrefix (after pid pkt confirmed) (ConsumeConfirmation.afterConfirmation pid pkt confirmed) := by
  have tail : ErasesStatePrefix
      (do let ready ← prepare pid pkt
          match ready with
          | none=>pure none
          | some ready=>liftWGPrefix (Packets.rxFinish pid ready))
      (do let ready ← RxCredits.prepareRest pid pkt
          match ready with
          | none=>pure none
          | some ready=>Packets.rxFinish pid ready) := by
    apply erasesStatePrefix_bind (prepare_erases pid pkt)
    intro ready
    cases ready
    · exact erasesStatePrefix_pure _
    · exact erasesStatePrefix_lift _
  unfold after afterWith ConsumeConfirmation.afterConfirmation
  dsimp only
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro received
  cases received
  · exact tail
  · exact erasesStatePrefix_bind (HookJournal.observed_erases _ _) (fun _=>
      erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _=>tail))

theorem consume_erases (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    ErasesStatePrefix (consume pid pkt ep) (consumeDataDone pid pkt ep) := by
  rw [consume_factor]
  unfold consume consumeWith
  exact erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun _=>
    erasesStatePrefix_bind (erasesStatePrefix_lift _) (fun confirmed=>after_erases pid pkt confirmed))

theorem lift_valid {α : Type} (action : WG.M α) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory
      (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ h=>h) (fun _ _ _ _ _ _ h _=>h)

theorem prepare_valid (pid : PeerId) (pkt : RxPacket) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (prepare pid pkt) := by
  unfold prepare prepareWith
  dsimp only
  repeat' first
    | exact HookJournal.observed_preserves _ _
    | exact lift_valid _
    | exact StatePrefixEnsures.pure _ (fun _ _ _ h=>h) (fun _ _ _ h=>h)
    | apply StatePrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem after_valid (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (after pid pkt confirmed) := by
  have tail : StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory
      (do let ready ← prepare pid pkt
          match ready with
          | none=>pure none
          | some ready=>liftWGPrefix (Packets.rxFinish pid ready)) := by
    apply StatePrefixEnsures.bind (prepare_valid pid pkt)
    intro ready
    cases ready
    · exact StatePrefixEnsures.pure _ (fun _ _ _ h=>h) (fun _ _ _ h=>h)
    · exact lift_valid _
  unfold after afterWith
  dsimp only
  apply StatePrefixEnsures.bind (lift_valid _)
  intro received
  cases received
  · exact tail
  · exact StatePrefixEnsures.bind (HookJournal.observed_preserves _ _) (fun _=>
      StatePrefixEnsures.bind (lift_valid _) (fun _=>tail))

theorem consume_valid (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StatePrefixPreserves (fun h _ _=>ValidHistory h) ValidHistory (consume pid pkt ep) := by
  unfold consume consumeWith
  exact StatePrefixEnsures.bind (lift_valid _) (fun _=>
    StatePrefixEnsures.bind (lift_valid _) (fun confirmed=>after_valid pid pkt confirmed))

theorem hook_scoped (pid : PeerId) (hook : Hook) (allowed : AllowedHook hook) :
    StatePrefixPreserves (fun h _ _=>Scoped pid h) (Scoped pid) (HookJournal.observed hook pid) := by
  intro g ambient history prior
  have post : Scoped pid (history ++
      [⟨hook,pid,Campaign2.snapshot g ambient,
        Campaign2.observeResult (((HookJournal.action hook pid).run g).run ambient)⟩]) := by
    intro receipt member
    rcases List.mem_append.mp member with old | fresh
    · exact prior receipt old
    · simp only [List.mem_singleton] at fresh
      subst receipt
      exact ⟨rfl,allowed⟩
  refine ⟨[_],rfl,post,?_⟩
  dsimp only [runPrefix,HookJournal.observed,StateT.run,ExceptT.run,ExceptT.mk]
  cases run : HookJournal.action hook pid g ambient with
  | error _=>trivial
  | ok result=>
    rcases result with ⟨⟨value,current⟩,inputs⟩
    simpa only [StateT.run,run] using post

theorem lift_scoped {α : Type} (pid : PeerId) (action : WG.M α) :
    StatePrefixPreserves (fun h _ _=>Scoped pid h) (Scoped pid) (liftWGPrefix action) :=
  StatePrefixEnsures.lift action (fun _ _ _ h=>h) (fun _ _ _ _ _ _ h _=>h)

theorem prepare_scoped (pid : PeerId) (pkt : RxPacket) :
    StatePrefixPreserves (fun h _ _=>Scoped pid h) (Scoped pid) (prepare pid pkt) := by
  unfold prepare prepareWith
  dsimp only
  repeat' first
    | exact hook_scoped pid .authenticatedReceived (Or.inr (Or.inl rfl))
    | exact hook_scoped pid .traversal (Or.inr (Or.inr (Or.inl rfl)))
    | exact hook_scoped pid .dataReceived (Or.inr (Or.inr (Or.inr rfl)))
    | exact lift_scoped _ _
    | exact StatePrefixEnsures.pure _ (fun _ _ _ h=>h) (fun _ _ _ h=>h)
    | apply StatePrefixEnsures.bind
    | split
    | (intro x; try dsimp only)

theorem after_scoped (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StatePrefixPreserves (fun h _ _=>Scoped pid h) (Scoped pid) (after pid pkt confirmed) := by
  have tail : StatePrefixPreserves (fun h _ _=>Scoped pid h) (Scoped pid)
      (do let ready ← prepare pid pkt
          match ready with
          | none=>pure none
          | some ready=>liftWGPrefix (Packets.rxFinish pid ready)) := by
    apply StatePrefixEnsures.bind (prepare_scoped pid pkt)
    intro ready
    cases ready
    · exact StatePrefixEnsures.pure _ (fun _ _ _ h=>h) (fun _ _ _ h=>h)
    · exact lift_scoped _ _
  unfold after afterWith
  dsimp only
  apply StatePrefixEnsures.bind (lift_scoped pid _)
  intro received
  cases received
  · exact tail
  · exact StatePrefixEnsures.bind
      (hook_scoped pid (.handshakeComplete .walltimeLastHandshakeData) (Or.inl rfl))
      (fun _=>StatePrefixEnsures.bind (lift_scoped pid _) (fun _=>tail))

theorem consume_scoped (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StatePrefixPreserves (fun h _ _=>Scoped pid h) (Scoped pid) (consume pid pkt ep) := by
  unfold consume consumeWith
  exact StatePrefixEnsures.bind (lift_scoped pid _) (fun _=>
    StatePrefixEnsures.bind (lift_scoped pid _) (fun confirmed=>after_scoped pid pkt confirmed))

theorem prepare_appends (pid : PeerId) (pkt : RxPacket) : StateAppends (prepare pid pkt) := by
  unfold prepare prepareWith
  dsimp only
  repeat' first
    | exact HookJournal.observed_appends _ _
    | exact StateAppends.lift _
    | exact StateAppends.pure _
    | apply StateAppends.bind
    | split
    | (intro x; try dsimp only)

theorem after_appends (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StateAppends (after pid pkt confirmed) := by
  have tail : StateAppends
      (do let ready ← prepare pid pkt
          match ready with
          | none=>pure none
          | some ready=>liftWGPrefix (Packets.rxFinish pid ready)) := by
    apply StateAppends.bind (prepare_appends pid pkt)
    intro ready
    cases ready
    · exact StateAppends.pure _
    · exact StateAppends.lift _
  unfold after afterWith
  dsimp only
  apply StateAppends.bind (StateAppends.lift _)
  intro received
  cases received
  · exact tail
  · exact StateAppends.bind (HookJournal.observed_appends _ _) (fun _=>
      StateAppends.bind (StateAppends.lift _) (fun _=>tail))

theorem consume_appends (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StateAppends (consume pid pkt ep) := by
  unfold consume consumeWith
  exact StateAppends.bind (StateAppends.lift _) (fun _=>
    StateAppends.bind (StateAppends.lift _) (fun confirmed=>after_appends pid pkt confirmed))

theorem consume_cut (pid : PeerId) (pkt : RxPacket) (ep : Endpoint)
    (g : WGWorld) (ambient : Ambient) (history : List Receipt) :
    runWGPrefix (consume pid pkt ep) g ambient history =
      match ((setPeerEndpoint pid ep).run g).run ambient with
      | .error stop=>(.error stop,history)
      | .ok ((_,middle),inputs)=>
        match ((receivedWithKeypair pid pkt.keypair).run middle).run inputs with
        | .error stop=>(.error stop,history)
        | .ok ((confirmed,current),later)=>runWGPrefix (after pid pkt confirmed) current later history := by
  unfold consume consumeWith runWGPrefix
  simp only [liftWGPrefix,runStatePrefix_bind,runStatePrefix_lift]
  cases endpointRun : ((setPeerEndpoint pid ep).run g).run ambient with
  | error stop=>rfl
  | ok out=>
    rcases out with ⟨⟨u,middle⟩,inputs⟩
    dsimp only
    cases confirmRun : ((receivedWithKeypair pid pkt.keypair).run middle).run inputs with
    | error stop=>rfl
    | ok result=>rcases result with ⟨⟨confirmed,current⟩,later⟩; rfl


end Leanux.Proofs.WG.TimerDiscipline.ReceiveHookJournal
