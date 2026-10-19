import Leanux.Proofs.WG.Queues.HandshakeSendResponse
import Leanux.Proofs.WG.Queues.CurrentSlotTransmit

/-! Three-slot compatibility through the actual handshake receive source.
The existing entry predicate supplies configured identity at the real session
cut. All native claims concern normal runs; the original observer and its
stopped journals are unchanged. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open HandshakeEntry

private theorem store (action : WG.M α) (same : SameWGStore action) : Preserves Entry action :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) action ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.store) action same)
    (CurrentSlots.store_preserves same)

private theorem update (pid : PeerId) (f : Peer → Peer)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (slots : ∀ p, Affiliation.peerCell (f p) = Affiliation.peerCell p) :
    Preserves Entry (getPeer pid >>= fun p => setPeer pid (f p)) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.update) pid f configured)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.update_peer) pid f slots)

private theorem update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (slots : ∀ p, Affiliation.peerCell (f p) = Affiliation.peerCell p)
    (ht : ∀ x, Preserves Entry (tail x)) :
    Preserves Entry (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind (update pid f configured slots) ht

private theorem readPeer (pid : PeerId) : Preserves Entry (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi hr
  exact (getPeer_normal pid w v p a b hr).1 ▸ hi

private theorem modifyDevice (f : Device → Device)
    (configured : ∀ d, ConfiguredIdentity.state (f d) = ConfiguredIdentity.state d)
    (material : ∀ d, ((f d).ifindex,(f d).keypairs) = (d.ifindex,d.keypairs))
    (peer : ∀ d, (f d).nextPeer = d.nextPeer)
    (key : ∀ d, (f d).nextKeypairId = d.nextKeypairId)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (rx : ∀ d, (f d).rxSkbs = d.rxSkbs)
    (peers : ∀ d, (f d).peers = d.peers) : Preserves Entry (modifyDev f) := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine)
  · exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.modifyDevice) f configured material peer key keys rx
  · apply CurrentSlots.fields_preserves (project := id)
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotFrames.«0».Leanux.Proofs.WG.CurrentSlots.fields_modify) f key peers keys

macro "receive_slots_step" : tactic => `(tactic| first
  | (receive_update_head setPeer; apply update <;> intro p <;> rfl)
  | (receive_update_head Bind.bind
     apply update_bind
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head getDev; exact store _ getDev_sameWGStore)
  | (rx_retention_head getPeer; exact readPeer _)
  | (rx_retention_head modifyDev
     apply modifyDevice _ ?_ ?_ ?_ ?_ ?_ ?_ ?_
     all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ Entry)
  | routing_tx_step)

/-- The actual normal session run supplies both its new material witness and
its three-slot installation; no tail-success premise is added. -/
theorem session (pid : PeerId) : Preserves Entry (beginSession pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.session) pid) w a result v b hi.1 run,
    (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.beginSession_preserves pid)
      w a result v b ⟨hi.2,(entry_facts hi).1⟩ run⟩

private theorem send_slots (pid : PeerId) (msg : List UInt8) :
    Preserves CurrentSlots.Inv (sendBufferToPeer pid msg) := by
  unfold sendBufferToPeer
  simp (config := {zeta := false}) only [branch,hiddenAlloc]
  repeat' first
    | (rx_retention_head send4; exact CurrentSlots.TxSource.send4_preserves _ _ _ _ _)
    | (rx_retention_head send6; exact CurrentSlots.TxSource.send6_preserves _ _ _ _ _)
    | slot_traffic_step

private theorem send (pid : PeerId) (msg : List UInt8) : Preserves Entry (sendBufferToPeer pid msg) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.send) pid msg) (send_slots pid msg)

private theorem traversal (pid : PeerId) : Preserves Entry (timersTraversal pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.traversal) pid) (CurrentSlots.timersTraversal_preserves pid)

private theorem sent (pid : PeerId) : Preserves Entry (timersAnyAuthenticatedPacketSent pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.sent) pid) (CurrentSlots.delTimer_preserves pid .sendKeepalive)

private theorem derived (pid : PeerId) : Preserves Entry (timersSessionDerived pid) := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.derived) pid)
  unfold timersSessionDerived
  apply discard_view_spec id CurrentSlots.Inv
  exact CurrentSlots.modPeerTimer_preserves _ _ _ _

private theorem complete (pid : PeerId) (site : HiddenSite) : Preserves Entry (timersHandshakeComplete pid site) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.complete) pid site) (CurrentSlots.timersHandshakeComplete_preserves pid site)

private theorem received (pid : PeerId) : Preserves Entry (timersAnyAuthenticatedPacketReceived pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.received) pid) (CurrentSlots.delTimer_preserves pid .newHandshake)

private theorem pay (peer : Option PeerId) : Preserves Entry (peerPut peer) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.pay) peer) (CurrentSlots.peerPut_preserves peer)

private theorem cookie (action : WG.M α) (frame : SameCookie action) : Preserves Entry action := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.cookie) action frame)
  apply CurrentSlots.fields_preserves (project := id)
  apply frame.of_factor (fun k : WGOwnedView => CurrentSlots.fields {dev := k.dev})
  intro w
  unfold CurrentSlots.fields Leanux.Proofs.WG.Queues.RxCredits.keyWords
  simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,
    Option.map_map,Option.bind_map,Function.comp_def]
  rfl

private theorem reply_slots (src : SkbSource) (bytes : List UInt8) :
    Preserves CurrentSlots.Inv (sendBufferAsReplyToSkb src bytes) := by
  unfold sendBufferAsReplyToSkb
  simp (config := {zeta := false}) only [branch,invariant,hiddenAlloc]
  repeat' first
    | (rx_retention_head endpointFromSkb; exact CurrentSlots.store_preserves (endpointFromSkb_sameWGStore _))
    | (rx_retention_head send4; exact CurrentSlots.TxSource.send4_preserves _ _ _ _ _)
    | (rx_retention_head send6; exact CurrentSlots.TxSource.send6_preserves _ _ _ _ _)
    | slot_traffic_step

private theorem sendCookie (msg : List UInt8) (src : SkbSource) : Preserves Entry (sendHandshakeCookie msg src) := by
  apply (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _ ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.sendCookie) msg src)
  unfold sendHandshakeCookie
  apply preserves_bind
  · apply CurrentSlots.fields_preserves (project := id)
    apply (cookieMessageCreate_sameCookie _ _ _).of_factor
      (fun k : WGOwnedView => CurrentSlots.fields {dev := k.dev})
    intro w
    unfold CurrentSlots.fields Leanux.Proofs.WG.Queues.RxCredits.keyWords
    simp only [cookieView,cookieDevice,wgOwnedView,wgStoreView,
      Option.map_map,Option.bind_map,Function.comp_def]
    rfl
  · intro bytes; exact reply_slots src bytes

private theorem keepalive_stage (pid : PeerId) (p : Peer) : Hoare (do
    let d ← getDev
    setPeer pid {p with staged := p.staged ++ [{mtu := d.mtu}]}
    sendStagedPackets pid)
    (fun w => CurrentSlots.Inv w ∧ Affiliation.peerAt w pid = some (Affiliation.peerCell p))
    (fun _ => CurrentSlots.Inv) := by
  let R := fun w => CurrentSlots.Inv w ∧ Affiliation.peerAt w pid = some (Affiliation.peerCell p)
  have getd : Preserves R getDev := by
    unfold getDev
    repeat' first
      | (rx_retention_head get; exact hoare_consequence (hoare_get R) (fun _ h => h) (fun _ _ h => h.2))
      | (rx_retention_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) R)
      | rx_retention_step
  apply hoare_bind _ _ getd
  intro d
  have saved : Hoare (setPeer pid {p with staged := p.staged ++ [{mtu := d.mtu}]}) R
      (fun _ => CurrentSlots.Inv) := by
    apply hoare_consequence (Affiliation.setPeer_spec
      (fun v => ∀ s, v = some s → CurrentSlots.SlotInv s) pid {p with staged := p.staged ++ [{mtu := d.mtu}]})
    · exact fun _ h => h
    · exact fun _ _ h => h
  exact hoare_bind _ _ saved (fun _ => CurrentSlots.sendStagedPackets_preserves pid)

private theorem keepalive_slots (pid : PeerId) : Preserves CurrentSlots.Inv (sendKeepalive pid) := by
  let P := CurrentSlots.Inv
  let R := fun p w => P w ∧ Affiliation.peerAt w pid = some (Affiliation.peerCell p)
  have getp : Hoare (getPeer pid) P (fun p => R p) :=
    Affiliation.getPeer_spec (fun v => ∀ s, v = some s → CurrentSlots.SlotInv s) pid
  unfold sendKeepalive
  apply hoare_bind _ _ getp
  intro p
  simp only [branch,hiddenAlloc]
  apply hoare_bind _ _ (hoare_liftAmbient _ (R p))
  intro empty
  cases empty with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte]
    exact hoare_consequence (CurrentSlots.sendStagedPackets_preserves pid) (fun _ h => h.1) (fun _ _ h => h)
  | true =>
    simp only [↓reduceIte]
    apply hoare_bind _ _ (hoare_liftAmbient _ (R p))
    intro allocated
    apply hoare_bind _ _ (hoare_liftAmbient _ (R p))
    intro noMem
    cases noMem with
    | true =>
      simp only [↓reduceIte]
      exact hoare_consequence (preserves_pure ()) (fun _ h => h.1) (fun _ _ h => h)
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte]
      exact keepalive_stage pid p

private theorem keepalive (pid : PeerId) : Preserves Entry (sendKeepalive pid) :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeEntry.combine) _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerHandshake.«0».Leanux.Proofs.WG.OwnerHandshake.keepalive) pid)
    (keepalive_slots pid)

theorem sendResponse (pid : PeerId) : Preserves Entry (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponse
  simp (config := {zeta := false}) only [hiddenClock64,branch,invariant]
  repeat' first
    | (rx_retention_head createResponse; exact HandshakeSendResponse.create_entry _)
    | (rx_retention_head addMacToPacket; exact HandshakeSendResponse.mac_entry _ _)
    | (rx_retention_head beginSession; exact session _)
    | (rx_retention_head timersSessionDerived; exact derived _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head timersAnyAuthenticatedPacketSent; exact sent _)
    | (rx_retention_head sendBufferToPeer; exact send _ _)
    | receive_slots_step

theorem afterMac (msg : List UInt8) (src : SkbSource) (loaded : Bool) (state : MacState) :
    Preserves Entry (Cookies.afterMac msg src loaded state) := by
  unfold Cookies.afterMac
  simp (config := {zeta := false}) only [branch,invariant,WG.andM,WG.orM]
  repeat' first
    | (rx_retention_head consumeInitiation; exact HandshakeEntry.initiation _)
    | (rx_retention_head consumeResponse; exact HandshakeEntry.response _)
    | (rx_retention_head sendHandshakeResponse; exact sendResponse _)
    | (rx_retention_head beginSession; exact session _)
    | (rx_retention_head sendHandshakeCookie; exact sendCookie _ _)
    | (rx_retention_head setPeerEndpointFromSkb; exact HandshakeEntry.endpoint _ _)
    | (rx_retention_head timersSessionDerived; exact derived _)
    | (rx_retention_head timersHandshakeComplete; exact complete _ _)
    | (rx_retention_head sendKeepalive; exact keepalive _)
    | (rx_retention_head timersAnyAuthenticatedPacketReceived; exact received _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head peerPut; exact pay _)
    | receive_slots_step

theorem receive (msg : List UInt8) (src : SkbSource) :
    Preserves Entry (receiveHandshakePacket msg src) := by
  rw [Cookies.receive_factor]
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head cookieMessageConsume; exact HandshakeEntry.cookie _)
    | (rx_retention_head Cookies.loadPhase; exact store _ Cookies.loadPhase_sameStore)
    | (rx_retention_head cookieValidatePacket; exact cookie _ (cookieValidatePacket_sameCookie _ _ _))
    | (rx_retention_head Cookies.afterMac; exact afterMac _ _ _ _)
    | receive_slots_step

theorem step : Preserves Entry WG.receiveStep := by
  unfold WG.receiveStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head receiveHandshakePacket; exact receive _ _)
    | receive_slots_step

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceiveSlots
