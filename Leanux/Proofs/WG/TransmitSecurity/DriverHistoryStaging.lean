import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsHistory

namespace Leanux.Proofs.WG.TransmitSecurity.Driver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open Leanux.Proofs.WG.Origins.HandshakeSources
variable {E : Type} {Safe : List E → Prop} {g : Hooks E}

set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem staging_history (h : HooksHistorySafe Safe g) (pid : PeerId) :
    StateHistorySafe Safe (stagingObserved g pid) := by
  unfold stagingObserved
  repeat' first
    | (driver_history_head AuthenticatedEffects.PacketEffects.noKeyWith; exact effects_noKey_history h.effects _ _ _ _)
    | (driver_history_head Hooks.selection; exact h.selection _)
    | (driver_history_head Hooks.reserve; exact h.reserve _)
    | (driver_history_head Hooks.allocate; exact h.allocate _)
    | (driver_history_head Hooks.create; exact h.create _ _)
    | (driver_history_head Hooks.session; exact h.session _)
    | (driver_history_head Hooks.confirmation; exact h.confirmation _ _)
    | driver_state_history_step

/-- Preparation and complete staging preserve the supplied history predicate. -/
theorem keepalive_staging_history
    (prepare : ∀ pid, StateHistorySafe Safe (g.keepalivePrepare pid))
    (staging : ∀ pid, StateHistorySafe Safe (stagingObserved g pid)) (pid : PeerId) :
    StateHistorySafe Safe (keepaliveObserved g pid) := by
  unfold keepaliveObserved
  repeat' first
    | (driver_history_head Hooks.keepalivePrepare; exact prepare _)
    | (driver_history_head stagingObserved; exact staging _)
    | driver_state_history_step

theorem HooksHistorySafe.core (h : HooksHistorySafe Safe g) : ActorCoreHistorySafe Safe g where
  keepalivePrepare := h.keepalivePrepare
  staging := staging_history h
  fixtureEnter := h.fixtureEnter
  fixtureLeave := h.fixtureLeave
  handshake := h.handshake _ _ h.session (keepalive_staging_history h.keepalivePrepare (staging_history h))
  sendWorker := h.sendWorker
  flushedSend := h.flushedSend
  armTimer := h.armTimer
  queueSend := h.queueSend
  candidateEnter := h.candidateEnter
  candidateLeave := h.candidateLeave
  prepare := h.prepare
  counterCheck := h.counterCheck
  timerSelected := h.timerSelected
  timerFinished := h.timerFinished
  confirmation := h.confirmation
  session := h.session
  front := h.front
  poll := h.poll
  encrypt := h.encrypt
  transmit := h.transmit

theorem keepalive_actor_history (h : ActorCoreHistorySafe Safe g) (pid : PeerId) :
    StateHistorySafe Safe (keepaliveObserved g pid) :=
  keepalive_staging_history h.keepalivePrepare h.staging pid

theorem keepalive_history (h : HooksHistorySafe Safe g) (pid : PeerId) :
    StateHistorySafe Safe (keepaliveObserved g pid) :=
  keepalive_actor_history h.core pid

theorem transmit_history (h : ActorCoreHistorySafe Safe g) (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateHistorySafe Safe (transmitObserved g family addr packets mtu) := by
  unfold transmitObserved
  repeat' first
    | (driver_history_head Hooks.front; exact h.front _ _ _ _)
    | (driver_history_head stagingObserved; exact h.staging _)
    | (driver_history_head Hooks.session; exact h.session _)
    | (driver_history_head Hooks.confirmation; exact h.confirmation _ _)
    | driver_state_history_step

theorem expired_history (h : ActorCoreHistorySafe Safe g) (pid : PeerId) :
    StateHistorySafe Safe (expiredKeepaliveObserved g pid) := by
  exact effects_expiredKeepalive_history h.effects _ (keepalive_actor_history h) pid

theorem persistent_history (h : ActorCoreHistorySafe Safe g) (pid : PeerId) :
    StateHistorySafe Safe (persistentObserved g pid) := by
  exact effects_persistent_history h.effects _ (keepalive_actor_history h) pid

theorem timer_history (h : ActorCoreHistorySafe Safe g) (pid : PeerId) (t : PeerTimer) :
    StateHistorySafe Safe (timerObserved g pid t) := by
  cases t with
  | retransmitHandshake => exact effects_retransmit_history h.effects _
  | sendKeepalive => exact expired_history h _
  | newHandshake => exact effects_expiredNew_history h.effects _
  | zeroKeyMaterial => exact History.state_lift _
  | persistentKeepalive => exact persistent_history h _

theorem response_history (h : ActorCoreHistorySafe Safe g) (pid : PeerId) :
    StateHistorySafe Safe (responseWith (handshakeOps g) pid) := by
  unfold responseWith
  dsimp only [handshakeOps]
  repeat' first
    | (driver_history_head Hooks.session; exact h.session _)
    | (driver_history_head Hooks.confirmation; exact h.confirmation _ _)
    | driver_state_history_step

theorem afterMac_history (h : ActorCoreHistorySafe Safe g) (msg : List UInt8) (src : SkbSource)
    (loaded : Bool) (mac : MacState) :
    StateHistorySafe Safe (afterMacWith (handshakeOps g) msg src loaded mac) := by
  unfold afterMacWith
  dsimp only [handshakeOps]
  repeat' first
    | (driver_history_head responseWith; exact response_history h _)
    | (driver_history_head keepaliveObserved; exact keepalive_actor_history h _)
    | (driver_history_head Hooks.session; exact h.session _)
    | (driver_history_head Hooks.confirmation; exact h.confirmation _ _)
    | driver_state_history_step

theorem reception_history (h : ActorCoreHistorySafe Safe g) (msg : List UInt8) (src : SkbSource) :
    StateHistorySafe Safe (receptionWith (handshakeOps g) msg src) := by
  unfold receptionWith
  dsimp only [handshakeOps]
  repeat' first
    | (driver_history_head afterMacWith; exact afterMac_history h _ _ _ _)
    | (driver_history_head Hooks.session; exact h.session _)
    | (driver_history_head Hooks.confirmation; exact h.confirmation _ _)
    | driver_state_history_step

theorem handshake_history (h : ActorCoreHistorySafe Safe g) :
    StateHistorySafe Safe (handshakeObserved g) := by
  exact h.handshake

theorem receiveTail_actor_history (h : ActorCoreHistorySafe Safe g) (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StateHistorySafe Safe (receiveTailObserved g pid pkt confirmed) := by
  unfold receiveTailObserved
  repeat' first
    | (driver_history_head AuthenticatedEffects.PacketEffects.prepareWith; exact effects_prepare_history h.effects _ _)
    | (driver_history_head stagingObserved; exact h.staging _)
    | (driver_history_head Hooks.session; exact h.session _)
    | (driver_history_head Hooks.confirmation; exact h.confirmation _ _)
    | driver_state_history_step

theorem consume_history (h : ActorCoreHistorySafe Safe g) (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    StateHistorySafe Safe (consumeObserved g pid pkt ep) := by
  unfold consumeObserved
  repeat' first
    | (driver_history_head receiveTailObserved; exact receiveTail_actor_history h _ _ _)
    | (driver_history_head Hooks.session; exact h.session _)
    | (driver_history_head Hooks.confirmation; exact h.confirmation _ _)
    | driver_state_history_step

theorem receiveTail_history (h : HooksHistorySafe Safe g) (pid : PeerId) (pkt : RxPacket) (confirmed : Bool) :
    StateHistorySafe Safe (receiveTailObserved g pid pkt confirmed) :=
  receiveTail_actor_history h.core pid pkt confirmed

end Leanux.Proofs.WG.TransmitSecurity.Driver
