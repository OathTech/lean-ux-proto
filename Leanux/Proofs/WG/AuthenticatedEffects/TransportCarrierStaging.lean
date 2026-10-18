import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierBase

/-! Actual shared staging and keepalive callbacks preserve RX authentication
carriers. Every native leaf uses its concrete packet-store projection frame. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity.Driver
set_option maxRecDepth 4096
set_option maxHeartbeats 600000
variable {E : Type} {extra : List E → Prop} {origin : E → Option TransportDriver.OriginEvent}
  {replay : E → Option TransportDriver.Replay} {hooks : Hooks E}

structure StagingSafe (extra : List E → Prop) (origin : E → Option TransportDriver.OriginEvent)
    (replay : E → Option TransportDriver.Replay) (hooks : Hooks E) : Prop where
  selection : ∀ pid, StateSafe extra origin replay (hooks.selection pid)
  reserve : ∀ kid, StateSafe extra origin replay (hooks.reserve kid)
  allocate : ∀ packets, StateSafe extra origin replay (hooks.allocate packets)
  create : ∀ pid item, StateSafe extra origin replay (hooks.create pid item)

private theorem ambient_rx (action : AmbientM α) :
    SameView RxDisposition.nativeRxStore (MonadLift.monadLift action : WG.M α) :=
  fun initial => hoare_liftAmbient action (fun w => RxDisposition.nativeRxStore w = initial)

private theorem noKey_rx (pid : PeerId) (packets : List Packet) (kid : Option KeypairId) (invalid : Bool) :
    SameView RxDisposition.nativeRxStore (stagedOutNokey pid packets kid invalid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.noKey_geometry) pid packets kid invalid).factor Prod.snd

private theorem readKey_rx (kid : KeypairId) :
    SameView RxDisposition.nativeRxStore (getKeypair kid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.readKey) kid).factor Prod.snd

private theorem peerGet_rx (pid : PeerId) :
    SameView RxDisposition.nativeRxStore (peerGet pid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.peerGet_geometry) pid).factor Prod.snd

private theorem modTimer_rx (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView RxDisposition.nativeRxStore (modPeerTimer site pid timer delay) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.mod_geometry) site pid timer delay).factor Prod.snd

macro "transport_native_rx" : tactic => `(tactic| (
  try simp only [Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
  | (snapshot_head stagedOutNokey; exact noKey_rx _ _ _ _)
  | (snapshot_head getKeypair; exact readKey_rx _)
  | (snapshot_head peerGet; exact peerGet_rx _)
  | (snapshot_head modPeerTimer; exact modTimer_rx _ _ _ _)
  | (snapshot_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).factor RxDisposition.nativeRxStore)
  | (snapshot_head ipTunnelEcnEncap; exact (ipTunnelEcnEncap_sameWGWorld _).factor RxDisposition.nativeRxStore)
  | (snapshot_head IndexOwner.peerDeref; intro initial; exact indexOwner_peerDeref_preserves _ _)
  | (snapshot_head branchCmp; exact ambient_rx _)
  | (snapshot_head hiddenAlloc; exact ambient_rx _)
  | solve | replay_native_frame
  | (snapshot_head Bind.bind; apply SameView.bind)
  | keypairs_intro_forall
  | snapshot_head_reduce
  | snapshot_head_match))

macro "transport_staging_step" : tactic => `(tactic| first
  | (transport_carrier_head liftWGPrefix; solve | apply state_rx; transport_native_rx)
  | transport_carrier_state_step)

theorem staging (h : StagingSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (stagingObserved hooks pid) := by
  unfold stagingObserved
  repeat' first
    | (transport_carrier_head Hooks.selection; exact h.selection _)
    | (transport_carrier_head Hooks.reserve; exact h.reserve _)
    | (transport_carrier_head Hooks.allocate; exact h.allocate _)
    | (transport_carrier_head Hooks.create; exact h.create _ _)
    | transport_staging_step

theorem keepalive (h : StagingSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (keepaliveObserved hooks pid) := by
  unfold keepaliveObserved
  repeat' first
    | (transport_carrier_head stagingObserved; exact staging h _)
    | transport_staging_step

theorem transmit (h : StagingSafe extra origin replay hooks)
    (front : ∀ family addr packets mtu, StateSafe extra origin replay (hooks.front family addr packets mtu))
    (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe extra origin replay (transmitObserved hooks family addr packets mtu) := by
  unfold transmitObserved
  repeat' first
    | (transport_carrier_head Hooks.front; exact front _ _ _ _)
    | (transport_carrier_head stagingObserved; exact staging h _)
    | transport_staging_step

theorem expired (h : StagingSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (expiredKeepaliveObserved hooks pid) := by
  unfold expiredKeepaliveObserved
  repeat' first
    | (transport_carrier_head keepaliveObserved; exact keepalive h _)
    | transport_staging_step

theorem persistent (h : StagingSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (persistentObserved hooks pid) := by
  unfold persistentObserved
  repeat' first
    | (transport_carrier_head keepaliveObserved; exact keepalive h _)
    | transport_staging_step

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
