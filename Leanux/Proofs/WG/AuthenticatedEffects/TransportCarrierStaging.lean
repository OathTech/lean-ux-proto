import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierEffects
import Leanux.Proofs.WG.AuthenticatedEffects.FixtureEffectsContracts

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
    (replay : E → Option TransportDriver.Replay) (hooks : Hooks E) : Prop extends EffectsSafe extra origin replay hooks where
  fixtureEnter : ∀ trigger, StateSafe extra origin replay (hooks.fixtureEnter trigger)
  fixtureLeave : ∀ token, StateSafe extra origin replay (hooks.fixtureLeave token)
  selection : ∀ pid, StateSafe extra origin replay (hooks.selection pid)
  reserve : ∀ kid, StateSafe extra origin replay (hooks.reserve kid)
  allocate : ∀ packets, StateSafe extra origin replay (hooks.allocate packets)
  create : ∀ pid item, StateSafe extra origin replay (hooks.create pid item)

theorem fixture (h : StagingSafe extra origin replay hooks) (trigger : FixtureEffects.Trigger)
    (body : WGPrefix E α) (preserves : StateSafe extra origin replay body) :
    StateSafe extra origin replay (FixtureEffects.runWith (fixtureOps hooks) trigger body) :=
  FixtureEffects.run_preserves _ _ _ (fun _ _ _ hi => hi.2)
    (h.fixtureEnter trigger) h.fixtureLeave preserves

macro "transport_staging_step" : tactic => `(tactic| first
  | (transport_carrier_head liftWGPrefix; solve | apply state_rx; transport_native_rx)
  | transport_carrier_state_step)

theorem staging (h : StagingSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (stagingObserved hooks pid) := by
  unfold stagingObserved
  repeat' first
    | (transport_carrier_head PacketEffects.noKeyWith; exact effects_noKey h.toEffectsSafe _ _ _ _)
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
  unfold expiredKeepaliveObserved TimerEffects.expiredKeepaliveWith
  simp only [effectOps,TimerEffects.observed,Functor.discard,map_const,Function.comp_apply,Function.const,map_eq_pure_bind]
  repeat' first
    | (transport_carrier_head keepaliveObserved; exact keepalive h _)
    | (transport_carrier_head TimerEffects.modifyWith; exact effects_modify h.toEffectsSafe _ _ _ _)
    | transport_staging_step

theorem persistent (h : StagingSafe extra origin replay hooks) (pid : PeerId) :
    StateSafe extra origin replay (persistentObserved hooks pid) := by
  unfold persistentObserved TimerEffects.persistentWith
  simp only [effectOps,TimerEffects.observed]
  repeat' first
    | (transport_carrier_head keepaliveObserved; exact keepalive h _)
    | transport_staging_step

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
