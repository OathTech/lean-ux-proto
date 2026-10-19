import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierNative
import Leanux.Proofs.WG.Packets.PublicationTimers

/-! Native RX-store frames at timer and packet-maintenance effect cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity.Driver

private theorem effect_ambient_rx (action : AmbientM α) :
    SameView RxDisposition.nativeRxStore (MonadLift.monadLift action : WG.M α) :=
  fun initial => hoare_liftAmbient action (fun w => RxDisposition.nativeRxStore w = initial)

theorem effect_setKey_rx (kid : KeypairId) (key : Keypair) :
    SameView RxDisposition.nativeRxStore (setKeypair kid key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a x v b run
  cases run
  simp only [RxDisposition.nativeRxStore,Option.map_map,Function.comp_def]
  cases w.dev <;> rfl

theorem effect_arm_rx (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    SameView RxDisposition.nativeRxStore (armTimer pid timer delay caller) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.arm_geometry) pid timer delay caller).factor Prod.snd

theorem effect_del_rx (pid : PeerId) (timer : PeerTimer) :
    SameView RxDisposition.nativeRxStore (delTimer pid timer) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.del_geometry) pid timer).factor Prod.snd

theorem effect_stats_rx (pid : PeerId) (len : Nat) :
    SameView RxDisposition.nativeRxStore (updateRxStats pid len) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.stats_geometry) pid len).factor Prod.snd

theorem effect_dishonest_rx (why : Dishonest) :
    SameView RxDisposition.nativeRxStore (dishonest why) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.dishonest_geometry) why).factor Prod.snd

theorem effect_clearEndpoint_rx (pid : PeerId) :
    SameView RxDisposition.nativeRxStore (clearPeerEndpointSrc pid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTimers.«0».Leanux.Proofs.WG.PublicationFrontier.clearEndpoint_geometry) pid).factor Prod.snd

theorem effect_purge_rx (pid : PeerId) :
    SameView RxDisposition.nativeRxStore (purgeStagedPackets pid) :=
  ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTimers.«0».Leanux.Proofs.WG.PublicationFrontier.purge_geometry) pid).factor Prod.snd

theorem effect_keyPut_rx (kid : Option KeypairId) (unreference : Bool) :
    SameView RxDisposition.nativeRxStore (keypairPut kid unreference) :=
  ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.keyPay) kid unreference).factor Prod.snd

macro "transport_effect_rx" : tactic => `(tactic| (
  try simp (config := {zeta := false}) only [WG.andM,WG.orM,branch,invariant,unsupported]
  repeat' first
  | (snapshot_head WG.andM; unfold WG.andM)
  | (snapshot_head WG.orM; unfold WG.orM)
  | (snapshot_head callerJiffies; exact (callerJiffies_sameWGWorld _).factor RxDisposition.nativeRxStore)
  | (snapshot_head jitterBelowRekeyTimeout; unfold jitterBelowRekeyTimeout)
  | (snapshot_head modPeerTimerGuard; unfold modPeerTimerGuard)
  | (snapshot_head timersAnyAuthenticatedPacketReceived; unfold timersAnyAuthenticatedPacketReceived)
  | (snapshot_head peekQueuedUnit; exact effect_ambient_rx _)
  | (snapshot_head recordQueued; exact effect_ambient_rx _)
  | (snapshot_head keypairPut; exact effect_keyPut_rx _ _)
  | (snapshot_head setKeypair; exact effect_setKey_rx _ _)
  | (snapshot_head updateRxStats; exact effect_stats_rx _ _)
  | (snapshot_head dishonest; exact effect_dishonest_rx _)
  | (snapshot_head inetEcnDecapsulate; exact TransportPublication.store_rx _ (inetEcnDecapsulate_sameWGStore _ _ _))
  | (snapshot_head delTimer; exact effect_del_rx _ _)
  | (snapshot_head clearPeerEndpointSrc; exact effect_clearEndpoint_rx _)
  | (snapshot_head purgeStagedPackets; exact effect_purge_rx _)
  | solve | transport_native_rx
  | (snapshot_head ite; split)
  | (snapshot_head dite; split)
  | (snapshot_head Bind.bind; apply SameView.bind)
  | keypairs_intro_forall
  | snapshot_head_reduce
  | snapshot_head_match))

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
