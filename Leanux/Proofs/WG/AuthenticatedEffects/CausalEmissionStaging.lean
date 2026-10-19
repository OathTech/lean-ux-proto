import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionHooks
import Leanux.Proofs.WG.AuthenticatedEffects.CausalEmissionHandshake

/-! The actual native staging, keepalive and handshake-worker callbacks retain
ordered socket accounting, with refusal restoration and allocation on their
original branches. No incoming callback preservation premise remains here. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing TransmitSecurity Lifetimes
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem no_key (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    StateSafe (PacketEffects.noKeyWith effects pid packets keypair invalid) := by
  unfold PacketEffects.noKeyWith
  repeat' first
    | (emission_head TimerEffects.queuedWith; exact queued _ _)
    | (emission_head TimerEffects.Ops.step
       change StateSafe (liftWGPrefix _)
       first
       | (emission_native_head keypairPut; exact state_native _ (EmissionFrames.keypair_put _ _))
       | emission_effect_native)
    | emission_effect_step

theorem staging (pid : PeerId) : StateSafe (Driver.stagingObserved hooks pid) := by
  unfold Driver.stagingObserved
  repeat' first
    | (emission_head PacketEffects.noKeyWith; exact no_key _ _ _ _)
    | (emission_head Driver.Hooks.selection; exact selection _)
    | (emission_head Driver.Hooks.reserve; exact reserve _)
    | (emission_head Driver.Hooks.allocate; exact allocate _)
    | (emission_head Driver.Hooks.create; exact create _ _)
    | (emission_native_head ipTunnelEcnEncap; exact state_native _ ((ipTunnelEcnEncap_sameWGWorld _).factor WGWorld.sent))
    | (emission_native_head IndexOwner.peerDeref
       apply state_native
       sent_frame [IndexOwner.peerDeref,IndexOwner.peerWord] using [getPeer_sent_spec,getKeypair_sent_spec])
    | emission_effect_native
    | emission_step

theorem keepalive (pid : PeerId) : StateSafe (Driver.keepaliveObserved hooks pid) := by
  unfold Driver.keepaliveObserved
  apply state_bind (keepalive_prepare pid)
  intro ready
  cases ready
  · exact state_pure _
  · exact staging pid

theorem handshake_worker : StateSafe (Driver.handshakeObserved hooks) :=
  handshake _ _ session keepalive

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Emissions
