import Leanux.Proofs.WG.Queues.DeviceStages
import Leanux.Proofs.Framing.WGIndex

set_option autoImplicit false

namespace Leanux.Proofs.WG.Index.ConfigurationKeyRules
open Leanux Leanux.WG Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

structure Contracts (P : WGWorld → Prop) : Prop where
  read : Preserves P getDev
  identity : ∀ key,Preserves P (setStaticIdentityPrivateKey key)
  cookie : Preserves P cookiePrecomputeDeviceKeys
  precompute : ∀ pid,Preserves P (precomputeStaticStatic pid)
  expire : ∀ pid,Preserves P (expireCurrentPeerKeypairs pid)
  staged : ∀ pid,Preserves P (sendStagedPackets pid)
  conflict : ∀ key,Preserves P (do
    let peer ← pubkeyLookup key
    if ← branch .setDevOldPeer peer.isSome then
      peerPut peer
      peerRemove peer : WG.M Unit)


theorem keyFinish (P : WGWorld → Prop) (c : Contracts P) (key : Key) :
    Preserves P
      ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyFinish
  unfold WG.andM
  simp (config := {zeta := false}) only [branch]
  repeat' first
  | (rx_retention_head getDev; exact c.read)
  | (rx_retention_head setStaticIdentityPrivateKey; exact c.identity _)
  | (rx_retention_head cookiePrecomputeDeviceKeys; exact c.cookie)
  | (rx_retention_head precomputeStaticStatic; exact c.precompute _)
  | (rx_retention_head expireCurrentPeerKeypairs; exact c.expire _)
  | (rx_retention_head sendStagedPackets; exact c.staged _)
  | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp P)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head ForIn.forIn
     apply list_view_spec id P
     intro x b
     change Preserves P _)
  | rx_retention_step

theorem keyChanged (P : WGWorld → Prop) (c : Contracts P) (key : Key) :
    Preserves P
      ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged) key) := by
  index_unfold _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.keyChanged
  apply preserves_bind ((generatePublic_sameWGWorld key).wp P)
  rintro ⟨pub,ok⟩
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .setDevGenPublic ok) P)
  intro generated
  cases generated with
  | false => exact keyFinish P c key
  | true =>
    cases pub with
    | none =>
      exact preserves_bind (hoare_liftAmbient
        (AmbientM.invariant "a generated public key without a write") P)
        (fun _ => keyFinish P c key)
    | some pub =>
      exact preserves_bind (c.conflict pub) (fun _ => keyFinish P c key)

theorem key (P : WGWorld → Prop) (c : Contracts P) (attrs : DeviceAttrs)
    (peers : Preserves P (devicePeersSource attrs)) :
    Preserves P (deviceKeySource attrs) := by
  rw [(pinned_const _private.Leanux.Proofs.WG.Queues.DeviceStages.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceStages.key_factor) attrs]
  unfold WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | exact peers
    | (rx_retention_head getDev; exact c.read)
    | (rx_retention_head setStaticIdentityPrivateKey; exact c.identity _)
    | (rx_retention_head cookiePrecomputeDeviceKeys; exact c.cookie)
    | (rx_retention_head precomputeStaticStatic; exact c.precompute _)
    | (rx_retention_head expireCurrentPeerKeypairs; exact c.expire _)
    | (rx_retention_head sendStagedPackets; exact c.staged _)
    | (rx_retention_head generatePublic; exact (generatePublic_sameWGWorld _).wp P)
    | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id P
       intro x b
       change Preserves P _)
    | rx_retention_step
  all_goals exact keyChanged P c _

end Leanux.Proofs.WG.Index.ConfigurationKeyRules
