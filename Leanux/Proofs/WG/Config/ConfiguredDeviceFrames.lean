import Leanux.Proofs.WG.Config.ExpiryEffects
import Leanux.Proofs.WG.AllowedIps.RoutingDeviceFrames
import Leanux.Proofs.WG.Queues.DeviceStages

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Lifetimes Std.Do Leanux.Proofs.WG.Configuration

theorem configuration_base {α : Type} (action : WG.M α) (same : SameConfiguration action) :
    SameView BaseCoherence.view action := by
  apply same.of_factor (fun k : WGOwnedView =>
    ((k.dev.map Device.peerList).getD [],(k.dev.map Device.peerHashtable).getD [])) BaseCoherence.view
  intro w
  simp [configurationView,configurationDevice,BaseCoherence.view,BaseCoherence.slots,
    BaseCoherence.rows,Option.map_map,Function.comp_def]

theorem socket_base {α : Type} (action : WG.M α) (same : SameSocket action) :
    SameView BaseCoherence.view action := by
  apply same.of_factor (fun k : WGOwnedView =>
    ((k.dev.map Device.peerList).getD [],(k.dev.map Device.peerHashtable).getD [])) BaseCoherence.view
  intro w
  simp [socketView,socketDevice,BaseCoherence.view,BaseCoherence.slots,
    BaseCoherence.rows,Option.map_map,Function.comp_def]

theorem precompute_base (pid : PeerId) :
    SameView BaseCoherence.view (precomputeStaticStatic pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have raw := (ProjectedAction.iff_run_ambient _ _ _).mp
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCreation.precompute_fields) pid)
    w a result v b run
  have kept := (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCreation.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCreation.fields_transport) raw
  have identity := (ProjectedAction.iff_run_ambient _ _ _).mp (ConfiguredIdentity.precompute pid)
    w a result v b run
  exact Prod.ext
    (congrArg (fun x : Option (List PeerId) => x.getD []) kept.2)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherence.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.rows_of_configured) identity)

theorem expire_base (pid : PeerId) :
    SameView BaseCoherence.view (expireCurrentPeerKeypairs pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases device : w.dev with
  | none =>
    simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
      IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
      device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [expireCurrentPeerKeypairs,requireNotPending,handshakeClear,
        IndexOwner.peerDeref,IndexOwner.peerWord,getPeer,getDev,
        device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨now,finalDevice⟩ := expireCurrent_exact pid d p resident
        w a result v b device run
      have invalid (d : Device) (kp : Option KeypairId) :
          ((invalidateDevice d kp).peerList,(invalidateDevice d kp).peerHashtable)=
          (d.peerList,d.peerHashtable) := by
        cases kp with
        | none => rfl
        | some kid =>
          cases found : d.keypairs[kid]? <;> simp [invalidateDevice,found]
      change BaseCoherence.view v=BaseCoherence.view w
      simp only [BaseCoherence.view,BaseCoherence.slots,BaseCoherence.rows,device,finalDevice,
        Option.map_some,Option.getD_some]
      rw [expiredDevice,invalid,invalid]
      rfl


end Leanux.Proofs.WG.Config.OwnerConfiguration
