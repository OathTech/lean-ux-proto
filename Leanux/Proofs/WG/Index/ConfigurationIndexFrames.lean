import Leanux.Proofs.WG.Index.ConfigurationIndexEffects
import Leanux.Proofs.WG.Config.Precomputation
import Leanux.Proofs.WG.Config.EndpointSetSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.ConfigurationIndex
open Leanux Leanux.WG Noise Queues Queues.RxCredits
open Queues.RxCredits.DurableHolders Leanux.Proofs.Framing Lifetimes Std.Do
open Leanux.Proofs.WG.Configuration

theorem frame_core {α : Type} {action : WG.M α} (same : SameView fields action) :
    Preserves Reached.Core action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  exact fields_core w v ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run) pre

theorem configuration_fields {α : Type} {action : WG.M α} (same : SameConfiguration action) :
    SameView fields action := by
  apply same.of_factor (fun s : WGOwnedView => s.dev.map deviceFields)
  intro w
  simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,fields,
    Option.map_map,Function.comp_def]
  rfl

theorem socket_fields {α : Type} {action : WG.M α} (same : SameSocket action) :
    SameView fields action := by
  apply same.of_factor (fun s : WGOwnedView => s.dev.map deviceFields)
  intro w
  simp only [socketView,socketDevice,wgOwnedView,wgStoreView,fields,
    Option.map_map,Function.comp_def]
  rfl

theorem modifyPeer_fields (pid : PeerId) (f : Peer → Peer)
    (same : ∀p, senderPeerCell (f p)=senderPeerCell p) :
    SameView fields (modifyPeer pid f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  change (((getPeer pid >>= fun p => setPeer pid (f p) : WG.M Unit).run w).run a)=
    .ok ((result,v),b) at run
  rw [MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨p,u,c,read,write⟩ := run
  obtain ⟨rfl,rfl,d,device,resident⟩ := getPeer_normal pid w u p a c read
  cases write
  simpa [fields,device] using congrArg some (deviceFields_peerWrite d pid p (f p) resident (same p))

theorem precompute_fields (pid : PeerId) : SameView fields (precomputeStaticStatic pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases device : w.dev with
  | none =>
    simp [precomputeStaticStatic,requireNotPending,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [precomputeStaticStatic,requireNotPending,getPeer,getDev,device,resident,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨result',out,after,executed,effect⟩ := Config.precomputeStaticStatic_returns pid d p resident w a device
      rw [run] at executed
      cases executed
      simp only [fields,device,effect,Option.map_some,Option.some.injEq]
      unfold Config.precomputeDevice
      dsimp only
      split
      · split
        · exact deviceFields_peerWrite d pid p _ resident rfl
        · let firstPeer := {p with precomputedStaticStatic:=(curve25519 d.staticIdentity.staticPrivate p.remoteStatic).1}
          have first := deviceFields_peerWrite d pid p firstPeer resident rfl
          have second := deviceFields_peerWrite (Config.withPeer d pid firstPeer) pid firstPeer
            {p with precomputedStaticStatic:=List.replicate 32 0} (by simp [Config.withPeer]) rfl
          exact second.trans first
      · exact deviceFields_peerWrite d pid p _ resident rfl

theorem read_entry (cs : Ledger) (loans : Reservations) :
    Preserves (Entry cs loans) getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b pre run
  cases hd:w.dev <;> simp [getDev,hd,invariant,AmbientM.invariant] at run
  · cases run
  · obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact pre

end Leanux.Proofs.WG.Index.ConfigurationIndex
