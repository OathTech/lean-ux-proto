import Leanux.Proofs.WG.Config.GetterContextModel
import Leanux.Proofs.WG.Config.GetterPeerCommandClaims
import Leanux.Proofs.WG.Config.KeyStageSource
import Leanux.Proofs.WG.Config.ZeroPortReadbackFrames
import Leanux.Proofs.WG.Origins.RetainingLifecycle

/-! Metadata projections and source-connected context frames. Port and source clearing reuse existing context and optional material observations. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterContext
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration

def view (g : WGWorld) : Context := (getterMetadata g).map Prod.snd

theorem metadata {α : Type} {action : WG.M α} (frame : SameView getterMetadata action) :
    SameView view action := frame.factor (fun v=>v.map Prod.snd)

theorem modify_device (f : Device→Device) : SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  cases run
  simp only [view,getterMetadata,Option.map_map,Function.comp_def]

theorem identity (key : Key) : SameView view (setStaticIdentityPrivateKey key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  cases hd : g.dev with
  | none =>
    simp [setStaticIdentityPrivateKey,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    have source:=setStaticIdentity_run key d g a hd
    rw [run] at source
    cases source
    simp only [view,getterMetadata,hd,Option.map_some]

theorem cookie : SameView view cookiePrecomputeDeviceKeys := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  cases hd : g.dev with
  | none =>
    simp [cookiePrecomputeDeviceKeys,getDev,hd,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    have source:=cookiePrecompute_run d g a hd
    rw [run] at source
    cases source
    simp only [view,getterMetadata,hd,Option.map_some]

theorem context_equal (g v : WGWorld) (presence : v.dev.isSome=g.dev.isSome)
    (socket : v.nlSock7=g.nlSock7) (selector : v.fixtureNetDevices=g.fixtureNetDevices) :
    view v=view g := by
  simp only [view,getterMetadata,Option.map_map,Function.comp_def,socket,selector]
  cases gd : g.dev <;> cases vd : v.dev <;> simp_all

theorem clear (pid : PeerId) : SameView view (clearPeerEndpointSrc pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  have fields := clearEndpointSource_readbackFrame pid g.nlSock7 g.fixtureNetDevices
    g a ret v b ⟨rfl,rfl⟩ run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.Retaining.clearPeerEndpointSrc_material pid) g a ret v b run
  have present := congrArg Option.isSome same
  apply context_equal g v
  · simpa only [Origins.view,Option.isSome_map] using present
  · exact fields.1
  · exact fields.2

theorem port (port : Nat) : SameView view (setPort port) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  have fields : v.portBound=g.portBound ∧ readbackFrame v g.nlSock7 g.fixtureNetDevices := by
    by_cases zero : port=0
    · subst port
      exact setPort_zero_configurationFrame _ _ _ g a ret v b ⟨rfl,rfl,rfl⟩ run
    · exact setPort_nonzero_configurationFrame port zero _ _ _ g a ret v b ⟨rfl,rfl,rfl⟩ run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (Origins.Retaining.setPort_material port) g a ret v b run
  have present := congrArg Option.isSome same
  apply context_equal g v
  · simpa only [Origins.view,Option.isSome_map] using present
  · exact fields.2.1
  · exact fields.2.2

theorem invalidate (site : Decision) (key : Option KeypairId) :
    SameView getterMetadata (invalidateSource site key) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  unfold invalidateSource
  repeat' getter_cleanup_step initial

theorem expire (pid : PeerId) : SameView getterMetadata (expireCurrentPeerKeypairs pid) := by
  intro initial
  change Preserves (fun g=>getterMetadata g=initial) _
  rw [expireCurrent_source]
  unfold expiryHeadSource expiryTailSource
  simp only [requireNotPending,pure_bind]
  repeat' first
    | (rx_retention_head handshakeClear; exact (GetterCleanup.handshake_clear _).wp (fun v=>v=initial))
    | (rx_retention_head resetLastSentHandshake; exact (GetterPeerCommand.reset_last _).wp (fun v=>v=initial))
    | (rx_retention_head invalidateSource; exact (invalidate _ _).wp (fun v=>v=initial))
    | getter_cleanup_step initial

end Leanux.Proofs.WG.Config.GetterContext
