import Leanux.Proofs.WG.Config.RequestInputFrames
import Leanux.Proofs.WG.Config.FwmarkEffects

/-! Substantive fwmark and source-clearing effects of the actual prefix. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.RequestOrder
open Leanux Leanux.WG Leanux.Proofs.Logged
open Leanux.Proofs.WG.Configuration

open Leanux.Proofs.WG.Noise in
theorem fwmarkSource_fields (attrs : DeviceAttrs) (initial : WGWorld) (a : Ambient) :
    Ensures (fwmarkSource attrs) (fun w => w = initial)
      (fun _ v => MarkInput attrs (Campaign2.snapshot initial a).wg
        (Campaign2.snapshot v a).wg) := by
  intro w ambient result final after pre run
  subst w
  cases mark : attrs.fwmark with
  | none =>
    simp [fwmarkSource,mark,branch,AmbientM.branch] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    simp [MarkInput,markDevice,mark,Campaign2.snapshot,Campaign2.core,
      ClaimView.clearedPeers]
    intro d hd q
    simp [hd]
  | some value =>
    cases hd : initial.dev with
    | none =>
      simp [fwmarkSource,mark,branch,AmbientM.branch,modifyDev,getDev,hd,
        invariant,AmbientM.invariant] at run
      cases run
    | some d =>
      let updated := {d with fwmark := value}
      let middle := {initial with dev := some updated}
      let next := {ambient with steps := ambient.steps.push {decision := .setDevFwmark, outcome := true, netRx := ambient.netRxSection}}
      let tail : WG.M Unit := do
        fwmarkClearLoop d.peerList
        _ ← branch .setDevFwmarkPeerIter false
      have source : ((fwmarkSource attrs).run initial).run ambient =
          (tail.run middle).run next := by
        simp [fwmarkSource,mark,branch,AmbientM.branch,modifyDev,getDev,hd,
          tail,middle,updated,next]
      rw [source] at run
      have loop : Ensures (fwmarkClearLoop d.peerList)
          (fun w => w.dev.map withoutPeers = some (withoutPeers updated) ∧
            clearedPeers d w [] ∧ w.portBound = initial.portBound ∧
            readbackFrame w initial.nlSock7 initial.fixtureNetDevices)
          (fun _ w => w.dev.map withoutPeers = some (withoutPeers updated) ∧
            clearedPeers d w d.peerList ∧ w.portBound = initial.portBound ∧
            readbackFrame w initial.nlSock7 initial.fixtureNetDevices) := by
        intro w env ret v out point execution
        have fields := fwmarkClearLoop_effects d d.peerList [] _ w env ret v out
          ⟨point.1,point.2.1⟩ execution
        have frame := endpointClearLoop_configurationFrame .setDevFwmarkPeerIter
          d.peerList initial.portBound initial.nlSock7 initial.fixtureNetDevices
          w env ret v out point.2.2 execution
        exact ⟨fields.1,by simpa using fields.2,frame⟩
      have tailLaw : Ensures tail
          (fun w => w.dev.map withoutPeers = some (withoutPeers updated) ∧
            clearedPeers d w [] ∧ w.portBound = initial.portBound ∧
            readbackFrame w initial.nlSock7 initial.fixtureNetDevices)
          (fun _ w => w.dev.map withoutPeers = some (withoutPeers updated) ∧
            clearedPeers d w d.peerList ∧ w.portBound = initial.portBound ∧
            readbackFrame w initial.nlSock7 initial.fixtureNetDevices) := by
        unfold tail
        refine ensures_bind _ _ loop ?_
        intro _ w env ret v out point execution
        simp [branch,AmbientM.branch] at execution
        rcases execution with ⟨⟨rfl,rfl⟩,rfl⟩
        exact point
      have effects := tailLaw middle next result final after
        (by simp [middle,updated,clearedPeers,readbackFrame]) run
      simpa [MarkInput,markDevice,mark,Campaign2.snapshot,Campaign2.core,hd,
        ClaimView.clearedPeers,clearedPeers,readbackFrame,updated] using effects

end Leanux.Proofs.WG.Config.RequestOrder
