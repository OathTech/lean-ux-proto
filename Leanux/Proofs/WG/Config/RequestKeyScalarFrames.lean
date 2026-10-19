import Leanux.Proofs.WG.Config.RequestKeyScalarEffects
import Leanux.Proofs.WG.Config.GetterScalarFrames
import Leanux.Proofs.WG.Config.EndpointSources
import Leanux.Proofs.WG.Config.ClearedSources
import Leanux.Proofs.WG.Noise.PortControlSource

/-! Physical getter-scalar frames for cache clearing, socket effects and the complete port setter. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration

theorem clear_source (pid : PeerId) : SameView view (clearPeerEndpointSrc pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a ret v b run
  cases hd:g.dev with
  | none=>
    exact False.elim (clearEndpointSource_missing pid g a ret v b (by simp [peerAt,hd]) run)
  | some d=>
    cases hp:d.peers[pid]? with
    | none=>
      exact False.elim (clearEndpointSource_missing pid g a ret v b (by simp [peerAt,hd,hp]) run)
    | some p=>
      obtain ⟨out,reset,present,_,selected,other⟩:=clearEndpointSource_exact pid d p hp g a ret v b hd run
      funext target
      by_cases same:target=pid
      · subst target
        simp only [view,values,present,hd,Option.bind_some,selected,hp,Option.map_some,cleared_cell]
      · simp only [view,values,present,hd,Option.bind_some,other target same]

theorem socket_frame {α : Type} (action : WG.M α) (frame : SameSocket action) :
    SameView view action := by
  apply frame.of_factor (fun s : WGOwnedView=>values s.dev) view
  intro g
  change GetterScalar.values g.dev=GetterScalar.values (g.dev.map socketDevice)
  cases device:g.dev <;> rfl

theorem port (port : Nat) : SameView view (setPort port) :=
  setPort_frame_source view port read_device clear_source
    (modify_device (fun d=>{d with incomingPort:=port}) (fun _=>rfl))
    (socket_frame _ (socketInit_sameSocket port))
end Leanux.Proofs.WG.Config.GetterScalar
