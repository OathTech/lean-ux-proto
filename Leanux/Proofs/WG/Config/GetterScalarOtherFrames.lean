import Leanux.Proofs.WG.Config.GetterScalarOtherModel
import Leanux.Proofs.WG.Config.GetterScalarClaims
import Leanux.Proofs.WG.Config.ScalarCommandSource

/-! Native view transports and exact nonselected field projections. Normal-return preservation permits deletion. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.GetterScalar.Other
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do Queues
open Queues.RxCredits Leanux.Proofs.WG.Configuration

def Holds (selected : PeerId) (entry : GetterScalar.Map) (g : WGWorld) : Prop :=
  ExceptAt selected entry (GetterScalar.view g)

theorem retained {α : Type} (selected : PeerId) (entry : GetterScalar.Map)
    (action : WG.M α)
    (keep : ∀ initial, Ensures action (GetterScalar.Retained initial)
      (fun _=>GetterScalar.Retained initial)) :
    Preserves (Holds selected entry) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  have step:=keep (GetterScalar.view g) g a result final b (fun _ _ h=>h) run
  intro pid value other present
  exact pre pid value other (step pid value present)

theorem frame {α : Type} (selected : PeerId) (entry : GetterScalar.Map)
    (action : WG.M α) (same : SameView GetterScalar.view action) :
    Preserves (Holds selected entry) action :=
  retained selected entry action (fun initial=>GetterScalar.of_frame initial action same)

theorem write (selected : PeerId) (entry : GetterScalar.Map) (p : Peer) :
    Preserves (Holds selected entry) (setPeer selected p) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  cases run
  intro pid value other present
  apply pre pid value other
  cases device:g.dev with
  | none => simp [GetterScalar.view,GetterScalar.values,device] at present
  | some d =>
    simpa [GetterScalar.view,GetterScalar.values,device,
      Std.TreeMap.getElem?_insert,Ne.symm other] using present

theorem read_device (P : WGWorld → Prop) : Preserves P getDev := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro g a result final b pre run
  obtain ⟨rfl,rfl,_⟩:=Queues.RxCredits.DecryptCarrier.getDev_current a b run
  exact pre

theorem read_peer (P : WGWorld → Prop) (pid : PeerId) : Preserves P (getPeer pid) :=
  hoare_consequence (getPeer_spec pid P) (fun _ h=>h) (fun _ _ h=>h.1)

theorem acquire (pid : PeerId) : SameView GetterScalar.view (peerGet pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g a result final b run
  cases result
  obtain ⟨d,p,device,resident,_,out⟩:=peerGet_loan pid g final a b run
  change g.dev=some d at device
  have target:final.dev=some (Index.acquirePeer d pid p):=congrArg WGStoreView.dev out
  change GetterScalar.values final.dev=GetterScalar.values g.dev
  rw [target,device]
  exact GetterScalar.write_values d pid p {p with refcount:=p.refcount+1} resident rfl

end Leanux.Proofs.WG.Config.GetterScalar.Other
