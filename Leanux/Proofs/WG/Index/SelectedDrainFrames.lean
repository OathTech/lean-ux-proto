import Leanux.Proofs.WG.Index.SelectedDrainModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index.SelectedDrain
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do Lifetimes
open Queues.RxCredits
open Noise.DriverTags.Flush

theorem ambient_cut {α : Type} (action : AmbientM α)
    (w v : WGWorld) (a b : Ambient) (x : α)
    (run : (((StateT.lift action : WG.M α).run w).run a) = .ok ((x,v),b)) :
    v = w ∧ action.run a = .ok (x,b) := by
  rw [stateLiftAmbient_run] at run
  cases h : action.run a with
  | error e => simp [h,Except.map] at run
  | ok out =>
    rcases out with ⟨y,c⟩
    simp only [h,Except.map,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨⟨rfl,rfl⟩,rfl⟩ := run
    exact ⟨rfl,rfl⟩

end Leanux.Proofs.WG.Index.SelectedDrain
