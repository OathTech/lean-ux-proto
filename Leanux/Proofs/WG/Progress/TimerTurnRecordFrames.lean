import Leanux.Env

/-! The original next-site read returns without changing the product state. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Env

theorem peekNextSite_exact (w : World) :
    Env.peekNextSite.run w = .ok
      (w.ambient.hidden.bind (fun rs=>(rs.find? (fun r=>!HiddenSite.passive r.site)).map (·.site)),w) := by
  unfold Env.peekNextSite
  rw [StateT.run_bind]
  change ((Except.ok (w.ambient,w) : Except Stop _) >>= _) = _
  dsimp only [Bind.bind,Except.bind]
  cases w.ambient.hidden <;> rfl


end Leanux.Proofs.WG.Progress.RecordSuffix
