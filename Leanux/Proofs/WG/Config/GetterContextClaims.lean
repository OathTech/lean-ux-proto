import Leanux.Proofs.WG.Config.GetterContextSource

/-! The original setter preserves its optional device-associated context on normal
returns, including errno returns. Resident entry additionally gives raw socket and
selector-table equality; an absent observation alone gives neither. -/
set_option autoImplicit false

namespace Leanux.Proofs.WG.Config.GetterContext
open Leanux Leanux.WG Noise TimerDiscipline Lifetimes Leanux.Proofs.Framing Std.Do
open Leanux.Proofs.WG.Configuration

theorem original_request_context (attrs : DeviceAttrs) (initial : Context) :
    Campaign2.Ensures (wgSetDevice attrs) (fun s=>observation s=initial)
      (fun _ s=>observation s=initial) := by
  intro g ambient ret v after pre run
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp
    (request attrs) g ambient ret v after run
  change view v=view g at same
  change view v=initial
  exact same.trans pre

theorem original_request_resident_context (attrs : DeviceAttrs) (sock : NlSock)
    (fixtures : FixtureDevices) :
    Campaign2.Ensures (wgSetDevice attrs)
      (fun s=>s.wg.device.isSome=true ∧ s.wg.nlSock7=sock ∧ s.wg.fixtureNetDevices=fixtures)
      (fun _ s=>s.wg.device.isSome=true ∧ s.wg.nlSock7=sock ∧ s.wg.fixtureNetDevices=fixtures) := by
  intro g ambient ret v after pre run
  have initial : view g=some (sock,fixtures) := by
    cases hd : g.dev with
    | none => simp [Campaign2.snapshot,Campaign2.core,hd] at pre
    | some d => simpa [view,getterMetadata,hd,Campaign2.snapshot,Campaign2.core] using pre.2
  have final := original_request_context attrs (some (sock,fixtures))
    g ambient ret v after initial run
  change view v=some (sock,fixtures) at final
  cases hd : v.dev with
  | none => simp [view,getterMetadata,hd] at final
  | some d =>
    change v.dev.isSome=true ∧ v.nlSock7=sock ∧ v.fixtureNetDevices=fixtures
    simpa [view,getterMetadata,hd] using final

end Leanux.Proofs.WG.Config.GetterContext
