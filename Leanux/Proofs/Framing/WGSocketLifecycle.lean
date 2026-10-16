import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.WGOwned
import Leanux.Proofs.Framing.Tools
import Leanux.WG.Socket

/-! Canonical socket-control frames. Only the two socket labels and incoming
port are masked. The other eleven-field observations and complete resident
objects remain; actual Ambient inputs and outputs are unrestricted. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def socketDevice (d : Device) : Device :=
  {d with sock4 := none, sock6 := none, incomingPort := 0}

def socketView (g : WGWorld) : WGOwnedView :=
  {wgOwnedView g with dev := g.dev.map socketDevice}

abbrev SameSocket (a : WG.M α) := SameView socketView a

theorem modifyDev_socket_spec (P : WGOwnedView → Prop) (f : Device → Device)
    (hf : ∀ d, socketDevice (f d) = socketDevice d) :
    ⦃fun w => ⌜P (socketView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (socketView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hp hr
  cases hr
  simpa [socketView, wgOwnedView, wgStoreView, modifyDev,
    Option.map_map, Function.comp_def, hf] using hp

theorem sockFree_sameWGWorld (sock : Option Nat) :
    SameView (id : WGWorld → WGWorld) (sockFree sock) := by
  apply SameView.of_wp
  intro initial
  have hi : Hoare (iputReport true : WG.M Unit)
      (fun w => w = initial) (fun _ w => w = initial) :=
    hoare_liftAmbient (AmbientM.iputReport true) (fun w => w = initial)
  unfold Hoare at hi
  mvcgen [sockFree, branch, AmbientM.branch, hi]

theorem socketReinit_sameSocket (new4 new6 : Option Nat) :
    SameSocket (socketReinit new4 new6) := by
  apply SameView.of_wp
  intro initial
  have hs := fun sock => ((sockFree_sameWGWorld sock).factor socketView).wp (fun s => s = initial)
  have hm := modifyDev_socket_spec (fun s => s = initial)
  mvcgen [socketReinit, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant, hs, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [socketView, socketDevice]

theorem socketInit_sameSocket (port : Nat) : SameSocket (socketInit port) := by
  apply SameView.of_wp
  intro initial
  have hh (site : HiddenSite) : Hoare (hidden site : WG.M (List UInt8))
      (fun w => socketView w = initial) (fun _ w => socketView w = initial) :=
    hoare_liftAmbient (AmbientM.hidden site) (fun w => socketView w = initial)
  have hs := fun a b => (socketReinit_sameSocket a b).wp (fun s => s = initial)
  have hi : Hoare (iputReport true : WG.M Unit)
      (fun w => socketView w = initial) (fun _ w => socketView w = initial) :=
    hoare_liftAmbient (AmbientM.iputReport true) (fun w => socketView w = initial)
  unfold Hoare at hh hi
  mvcgen [socketInit, getDev, invariant, AmbientM.invariant,
    unsupported, AmbientM.unsupported, hh, hs, hi]

end Leanux.Proofs.Framing
