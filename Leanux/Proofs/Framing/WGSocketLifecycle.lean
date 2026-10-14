import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.Framing.Tools
import Leanux.WG.Socket

/-! Canonical socket-control frames. Only the two socket labels and incoming
port are masked; device presence, complete resident objects, allocation
frontiers and every other Kernel field remain. These three original helpers
inspect socket/device scalars and records, never resident peer/key/packet
objects. That source fact is separate from the normal-return frame. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def socketDevice (d : Device) : Device :=
  {d with sock4 := none, sock6 := none, incomingPort := 0}

def socketKernel (k : Kernel) : Kernel := {k with wg := k.wg.map socketDevice}

def socketKernelView (w : World) : Kernel := socketKernel w.k

abbrev SameSocketKernel (a : M α) := SameView socketKernelView a

theorem modifyDev_socket_spec (P : Kernel → Prop) (f : Device → Device)
    (hf : ∀ d, socketDevice (f d) = socketDevice d) :
    ⦃fun w => ⌜P (socketKernelView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (socketKernelView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [socketKernelView, socketKernel, modifyDev, modifyK,
    Option.map_map, Function.comp_def, hf] using hp

theorem sockFree_sameKernel (sock : Option Nat) : SameKernel (sockFree sock) := by
  apply SameView.of_wp
  intro initial
  mvcgen [sockFree, branch]

theorem socketReinit_sameSocketKernel (new4 new6 : Option Nat) :
    SameSocketKernel (socketReinit new4 new6) := by
  apply SameView.of_wp
  intro initial
  have hs := fun sock => (SameView.of_sameKernel socketKernel (sockFree_sameKernel sock)).wp (fun s => s = initial)
  have hm := modifyDev_socket_spec (fun s => s = initial)
  mvcgen [socketReinit, getDev, getK, branch, invariant, hs, hm]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [socketKernelView, socketKernel, socketDevice]

theorem socketInit_sameSocketKernel (port : Nat) : SameSocketKernel (socketInit port) := by
  apply SameView.of_wp
  intro initial
  have hh := fun site => (SameView.of_sameKernel socketKernel (hidden_sameKernel site)).wp (fun s => s = initial)
  have hs := fun a b => (socketReinit_sameSocketKernel a b).wp (fun s => s = initial)
  mvcgen [socketInit, getDev, getK, invariant, unsupported, hh, hs]

end Leanux.Proofs.Framing
