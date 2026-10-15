import Leanux.Proofs.Framing.EnvLeaves
import Leanux.Proofs.Framing.Tools
import Leanux.Proofs.WG.Environment.ObservationSource

/-! Original environment leaves. Their source inspects World/container/scalar
fields and packet bytes, never resolved peer/key/packet stores. MTU changes use
an explicit scalar mask rather than an unchanged-Kernel claim. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do

def envScalarDevice (d : Device) : Device :=
  { d with mtu := 0, inet4Dev := false, inet6Dev := false }
def envScalarKernel (k : Kernel) : Kernel := { k with wg := k.wg.map envScalarDevice }
def envScalarView (w : World) : Kernel := envScalarKernel w.k
abbrev SameEnvScalar (a : M α) := SameView envScalarView a

theorem modifyDev_envScalar_spec (P : Kernel → Prop) (f : Device → Device)
    (hf : ∀ d, envScalarDevice (f d) = envScalarDevice d) :
    ⦃fun w => ⌜P (envScalarView w)⌝⦄ modifyDev f
    ⦃⇓? _ w => ⌜P (envScalarView w)⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases hr
  simpa [envScalarView, envScalarKernel, modifyDev, modifyK,
    Option.map_map, Function.comp_def, hf] using hp

theorem wgSetMtu_sameEnvScalar (mtu : Int) : SameEnvScalar (WG.setMtu mtu) := by
  apply SameView.of_wp
  intro initial
  have hm := modifyDev_envScalar_spec (fun k => k = initial)
  mvcgen [WG.setMtu, hm]
  all_goals simp [envScalarDevice]

theorem setMtu_sameEnvScalar (mtu : Nat) : SameEnvScalar (Env.setMtu mtu) := by
  apply SameView.of_wp
  intro initial
  have hm := fun n => (wgSetMtu_sameEnvScalar n).wp (fun k => k = initial)
  have hs := (SameView.of_sameKernel envScalarKernel (skipCut_sameKernel allocCuts)).wp (fun k => k = initial)
  mvcgen [Env.setMtu, getDev, getK, invariant, hm, hs]

theorem senderSource_sameKernel (family dest tos : Nat) (ll : Bool) : SameKernel (Env.senderSource family dest tos ll) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.senderSource, getK, getDev, invariant, unsupported]

theorem fixtureSend_sameKernel  : SameKernel (Env.fixtureSend) := by
  apply sameKernel_of_wp
  intro k
  have hs := sameKernel_wp _ (skipCut_sameKernel ([.ipIdentKey, .ipIdentReserve, .flowHashSecret] ++ allocCuts)) (fun s => s = k)
  mvcgen [Env.fixtureSend, getK, getDev, invariant, unsupported, hs]

theorem routeIntoWg0_sameKernel  : SameKernel (Env.routeIntoWg0) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.routeIntoWg0, getK, getDev, invariant, unsupported]

theorem wgDeladdr_sameKernel (family : Nat) : SameKernel (Env.wgDeladdr family) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.wgDeladdr, getK, getDev, invariant, unsupported]

theorem wgDelroute_sameKernel (family : Nat) : SameKernel (Env.wgDelroute family) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.wgDelroute, getK, getDev, invariant, unsupported]

theorem xmitPacket_sameKernel (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) : SameKernel (Env.xmitPacket family addr payload mtu tos) := by
  apply sameKernel_of_wp
  intro k
  mvcgen [Env.xmitPacket, getK, getDev, invariant, unsupported]

theorem xmitPackets_sameKernel (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) : SameKernel (Env.xmitPackets family addr payload opts) := by
  apply sameKernel_of_wp
  intro k
  have hp := fun family addr payload mtu tos => sameKernel_wp _ (xmitPacket_sameKernel family addr payload mtu tos) (fun s => s = k)
  mvcgen [Env.xmitPackets, getK, getDev, invariant, unsupported, hp]

theorem observeTail_sameKernel  : SameKernel (Leanux.Proofs.WG.Environment.observeTail) := by
  apply sameKernel_of_wp
  intro k
  have hr := sameKernel_wp _ requireNoCryptWork_sameKernel (fun s => s = k)
  have hd := sameKernel_wp _ deliverSent_sameKernel (fun s => s = k)
  mvcgen [Leanux.Proofs.WG.Environment.observeTail, getK, getDev, invariant, unsupported, hr, hd]

end Leanux.Proofs.Framing
