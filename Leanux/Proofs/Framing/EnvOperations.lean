import Leanux.Proofs.Framing.EnvLeaves
import Leanux.Proofs.WG.Environment.ObservationSource

/-! Original environment contracts over the original 43 store fields.
MTU changes mask precisely the three original device scalars. Routing remains
outside the seven original WireGuard store fields, with its actual effects
and Stops retained by the native adapters. -/
namespace Leanux.Proofs.Framing
open Leanux Leanux.WG Std.Do Leanux.Proofs.WG.Lifetimes

def envScalarDevice (d : Device) : Device :=
  { d with mtu := 0, inet4Dev := false, inet6Dev := false }
def envScalarStore (v : ProductStore43) : ProductStore43 :=
  (v.1, v.2.1, v.2.2.1, { v.2.2.2 with dev := v.2.2.2.dev.map envScalarDevice })
def envScalarView (w : World) : ProductStore43 := envScalarStore (productStoreView w)
def envScalarWGView (g : WGWorld) : WGStoreView :=
  { wgStoreView g with dev := g.dev.map envScalarDevice }
abbrev SameEnvScalar (a : Leanux.M α) := SameView envScalarView a

theorem modifyDev_envScalar_spec (P : ProductStore43 → Prop) (f : Device → Device)
    (hf : ∀ d, envScalarDevice (f d) = envScalarDevice d) :
    Hoare (MonadLift.monadLift (modifyDev f) : Leanux.M Unit)
      (fun w => P (envScalarView w)) (fun _ w => P (envScalarView w)) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w x v hp hr
  cases hr
  simpa [envScalarView, envScalarStore, productStoreView, wgStoreView, modifyDev,
    liftWG, Option.map_map, Function.comp_def, hf] using hp

theorem wgSetMtu_sameEnvScalar (mtu : Int) :
    SameEnvScalar (MonadLift.monadLift (WG.setMtu mtu) : Leanux.M Int) := by
  have h : SameView envScalarWGView (WG.setMtu mtu) := by
    intro initial
    unfold Hoare
    mvcgen [WG.setMtu, modifyDev]
    all_goals simp_all (config := { zetaDelta := true }) [envScalarWGView, wgStoreView, envScalarDevice,
      Option.map_map, Function.comp_def]
    all_goals assumption
  apply sameView_liftWG envScalarView envScalarWGView (WG.setMtu mtu) h
  intro w g ambient hg
  change (fsStoreView w.fs, w.tasks, (w.seccomp.filters, w.seccomp.nextFilter),
    envScalarWGView g) = (_, _, _, envScalarWGView w.wg)
  rw [hg]
  rfl

theorem setMtu_sameEnvScalar (mtu : Nat) : SameEnvScalar (Env.setMtu mtu) := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => envScalarView w = k) (fun _ _ h => h)
  have hg := productGetWG_spec (fun s => envScalarStore s = k)
  have hd := productGetDev_spec (fun s => envScalarStore s = k)
  have hr := fun α (a : Net.M α) => productRouting_spec a (fun s => envScalarStore s = k)
  have hm := fun n => (wgSetMtu_sameEnvScalar n).wp (fun s => s = k)
  have hl (α β : Type) := list_view_spec (m := Except Stop) envScalarView
    (α := α) (β := β) (fun s => s = k)
  unfold Hoare at ha hg hd hr
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT,
    Env.setMtu, Env.inetdevDestroy, getRouting, modifyRouting, hg, hd, hr, hm, ha, hl,
    skipCut, unsupported]

theorem senderSource_sameKernel (family dest tos : Nat) (ll : Bool) :
    SameProductStore (Env.senderSource family dest tos ll) := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  have hr := fun α (a : Net.M α) => productRouting_spec a (fun s => s = k)
  unfold Hoare at ha hr
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.senderSource, getRouting, hr, ha, unsupported]

theorem routeIntoWg0_sameKernel : SameProductStore Env.routeIntoWg0 := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  have hd := productGetDev_spec (fun s => s = k)
  have hr := fun α (a : Net.M α) => productRouting_spec a (fun s => s = k)
  unfold Hoare at ha hd hr
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.routeIntoWg0, Env.outsideWindow,
    getRouting, modifyRouting, getEnv, modifyEnv, getAmbient, modifyAmbient,
    hd, hr, ha]
  all_goals simp_all [productStoreView]

theorem wgDeladdr_sameKernel (family : Nat) : SameProductStore (Env.wgDeladdr family) := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  have hg := productGetWG_spec (fun s => s = k)
  have hr := fun α (a : Net.M α) => productRouting_spec a (fun s => s = k)
  unfold Hoare at ha hg hr
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.wgDeladdr, getRouting, modifyRouting,
    hg, hr, ha, unsupported]

theorem wgDelroute_sameKernel (family : Nat) :
    SameProductStore (Env.wgDelroute family false 0 0 0 0 0) := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  have hg := productGetWG_spec (fun s => s = k)
  have hr := fun α (a : Net.M α) => productRouting_spec a (fun s => s = k)
  unfold Hoare at ha hg hr
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.wgDelroute, getRouting, modifyRouting,
    hg, hr, ha, unsupported]

theorem xmitPacket_sameKernel (family addr : Nat) (payload : List UInt8) (mtu tos : Nat) :
    SameProductStore (Env.xmitPacket family addr payload mtu tos) := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  unfold Hoare at ha
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.xmitPacket, ha, invariant, unsupported]

theorem xmitPackets_sameKernel (family addr : Nat) (payload : List UInt8) (opts : Env.XmitOpts) :
    SameProductStore (Env.xmitPackets family addr payload opts) := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  have hd := productGetDev_spec (fun s => s = k)
  have hp := fun family addr payload mtu tos =>
    (xmitPacket_sameKernel family addr payload mtu tos).wp (fun s => s = k)
  unfold Hoare at ha hd
  mvcgen [-Std.Do.Spec.monadLift_StateT, Env.xmitPackets, getEnv, hd, hp, ha, unsupported]
  all_goals simp_all [productStoreView]

theorem observeTail_sameKernel : SameProductStore Leanux.Proofs.WG.Environment.observeTail := by
  apply SameView.of_wp
  intro k
  have ha := fun α (a : AmbientM α) => productAmbient_spec a
    (fun w => productStoreView w = k) (fun _ _ h => h)
  have hg := productGetWG_spec (fun s => s = k)
  have hr := fun α (a : Net.M α) => productRouting_spec a (fun s => s = k)
  have hc := requireNoCryptWork_sameKernel.wp (fun s => s = k)
  have hd := deliverSent_sameKernel.wp (fun s => s = k)
  unfold Hoare at ha hg hr
  mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Proofs.WG.Environment.observeTail,
    getRouting, getEnv, modifyEnv, hg, hr, ha, hc, hd, unsupported]
  all_goals simp_all [productStoreView]

end Leanux.Proofs.Framing
