import Leanux.Proofs.WG.AllowedIps.AddressBounds
import Leanux.Proofs.WG.AllowedIps.RoutingHistory

/-! Actual setAllowedip guards select a bounded original insertion or return
EINVAL without changing the seven-field WireGuard store view. Negative insertion returns retain their real
sequence/frontier effects. This is a call boundary, not enclosing Netlink closure. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do
set_option maxHeartbeats 1200000
set_option pp.structureInstances false

theorem AddressShape.width (hs : AddressShape ip) (v4 : Bool)
    (ha : ip.addr.isNone = false) (hl : ip.addrLen = if v4 then 4 else 16) :
    ip.addr.getD 0 < 2 ^ rootWidth v4 := by
  cases hx : ip.addr with
  | none => simp [hx] at ha
  | some addr =>
    have hh := hs addr hx
    rw [hl] at hh
    cases v4 <;> simpa [rootWidth, hx] using hh

/-- The selected original call starts after the actual source guards. Its cut
Ambient retains their records, and its seven-field store view equals the entry
view. The insertion returns the actual final WG and Ambient states. -/
def AllowedipOutcome (initial : WGStoreView) (pid : PeerId) (ip : AllowedIpAttrs)
    (ret : Int) (v : WGWorld) (finalAmbient : Ambient) : Prop :=
  (ret = -EINVAL ∧ wgStoreView v = initial) ∨
    ∃ v4 cut cutAmbient, wgStoreView cut = initial ∧ ip.family.getD 0 = (if v4 then AF_INET else AF_INET6) ∧
      ip.addr.getD 0 < 2 ^ rootWidth v4 ∧ ip.cidr.getD 0 ≤ rootWidth v4 ∧
      ((insert (if v4 then 4 else 6) (ip.addr.getD 0) (ip.cidr.getD 0) pid).run cut).run cutAmbient =
        .ok ((ret, v), finalAmbient)

theorem setAllowedip_outcome (pid : PeerId) (ip : AllowedIpAttrs) (hs : AddressShape ip)
    (w v : WGWorld) (ambient finalAmbient : Ambient) (ret : Int)
    (hr : ((setAllowedip pid ip).run w).run ambient = .ok ((ret, v), finalAmbient)) :
    AllowedipOutcome (wgStoreView w) pid ip ret v finalAmbient := by
  have hi (v4 : Bool) :
      ⦃fun u _ => ⌜wgStoreView u = wgStoreView w ∧ ip.family.getD 0 = (if v4 then AF_INET else AF_INET6) ∧ ip.addr.getD 0 < 2 ^ rootWidth v4 ∧ ip.cidr.getD 0 ≤ rootWidth v4⌝⦄
        insert (if v4 then 4 else 6) (ip.addr.getD 0) (ip.cidr.getD 0) pid
      ⦃⇓? result u nextAmbient => ⌜AllowedipOutcome (wgStoreView w) pid ip result u nextAmbient⌝⦄ := by
    intro u cutAmbient hu
    cases hrun : ((insert (if v4 then 4 else 6) (ip.addr.getD 0) (ip.cidr.getD 0) pid).run u).run cutAmbient with
    | error e =>
      dsimp only [StateT.run] at hrun
      simp [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.true, ExceptConds.const, hrun]
    | ok out =>
      rcases out with ⟨⟨result, finish⟩, nextAmbient⟩
      have hq : AllowedipOutcome (wgStoreView w) pid ip result finish nextAmbient :=
        Or.inr ⟨v4, u, cutAmbient, hu.1, hu.2.1, hu.2.2.1, hu.2.2.2, hrun⟩
      dsimp only [StateT.run] at hrun
      simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
        StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
        Pure.pure, ExceptConds.true, ExceptConds.const, hrun] using hq
  have h4 : ⦃fun u _ => ⌜wgStoreView u = wgStoreView w ∧ ip.family.getD 0 = AF_INET ∧ ip.addr.getD 0 < 2 ^ 32 ∧ ip.cidr.getD 0 ≤ 32⌝⦄
      insert 4 (ip.addr.getD 0) (ip.cidr.getD 0) pid
      ⦃⇓? result u nextAmbient => ⌜AllowedipOutcome (wgStoreView w) pid ip result u nextAmbient⌝⦄ := by simpa [rootWidth] using hi true
  have h6 : ⦃fun u _ => ⌜wgStoreView u = wgStoreView w ∧ ip.family.getD 0 = AF_INET6 ∧ ip.addr.getD 0 < 2 ^ 128 ∧ ip.cidr.getD 0 ≤ 128⌝⦄
      insert 6 (ip.addr.getD 0) (ip.cidr.getD 0) pid
      ⦃⇓? result u nextAmbient => ⌜AllowedipOutcome (wgStoreView w) pid ip result u nextAmbient⌝⦄ := by simpa [rootWidth] using hi false
  have hspec : ⦃fun u _ => ⌜wgStoreView u = wgStoreView w⌝⦄ setAllowedip pid ip
      ⦃⇓? result u nextAmbient => ⌜AllowedipOutcome (wgStoreView w) pid ip result u nextAmbient⌝⦄ := by
    mvcgen [setAllowedip, WG.orM, WG.andM, h4, h6, branch, AmbientM.branch]
    all_goals try dsimp +zetaDelta only at *
    all_goals try simp_all only [Bool.not_eq_true', beq_iff_eq, decide_eq_true_eq, rootWidth, Bool.true_eq_false, Bool.false_eq_true]
    all_goals try simp only [true_and, and_true]
    all_goals first
      | exact Or.inl ⟨rfl, by assumption⟩
      | apply hs.width true
      | apply hs.width false
      | assumption
    all_goals simp_all
    all_goals cases hx : ip.addr <;> simp_all
  have hh := hspec w ambient rfl
  dsimp only [StateT.run] at hr
  simpa [WP.wp, PredTrans.pushArg, PredTrans.pushExcept, PredTrans.apply,
    StateT.run, Except.instWP._aux_1, ExceptT.run, Id.run, PredTrans.pure,
    Pure.pure, ExceptConds.true, ExceptConds.const, hr] using hh

/-- Parser success supplies the address-shape premise rather than requiring
it from callers. Malformed entries keep their separate constructor. -/
theorem parsed_setAllowedip_outcome (j : Lean.Json) (what : String) (ip : AllowedIpAttrs)
    (hp : parseAllowedIp j what = .ok (.attrs ip)) (pid : PeerId)
    (w v : WGWorld) (ambient finalAmbient : Ambient) (ret : Int)
    (hr : ((setAllowedip pid ip).run w).run ambient = .ok ((ret, v), finalAmbient)) :
    AllowedipOutcome (wgStoreView w) pid ip ret v finalAmbient :=
  setAllowedip_outcome pid ip (parseAllowedIp_shape j what (.attrs ip) hp) w v ambient finalAmbient ret hr
/-- The guard bridge composes with the existing actual-insertion history rule;
its selected family is proved from the actual guard, not supplied by a caller. -/
theorem setAllowedip_routing (pid : PeerId) (ip : AllowedIpAttrs) (hs : AddressShape ip)
    (w v : WGWorld) (ambient finalAmbient : Ambient) (d : Device) (hd : w.dev = some d) (hi : RoutingInvariant d t4 t6)
    (hp : d.peers[pid]? = some p) (he4 : FlatAgree 32 t4 xs.1) (he6 : FlatAgree 128 t6 xs.2)
    (ret : Int) (hr : ((setAllowedip pid ip).run w).run ambient = .ok ((ret, v), finalAmbient)) :
    (ret = -EINVAL ∧ wgStoreView v = wgStoreView w) ∨
      ∃ v4 out u4 u6, ip.family.getD 0 = (if v4 then AF_INET else AF_INET6) ∧
        v.dev = some out ∧ RoutingInvariant out u4 u6 ∧
        FlatAgree 32 u4 ((RoutingCall.insert v4 (ip.addr.getD 0) (ip.cidr.getD 0) pid ret).flat xs).1 ∧
        FlatAgree 128 u6 ((RoutingCall.insert v4 (ip.addr.getD 0) (ip.cidr.getD 0) pid ret).flat xs).2 := by
  rcases setAllowedip_outcome pid ip hs w v ambient finalAmbient ret hr with reject | ⟨v4, cut, cutAmbient, hk, hf, ha, hc, hrun⟩
  · exact Or.inl reject
  · have hcut : cut.dev = some d := (congrArg WGStoreView.dev hk).trans hd
    have step : RoutingStep cut cutAmbient (.insert v4 (ip.addr.getD 0) (ip.cidr.getD 0) pid ret) v finalAmbient :=
      .insert ha hc ⟨d, p, hcut, hp⟩ hrun
    obtain ⟨out, u4, u6, hout, hinv, h4, h6⟩ := step.refines hcut hi he4 he6
    exact Or.inr ⟨v4, out, u4, u6, hf, hout, hinv, h4, h6⟩

end Leanux.Proofs.WG.AllowedIps
