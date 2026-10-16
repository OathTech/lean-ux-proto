import Leanux.Proofs.Framing.Projection
import Leanux.Proofs.WG.Keypairs.Frames.WGBase
import Leanux.WG.Peer

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Balanced original peer reference acquisition and repayment. The endpoint
view retains the original seven WG store fields outside the peer map and every
complete peer record pointwise. It deliberately does not assert equality of TreeMap shapes.
These are normal-return contracts over the actual WG and Ambient stack. -/
namespace Leanux.Proofs.Framing.PeerBorrow
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def outsidePeers (k : WGStoreView) : WGStoreView :=
  { k with dev := k.dev.map fun d => { d with peers := {} } }

def resident (k : WGStoreView) (pid : PeerId) : Option Peer :=
  k.dev.bind fun d => d.peers[pid]?

def view (w : WGWorld) : WGStoreView × (PeerId → Option Peer) :=
  (outsidePeers (wgStoreView w), resident (wgStoreView w))

/-- A successful acquisition changes only the selected resident peer's
reference count. Positivity is a conclusion of the original call. -/
def Borrowed (initial : WGStoreView) (result : Option PeerId) (current : WGStoreView) : Prop :=
  match result with
  | none => current = initial
  | some pid => ∃ d p, initial.dev = some d ∧ d.peers[pid]? = some p ∧
      0 < p.refcount ∧ current = { initial with dev := some (
        { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } }) }

theorem refcountIncNotZero_spec (old : Nat) :
    ⦃fun (_ : Ambient) => ⌜True⌝⦄ (refcountIncNotZero old : AmbientM Bool)
    ⦃⇓? live _ => ⌜live = (old != 0)⌝⦄ := by
  mvcgen [refcountIncNotZero, branchCmp, branchCmpExcluded, branch, unsupported,
    AmbientM.branchCmp, AmbientM.branchCmpExcluded, AmbientM.branch, AmbientM.unsupported]

theorem refcountDecAndTest_spec (old : Nat) :
    ⦃fun (_ : Ambient) => ⌜True⌝⦄ (refcountDecAndTest old : AmbientM Bool)
    ⦃⇓? released _ => ⌜0 < old ∧ released = (old == 1)⌝⦄ := by
  mvcgen [refcountDecAndTest, branchCmp, branchCmpExcluded, branch, unsupported,
    AmbientM.branchCmp, AmbientM.branchCmpExcluded, AmbientM.branch, AmbientM.unsupported]
  all_goals simp_all
  all_goals omega

theorem acquire_spec (peer : Option PeerId) (initial : WGStoreView) :
    ⦃fun w => ⌜(wgStoreView w) = initial⌝⦄ peerGetMaybeZero peer
    ⦃⇓? result w => ⌜(result = none ∨ result = peer) ∧ Borrowed initial result (wgStoreView w)⌝⦄ := by
  mvcgen [peerGetMaybeZero, requireNotPending, getPeer, getDev, setPeer,
    modifyDev, refcountIncNotZero, branchCmp, branchCmpExcluded, branch,
    invariant, unsupported, AmbientM.branchCmp, AmbientM.branchCmpExcluded,
    AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals subst_vars
  all_goals simp_all [Borrowed, wgStoreView]
  all_goals first
    | (refine ⟨_, _, ?_, ?_, ?_, ?_⟩ <;> first | assumption | rfl | omega)
    | omega

theorem restore_view (initial : WGStoreView) (d : Device) (pid : PeerId) (p : Peer)
    (hd : initial.dev = some d) (hp : d.peers[pid]? = some p) :
    (outsidePeers { initial with dev := some { d with peers :=
        (d.peers.insert pid { p with refcount := p.refcount + 1 }).insert pid p } },
      resident { initial with dev := some { d with peers :=
        (d.peers.insert pid { p with refcount := p.refcount + 1 }).insert pid p } }) =
      (outsidePeers initial, resident initial) := by
  apply Prod.ext
  · simp [outsidePeers, hd]
  · funext j
    simp only [resident, hd, Option.bind_some, Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq]
    by_cases h : pid = j <;> simp_all

theorem getPeer_known (initial : WGStoreView) (d : Device) (pid : PeerId) (p : Peer)
    (hd : initial.dev = some d) (hp : d.peers[pid]? = some p) :
    ⦃fun w => ⌜wgStoreView w = initial⌝⦄ getPeer pid
    ⦃⇓? result w => ⌜result = p ∧ wgStoreView w = initial⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hk hr
  have hw : w.dev = some d := (congrArg WGStoreView.dev hk).trans hd
  have he : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient) := by
    simp [getPeer, getDev, hw, hp] <;> rfl
  rw [he] at hr
  cases hr
  exact ⟨rfl, hk⟩

/-- Repayment of a just-acquired reference cannot enter the deletion branch.
No initial liveness premise is supplied: it is carried by `Borrowed`, which
`acquire_spec` derives from the actual successful acquisition. -/
theorem repay_spec (result : Option PeerId) (initial : WGStoreView) :
    ⦃fun w => ⌜Borrowed initial result (wgStoreView w)⌝⦄ peerPut result
    ⦃⇓? _ w => ⌜view w = (outsidePeers initial, resident initial)⌝⦄ := by
  cases result with
  | none =>
    simp only [peerPut]
    mvcgen [branch, invariant, AmbientM.branch, AmbientM.invariant]
    all_goals try dsimp +zetaDelta only at *
    all_goals simp_all [Borrowed, view]
  | some pid =>
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w ambient u v ambient' hb hr
    obtain ⟨d, p, hd, hp, hpos, hk⟩ := hb
    have hs : ⦃fun w => ⌜(wgStoreView w) = { initial with dev := some (
          { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } }) }⌝⦄
        peerPut (some pid)
        ⦃⇓? _ w => ⌜view w = (outsidePeers initial, resident initial)⌝⦄ := by
      have hg := getPeer_known
        { initial with dev := some { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } } }
        { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } }
        pid { p with refcount := p.refcount + 1 } rfl (by simp)
      simp only [peerPut]
      mvcgen [requireNotPending, hg, setPeer,
        modifyDev, refcountDecAndTest, branchCmp, branchCmpExcluded, branch,
        invariant, unsupported, AmbientM.branchCmp, AmbientM.branchCmpExcluded,
        AmbientM.branch, AmbientM.invariant, AmbientM.unsupported]
      all_goals try dsimp +zetaDelta only at *
      all_goals simp_all [view, wgStoreView]
      all_goals subst_vars
      all_goals try simp_all [Std.TreeMap.getElem?_insert]
      all_goals first
        | simpa only [Prod.mk.injEq] using restore_view initial d pid p hd hp
        | omega
    exact (hoare_iff_run_ambient _ _ _).mp hs w ambient u v ambient' hk hr

end Leanux.Proofs.Framing.PeerBorrow
