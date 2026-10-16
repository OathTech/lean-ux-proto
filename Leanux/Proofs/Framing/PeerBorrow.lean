import Leanux.Proofs.Framing.Projection
import Leanux.Proofs.WG.Keypairs.Frames.WGBase
import Leanux.WG.Peer

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Balanced original peer reference acquisition and repayment. The endpoint
view retains the complete Kernel outside the peer map and every complete peer
record pointwise. It deliberately does not assert equality of TreeMap shapes.
These are normal-return contracts; a Stop has no returned World. -/
namespace Leanux.Proofs.Framing.PeerBorrow
open Leanux Leanux.WG Leanux.Proofs.Framing Std.Do

def outsidePeers (k : Kernel) : Kernel :=
  { k with wg := k.wg.map fun d => { d with peers := {} } }

def resident (k : Kernel) (pid : PeerId) : Option Peer :=
  k.wg.bind fun d => d.peers[pid]?

def view (w : World) : Kernel × (PeerId → Option Peer) :=
  (outsidePeers w.k, resident w.k)

/-- A successful acquisition changes only the selected resident peer's
reference count. Positivity is a conclusion of the original call. -/
def Borrowed (initial : Kernel) (result : Option PeerId) (current : Kernel) : Prop :=
  match result with
  | none => current = initial
  | some pid => ∃ d p, initial.wg = some d ∧ d.peers[pid]? = some p ∧
      0 < p.refcount ∧ current = { initial with wg := some (
        { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } }) }

theorem refcountIncNotZero_spec (old : Nat) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ refcountIncNotZero old
    ⦃⇓? live w => ⌜w.k = initial ∧ live = (old != 0)⌝⦄ := by
  mvcgen [refcountIncNotZero, branchCmp, branchCmpExcluded, branch, unsupported]

theorem refcountDecAndTest_spec (old : Nat) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ refcountDecAndTest old
    ⦃⇓? released w => ⌜w.k = initial ∧ 0 < old ∧ released = (old == 1)⌝⦄ := by
  mvcgen [refcountDecAndTest, branchCmp, branchCmpExcluded, branch, unsupported]
  all_goals simp_all
  all_goals omega

theorem acquire_spec (peer : Option PeerId) (initial : Kernel) :
    ⦃fun w => ⌜w.k = initial⌝⦄ peerGetMaybeZero peer
    ⦃⇓? result w => ⌜(result = none ∨ result = peer) ∧ Borrowed initial result w.k⌝⦄ := by
  mvcgen [peerGetMaybeZero, requireNotPending, getPeer, getDev, getK, setPeer,
    modifyDev, modifyK, refcountIncNotZero, branchCmp, branchCmpExcluded, branch,
    invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals simp_all [Borrowed]
  all_goals first
    | (refine ⟨_, _, ?_, ?_, ?_, ?_⟩ <;> first | assumption | rfl | omega)
    | omega

theorem restore_view (initial : Kernel) (d : Device) (pid : PeerId) (p : Peer)
    (hd : initial.wg = some d) (hp : d.peers[pid]? = some p) :
    (outsidePeers { initial with wg := some { d with peers :=
        (d.peers.insert pid { p with refcount := p.refcount + 1 }).insert pid p } },
      resident { initial with wg := some { d with peers :=
        (d.peers.insert pid { p with refcount := p.refcount + 1 }).insert pid p } }) =
      (outsidePeers initial, resident initial) := by
  apply Prod.ext
  · simp [outsidePeers, hd]
  · funext j
    simp only [resident, hd, Option.bind_some, Std.TreeMap.getElem?_insert,
      Std.LawfulEqOrd.compare_eq_iff_eq]
    by_cases h : pid = j <;> simp_all

theorem getPeer_known (initial : Kernel) (d : Device) (pid : PeerId) (p : Peer)
    (hd : initial.wg = some d) (hp : d.peers[pid]? = some p) :
    ⦃fun w => ⌜w.k = initial⌝⦄ getPeer pid
    ⦃⇓? result w => ⌜result = p ∧ w.k = initial⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w result v hk hr
  have he : (getPeer pid).run w = .ok (p, w) := by
    simp [getPeer, getDev, getK, hk, hd, hp]
  rw [he] at hr
  cases hr
  exact ⟨rfl, hk⟩

/-- Repayment of a just-acquired reference cannot enter the deletion branch.
No initial liveness premise is supplied: it is carried by `Borrowed`, which
`acquire_spec` derives from the actual successful acquisition. -/
theorem repay_spec (result : Option PeerId) (initial : Kernel) :
    ⦃fun w => ⌜Borrowed initial result w.k⌝⦄ peerPut result
    ⦃⇓? _ w => ⌜view w = (outsidePeers initial, resident initial)⌝⦄ := by
  cases result with
  | none =>
    simp only [peerPut]
    mvcgen [branch, invariant]
    all_goals dsimp +zetaDelta only at *
    all_goals simp_all [Borrowed, view]
  | some pid =>
    apply (hoare_iff_triple _ _ _).mp
    intro w u v hb hr
    obtain ⟨d, p, hd, hp, hpos, hk⟩ := hb
    have hs : ⦃fun w => ⌜w.k = { initial with wg := some (
          { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } }) }⌝⦄
        peerPut (some pid)
        ⦃⇓? _ w => ⌜view w = (outsidePeers initial, resident initial)⌝⦄ := by
      have hg := getPeer_known
        { initial with wg := some { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } } }
        { d with peers := d.peers.insert pid { p with refcount := p.refcount + 1 } }
        pid { p with refcount := p.refcount + 1 } rfl (by simp)
      simp only [peerPut]
      mvcgen [requireNotPending, hg, setPeer,
        modifyDev, modifyK, refcountDecAndTest, branchCmp, branchCmpExcluded, branch,
        invariant, unsupported]
      all_goals dsimp +zetaDelta only at *
      all_goals simp_all [view]
      all_goals subst_vars
      all_goals try simp_all [Std.TreeMap.getElem?_insert]
      all_goals first
        | simpa only [Prod.mk.injEq] using restore_view initial d pid p hd hp
        | omega
    exact (hoare_iff_triple _ _ _).mpr hs w u v hk hr

end Leanux.Proofs.Framing.PeerBorrow
