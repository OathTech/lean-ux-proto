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
  apply (hoare_iff_run _ _ _).mpr
  intro ambient live ambient' _ run
  by_cases zero : old = 0 <;> by_cases overflow : old + 1 ≥ 2 ^ 31 <;>
    simp [StateT.run_bind, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
      Leanux.Proofs.WG.CounterWindow.except_pure, refcountIncNotZero, branch, branchCmp,
      AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported, zero,
      overflow] at run
  all_goals rcases run with ⟨rfl, rfl⟩ <;> simp [zero]

theorem refcountDecAndTest_spec (old : Nat) :
    ⦃fun (_ : Ambient) => ⌜True⌝⦄ (refcountDecAndTest old : AmbientM Bool)
    ⦃⇓? released _ => ⌜0 < old ∧ released = (old == 1)⌝⦄ := by
  apply (hoare_iff_run _ _ _).mpr
  intro ambient released ambient' _ run
  cases old with
  | zero =>
    simp [StateT.run_bind, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
      Leanux.Proofs.WG.CounterWindow.except_pure, refcountDecAndTest, branch, branchCmp,
      AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported] at run
    cases run
  | succ old =>
    cases old with
    | zero =>
      simp [StateT.run_bind, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
        Leanux.Proofs.WG.CounterWindow.except_pure, refcountDecAndTest, branch, branchCmp,
        AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨by omega, rfl⟩
    | succ n =>
      simp [StateT.run_bind, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
        Leanux.Proofs.WG.CounterWindow.except_pure, refcountDecAndTest, branch, branchCmp,
        AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨by omega, rfl⟩

theorem acquire_spec (peer : Option PeerId) (initial : WGStoreView) :
    ⦃fun w => ⌜(wgStoreView w) = initial⌝⦄ peerGetMaybeZero peer
    ⦃⇓? result w => ⌜(result = none ∨ result = peer) ∧ Borrowed initial result (wgStoreView w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' initialView run
  cases peer with
  | none =>
    simp [StateT.run_monadLift, Leanux.Proofs.WG.CounterWindow.except_pure, peerGetMaybeZero,
      branch, AmbientM.branch] at run
    rcases run with ⟨rfl, rfl, rfl⟩
    exact ⟨Or.inl rfl, initialView⟩
  | some pid =>
    cases hd : w.dev with
    | none =>
      simp [StateT.run_bind, StateT.run_monadLift, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
        Leanux.Proofs.WG.CounterWindow.except_pure, peerGetMaybeZero, branch, AmbientM.branch,
        requireNotPending, getPeer, getDev, hd, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases hp : d.peers[pid]? with
      | none =>
        simp [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
          Leanux.Proofs.WG.CounterWindow.except_ok_bind,
          Leanux.Proofs.WG.CounterWindow.except_pure, peerGetMaybeZero, branch, AmbientM.branch,
          requireNotPending, getPeer, getDev, hd, hp, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        by_cases zero : p.refcount = 0 <;>
          by_cases overflow : 2147483647 ≤ p.refcount <;>
          simp [StateT.run_bind, StateT.run_pure, StateT.run_monadLift,
            Leanux.Proofs.WG.CounterWindow.except_ok_bind,
            Leanux.Proofs.WG.CounterWindow.except_pure, peerGetMaybeZero, requireNotPending,
            getPeer, getDev, setPeer, modifyDev, hd, hp, refcountIncNotZero, branch, branchCmp,
            AmbientM.branch, AmbientM.branchCmp, unsupported, AmbientM.unsupported, zero,
            overflow] at run
        all_goals try (change Except.error _ = Except.ok _ at run; cases run)
        all_goals rcases run with ⟨rfl, rfl, rfl⟩
        all_goals first
          | exact ⟨Or.inl rfl, initialView⟩
          | (refine ⟨Or.inr rfl, d, p, ?_, hp, by omega, ?_⟩
             · exact (congrArg WGStoreView.dev initialView).symm.trans hd
             · subst initial
               simp [wgStoreView, hd])

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
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' borrowed run
  cases result with
  | none =>
    simp [peerPut, branch, AmbientM.branch, StateT.run_monadLift] at run
    rcases run with ⟨rfl, rfl⟩
    exact congrArg (fun k => (outsidePeers k, resident k)) borrowed
  | some pid =>
    obtain ⟨d, p, hd, hp, positive, hk⟩ := borrowed
    have hw : w.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
      congrArg WGStoreView.dev hk
    have nonzero : p.refcount ≠ 0 := by omega
    simp [peerPut, requireNotPending, getPeer, getDev, setPeer, modifyDev, hw, refcountDecAndTest,
      branch, branchCmp, Leanux.Proofs.WG.CounterWindow.branch_run,
      Leanux.Proofs.WG.CounterWindow.branchCmp_run, StateT.run_bind, StateT.run_pure,
      StateT.run_monadLift, Leanux.Proofs.WG.CounterWindow.except_ok_bind,
      Leanux.Proofs.WG.CounterWindow.except_pure, nonzero] at run
    rcases run with ⟨rfl, rfl⟩
    have updated := congrArg (fun k : WGStoreView => {k with dev := k.dev.map fun (d : Device) =>
      {d with peers := d.peers.insert pid p}}) hk
    have observed := congrArg (fun k : WGStoreView => (outsidePeers k, resident k)) updated
    apply Eq.trans ?_ (restore_view initial d pid p hd hp)
    simpa [view, wgStoreView, hw] using observed

end Leanux.Proofs.Framing.PeerBorrow
