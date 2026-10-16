import Leanux.Proofs.WG.Queues.RxHelperFrames
import Leanux.Proofs.WG.Peers.Primitives

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Queue-specific primitive contracts. A cached setter must match the
current resident's complete queue and identity, not merely its slot number. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

abbrev RxView := PeerId → Option RxQueueCell

/-- Two native reads return the same peer and retain both the WG and Ambient
endpoints of every continuation, including Stops. -/
theorem getPeer_twice (pid : PeerId) (f : Peer → Peer → WG.M α) :
    (do let p ← getPeer pid; let q ← getPeer pid; f p q) =
      (do let p ← getPeer pid; f p p) := by
  funext w ambient
  change (((getPeer pid >>= fun p => getPeer pid >>= f p).run w).run ambient) =
    (((getPeer pid >>= fun p => f p p).run w).run ambient)
  simp only [StateT.run_bind]
  cases hr : ((getPeer pid).run w).run ambient with
  | error e => simp [hr]
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨rfl, rfl, _⟩ := Peers.getPeer_current pid w v p ambient ambient' hr
    simp [hr, StateT.run_bind]

/-- The original arbitrary product continuation domain is retained at the
actual adapter; it may act on every subsystem. -/
theorem getPeer_twice_product (pid : PeerId) (f : Peer → Peer → Leanux.M α) :
    (do let p ← liftWG (getPeer pid); let q ← liftWG (getPeer pid); f p q) =
      (do let p ← liftWG (getPeer pid); f p p) := by
  funext w
  change ((liftWG (getPeer pid)).run w >>= fun (p, v) =>
    (liftWG (getPeer pid) >>= f p).run v) =
    ((liftWG (getPeer pid)).run w >>= fun (p, v) => (f p p).run v)
  cases hr : ((getPeer pid).run w.wg).run w.ambient with
  | error e => simp [liftWG_run, hr, Except.map, Except.bind]
  | ok out =>
    rcases out with ⟨⟨p, v⟩, ambient'⟩
    obtain ⟨hv, ha, _⟩ := Peers.getPeer_current pid w.wg v p w.ambient ambient' hr
    subst v ambient'
    have hg : (liftWG (getPeer pid)).run w = .ok (p, w) := by
      rw [liftWG_run, hr]
      rfl
    rw [hg]
    change (liftWG (getPeer pid) >>= f p).run w = (f p p).run w
    change ((liftWG (getPeer pid)).run w >>= fun (q, v) => (f p q).run v) = _
    rw [hg]
    rfl

def CurrentRx (s : RxView) (pid : PeerId) (p : Peer) : Prop :=
  ∃ epoch, s pid = some ⟨epoch, p.internalId, p.rxQueue⟩

theorem getPeer_rx_spec (P : RxView → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (rxQueues w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (rxQueues w) ∧ CurrentRx (rxQueues w) pid p⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hp hr
  have hc : Hoare ((getPeer pid).run w) (fun b => w = w ∧ b = ambient)
      (fun out b => out.2 = w ∧ b = ambient ∧
        ∃ d, out.2.dev = some d ∧ d.peers[pid]? = some out.1) :=
    Peers.getPeer_spec pid w ambient w
  obtain ⟨hv, _, d, hd, hl⟩ := (hoare_iff_run _ _ _).mp hc ambient (p, v) ambient' ⟨rfl, rfl⟩ hr
  dsimp only at hv hd hl
  subst v
  exact ⟨hp, d.ifindex, by simp [rxQueues, rxMap, hd, hl]⟩

theorem setPeer_rx_same (pid : PeerId) (p : Peer) (w v : WGWorld) (ambient ambient' : Ambient)
    (hc : CurrentRx (rxQueues w) pid p) (hr : ((setPeer pid p).run w).run ambient = .ok (((), v), ambient')) :
    rxQueues v = rxQueues w := by
  cases hr
  obtain ⟨epoch, hc⟩ := hc
  cases hd : w.dev with
  | none => simp [rxQueues, hd] at hc
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [rxQueues, rxMap, hd, hp] at hc
    | some old =>
      simp only [rxQueues, hd, Option.bind_some, rxMap, hp, Option.map_some,
        Option.some.injEq, RxQueueCell.mk.injEq] at hc
      funext i
      simp only [rxQueues, hd, Option.map_some, Option.bind_some]
      exact congrFun (rxMap_insert_same d.ifindex d.peers pid old p hp hc.2.1.symm hc.2.2.symm) i

theorem setPeer_rx_spec (P : RxView → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (rxQueues w) ∧ CurrentRx (rxQueues w) pid p⌝⦄ setPeer pid p
    ⦃⇓? _ w => ⌜P (rxQueues w)⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hp hr
  cases x
  rw [setPeer_rx_same pid p w v ambient ambient' hp.2 hr]
  exact hp.1

theorem modifyDev_rxQueues (f : Device → Device)
    (he : ∀ d, (f d).ifindex = d.ifindex) (hp : ∀ d, (f d).peers = d.peers) :
    SameView rxQueues (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  funext i
  simp [rxQueues, Option.bind_map, Function.comp_def, he, hp]

theorem RetainsRx.wp {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {view : S → RxView} {a : StateT S m α}
    (h : ProjectedAction view ResidentsRetained a) (s : RxView) :
    ⦃fun w => ⌜ResidentsRetained s (view w)⌝⦄ a
    ⦃⇓? _ w => ⌜ResidentsRetained s (view w)⌝⦄ :=
  ProjectedAction.wp h (ResidentsRetained s) (fun _ _ hr hs => rx_retained_trans hs hr)

theorem RetainsRx.of_same {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {view : S → RxView} {a : StateT S m α}
    (h : SameView view a) : ProjectedAction view ResidentsRetained a := by
  intro initial
  exact hoare_consequence (h initial) (fun _ he => he)
    (fun _ _ he => he ▸ rx_retained_refl _)

theorem requireNotPending_rxQueues (pid : PeerId) (why : String) :
    SameView rxQueues (requireNotPending pid why) := by
  apply SameView.of_wp
  intro s
  mvcgen [requireNotPending]

theorem getKeypair_rxQueues (kp : KeypairId) : SameView rxQueues (getKeypair kp) := by
  apply SameView.of_wp
  intro s
  mvcgen [getKeypair, getDev, invariant, AmbientM.invariant]

theorem setKeypair_rxQueues (kp : KeypairId) (k : Keypair) : SameView rxQueues (setKeypair kp k) :=
  modifyDev_rxQueues _ (fun _ => rfl) (fun _ => rfl)

end Leanux.Proofs.WG.Queues
