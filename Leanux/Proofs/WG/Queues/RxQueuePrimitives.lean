import Leanux.Proofs.WG.Queues.RxHelperFrames
import Leanux.Proofs.WG.Lifetimes.ReceiveCompletion

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Queue-specific primitive contracts. A cached setter must match the
current resident's complete queue and identity, not merely its slot number. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

abbrev RxView := PeerId → Option RxQueueCell

/-- Two consecutive original reads return the same peer and preserve every
result, World and Stop of their continuation. -/
theorem getPeer_twice (pid : PeerId) (f : Peer → Peer → M α) :
    (do let p ← getPeer pid; let q ← getPeer pid; f p q) =
      (do let p ← getPeer pid; f p p) := by
  funext w
  change ((getPeer pid >>= fun p => getPeer pid >>= f p).run w) =
    ((getPeer pid >>= fun p => f p p).run w)
  simp only [StateT.run_bind]
  cases hr : (getPeer pid).run w with
  | error e => simp [hr]
  | ok out =>
    rcases out with ⟨p, v⟩
    have hv := (hoare_iff_triple _ _ _).mpr (Peers.getPeer_spec pid w) w p v rfl hr
    rcases hv with ⟨rfl, _⟩
    simp [hr, StateT.run_bind]

def CurrentRx (s : RxView) (pid : PeerId) (p : Peer) : Prop :=
  ∃ epoch, s pid = some ⟨epoch, p.internalId, p.rxQueue⟩

theorem getPeer_rx_spec (P : RxView → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (rxQueues w)⌝⦄ getPeer pid
    ⦃⇓? p w => ⌜P (rxQueues w) ∧ CurrentRx (rxQueues w) pid p⌝⦄ := by
  apply (hoare_iff_triple _ _ _).mp
  intro w p v hp hr
  have hc := (hoare_iff_triple _ _ _).mpr (Peers.getPeer_spec pid w) w p v rfl hr
  obtain ⟨rfl, d, hd, hl⟩ := hc
  exact ⟨hp, d.ifindex, by simp [rxQueues, rxMap, hd, hl]⟩

theorem setPeer_rx_same (pid : PeerId) (p : Peer) (w v : World)
    (hc : CurrentRx (rxQueues w) pid p) (hr : (setPeer pid p).run w = .ok ((), v)) :
    rxQueues v = rxQueues w := by
  cases hr
  obtain ⟨epoch, hc⟩ := hc
  cases hd : w.k.wg with
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
  apply (hoare_iff_triple _ _ _).mp
  intro w x v hp hr
  cases x
  rw [setPeer_rx_same pid p w v hp.2 hr]
  exact hp.1

theorem modifyDev_rxQueues (f : Device → Device)
    (he : ∀ d, (f d).ifindex = d.ifindex) (hp : ∀ d, (f d).peers = d.peers) :
    SameView rxQueues (modifyDev f) := by
  intro w x v hr
  cases hr
  funext i
  simp [rxQueues, Option.bind_map, Function.comp_def, he, hp]

theorem RetainsRx.wp (h : RetainsRx a) (s : RxView) :
    ⦃fun w => ⌜ResidentsRetained s (rxQueues w)⌝⦄ a
    ⦃⇓? _ w => ⌜ResidentsRetained s (rxQueues w)⌝⦄ :=
  ProjectedAction.wp h (ResidentsRetained s) (fun _ _ hr hs => rx_retained_trans hs hr)

theorem RetainsRx.of_same (h : SameView rxQueues a) : RetainsRx a := by
  intro w x v hr
  rw [h w x v hr]
  exact rx_retained_refl _

theorem requireNotPending_rxQueues (pid : PeerId) (why : String) :
    SameView rxQueues (requireNotPending pid why) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_rxQueues pid).wp (fun t => t = s)
  mvcgen [requireNotPending, hg, unsupported]

theorem getKeypair_rxQueues (kp : KeypairId) : SameView rxQueues (getKeypair kp) := by
  apply SameView.of_wp
  intro s
  mvcgen [getKeypair, getDev, getK, invariant]

theorem setKeypair_rxQueues (kp : KeypairId) (k : Keypair) : SameView rxQueues (setKeypair kp k) :=
  modifyDev_rxQueues _ (fun _ => rfl) (fun _ => rfl)

theorem getTxSkb_rxQueues (id : SkbId) : SameView rxQueues (getTxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [getTxSkb, getDev, getK, invariant]

theorem setTxSkb_rxQueues (id : SkbId) (f : DataPacket → DataPacket) :
    SameView rxQueues (setTxSkb id f) := by
  apply SameView.of_wp
  intro s
  have hg := (getTxSkb_rxQueues id).wp (fun t => t = s)
  have hm := fun p => (modifyDev_rxQueues (fun d => {d with txSkbs := d.txSkbs.insert id (f p)})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [setTxSkb, hg, hm]

theorem newTxSkb_rxQueues (p : DataPacket) : SameView rxQueues (newTxSkb p) := by
  apply SameView.of_wp
  intro s
  mvcgen [newTxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all

theorem freeTxSkb_rxQueues (id : SkbId) : SameView rxQueues (freeTxSkb id) := by
  apply SameView.of_wp
  intro s
  have hg := (getTxSkb_rxQueues id).wp (fun t => t = s)
  have hm := (modifyDev_rxQueues (fun d => {d with txSkbs := d.txSkbs.erase id})
    (fun _ => rfl) (fun _ => rfl)).wp (fun t => t = s)
  mvcgen [freeTxSkb, hg, hm]

end Leanux.Proofs.WG.Queues
