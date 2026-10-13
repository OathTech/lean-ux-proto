import Leanux.Proofs.WG.Queues.RxQueueView
import Leanux.WG.RxData

set_option maxHeartbeats 1000000
set_option pp.structureInstances false

/-! Successful-endpoint receive-queue frames for complete original helpers.
These are queue facts, not access logs or error-state claims. Peer release may
delete a queue; every remaining entry retains its epoch, identity and contents. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem getPeer_rxQueues (pid : PeerId) : SameView rxQueues (getPeer pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [getPeer, getDev, getK, invariant]

theorem keypairGet_rxQueues (kp : Option KeypairId) : SameView rxQueues (keypairGet kp) := by
  apply SameView.of_wp
  intro s
  mvcgen [keypairGet, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    refcountIncNotZero, branch, branchCmp, invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]

theorem keypairPut_rxQueues (kp : Option KeypairId) (now : Bool) :
    SameView rxQueues (keypairPut kp now) := by
  apply SameView.of_wp
  intro s
  mvcgen [keypairPut, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    refcountDecAndTest, branch, branchCmp, invariant, unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]

theorem freeRxSkb_rxQueues (id : SkbId) : SameView rxQueues (freeRxSkb id) := by
  apply SameView.of_wp
  intro s
  mvcgen [freeRxSkb, getRxSkb, getDev, getK, modifyDev, modifyK, invariant]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]

theorem peerGet_rxQueues (pid : PeerId) : SameView rxQueues (peerGet pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, Peers.getPeer_spec, getDev, getK, setPeer,
    modifyDev, modifyK, refcountInc, branch, branchCmp, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try simp_all only
  all_goals try obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try unfold rxQueues at *; simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]
  subst s
  apply rxMap_insert_same <;> first | assumption | rfl

theorem peerGetMaybeZero_rxQueues (pid : Option PeerId) :
    SameView rxQueues (peerGetMaybeZero pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGetMaybeZero, requireNotPending, Peers.getPeer_spec, getDev, getK,
    setPeer, modifyDev, modifyK, refcountIncNotZero, branch, branchCmp, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try solve | unfold rxQueues at *; simp_all only [Option.bind_map, Function.comp_def]
  all_goals try obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try simp_all only
  all_goals try obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try unfold rxQueues at *; simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]
  all_goals subst s
  all_goals apply rxMap_insert_same <;> first | assumption | rfl

theorem peerPut_rxQueues (pid : Option PeerId) : RetainsRx (peerPut pid) := by
  apply ProjectedAction.of_wp
  intro s
  mvcgen [peerPut, requireNotPending, Peers.getPeer_spec, getDev, getK, setPeer,
    modifyDev, modifyK, refcountDecAndTest, indexRemove, retirePeerUnits,
    branch, branchCmp, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try solve | unfold rxQueues at *; simp_all only [Option.bind_map, Function.comp_def]; exact rx_retained_refl _
  all_goals try obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try simp_all only
  all_goals try obtain ⟨_, _, _, _⟩ := ‹_ ∧ ∃ _, _ ∧ _›
  all_goals try unfold rxQueues at *; simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]
  all_goals try subst s
  all_goals first
    | exact rx_retained_refl _
    | exact rxMap_insert_erase _ _ _ _
    | (apply rxMap_insert_retained <;> first | assumption | rfl)

theorem counterValidate_rxQueues (kp : KeypairId) (nonce : Nat) :
    SameView rxQueues (counterValidate kp nonce) := by
  apply SameView.of_wp
  intro s
  mvcgen [counterValidate, getKeypair, getDev, getK, setKeypair, modifyDev, modifyK,
    branch, branchCmp, WG.orM, invariant]
  all_goals try exact ((⇓? _ w => ⌜rxQueues w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals try unfold rxQueues at *; simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]

  all_goals trivial

theorem receivedWithKeypair_rxQueues (pid : PeerId) (kp : KeypairId) :
    SameView rxQueues (receivedWithKeypair pid kp) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_rxQueues pid).wp (fun t => t = s)
  have hk := fun old => (keypairPut_rxQueues old true).wp (fun t => t = s)
  have hm (f : Peer → Peer) (hs : ∀ p, (f p).internalId = p.internalId)
      (hq : ∀ p, (f p).rxQueue = p.rxQueue) :=
    (modifyPeer_rxQueues pid f hs hq).wp (fun t => t = s)
  have hm1 := hm (fun p => {p with keypairPrevious := p.keypairCurrent}) (fun _ => rfl) (fun _ => rfl)
  have hm2 := hm (fun p => {p with keypairCurrent := some kp, keypairNext := none}) (fun _ => rfl) (fun _ => rfl)
  have hp1 : ⦃fun w => ⌜rxQueues w = s⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairPrevious := p.keypairCurrent})
      ⦃⇓? _ w => ⌜rxQueues w = s⌝⦄ := hm1
  have hp2 : ⦃fun w => ⌜rxQueues w = s⌝⦄
      (pinned_const _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer) pid
        (fun p => {p with keypairCurrent := some kp, keypairNext := none})
      ⦃⇓? _ w => ⌜rxQueues w = s⌝⦄ := hm2
  mvcgen [receivedWithKeypair, hg, hk, hp1, hp2, branch, invariant]

end Leanux.Proofs.WG.Queues
