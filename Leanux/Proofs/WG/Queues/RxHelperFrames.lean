import Leanux.Proofs.WG.Queues.RxQueueView
import Leanux.WG.RxData
import Leanux.Proofs.Framing.Index

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
  mvcgen [getPeer, getDev, invariant, AmbientM.invariant]

theorem keypairGet_rxQueues (kp : Option KeypairId) : SameView rxQueues (keypairGet kp) := by
  apply SameView.of_wp
  intro s
  mvcgen [keypairGet, getKeypair, getDev, setKeypair, modifyDev,
    refcountIncNotZero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]

theorem keypairPut_rxQueues (kp : Option KeypairId) (now : Bool) :
    SameView rxQueues (keypairPut kp now) := by
  apply SameView.of_wp
  intro s
  have hd := fun o => indexOwner_peerDeref_preserves o (fun w => rxQueues w = s)
  unfold Preserves Hoare at hd
  have index_spec (a : IndexM Unit) :
      Hoare (MonadLift.monadLift a : WG.M Unit)
        (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) := by
    apply hoare_liftIndex a (fun w => rxQueues w = s)
    intro w d table hi hw
    unfold rxQueues at hi ⊢
    simpa only [hw, Option.bind_some] using hi
  unfold Hoare at index_spec
  mvcgen [keypairPut, hd, index_spec, getKeypair, getDev, setKeypair, modifyDev,
    refcountDecAndTest, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [Option.bind_some, Option.bind_map, Function.comp_def]
  all_goals subst_vars
  all_goals simp_all

theorem peerGet_rxQueues (pid : PeerId) : SameView rxQueues (peerGet pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGet, requireNotPending, getPeer, getDev, setPeer,
    modifyDev, refcountInc, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *
  all_goals simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]
  all_goals subst s
  all_goals apply rxMap_insert_same <;> first | assumption | rfl

theorem peerGetMaybeZero_rxQueues (pid : Option PeerId) :
    SameView rxQueues (peerGetMaybeZero pid) := by
  apply SameView.of_wp
  intro s
  mvcgen [peerGetMaybeZero, requireNotPending, getPeer, getDev,
    setPeer, modifyDev, refcountIncNotZero, branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *
  all_goals simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]
  all_goals subst s
  all_goals apply rxMap_insert_same <;> first | assumption | rfl

theorem peerPut_rxQueues (pid : Option PeerId) : RetainsRx (peerPut pid) := by
  apply ProjectedAction.of_wp
  intro s
  have index_spec (a : IndexM Unit) :
      Hoare (MonadLift.monadLift a : WG.M Unit)
        (fun w => ResidentsRetained s (rxQueues w))
        (fun _ w => ResidentsRetained s (rxQueues w)) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    unfold rxQueues at hi ⊢
    simpa only [hd, Option.bind_some] using hi
  unfold Hoare at index_spec
  have erase_retains (ds : Option Device) (pid : PeerId) :
      ResidentsRetained (fun i => ds.bind fun d => rxMap d.ifindex d.peers i)
        (fun i => ds.bind fun d => rxMap d.ifindex (d.peers.erase pid) i) := by
    cases ds with
    | none => exact rx_retained_refl _
    | some d => exact rxMap_erase d.ifindex d.peers pid
  mvcgen [peerPut, index_spec, requireNotPending, getPeer, getDev, setPeer,
    modifyDev, refcountDecAndTest, retirePeerUnits, modifyAmbient,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    invariant, unsupported, AmbientM.invariant, AmbientM.unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals try solve | unfold rxQueues at *; simp_all only [Option.bind_map, Function.comp_def]; exact rx_retained_refl _
  all_goals try unfold rxQueues at *; simp_all only [Option.bind_some, Option.bind_map, Function.comp_def]
  all_goals try subst s
  all_goals try simp_all [Option.bind_map, Function.comp_def]
  all_goals try subst_vars
  all_goals first
    | exact rx_retained_refl _
    | exact rxMap_insert_erase _ _ _ _
    | exact rx_retained_trans (by assumption) (erase_retains _ _)
    | (apply rxMap_insert_retained <;> first | assumption | rfl)

theorem counterValidate_rxQueues (kp : KeypairId) (nonce : Nat) :
    SameView rxQueues (counterValidate kp nonce) := by
  apply SameView.of_wp
  intro s
  mvcgen [counterValidate, getKeypair, getDev, setKeypair, modifyDev,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp, WG.orM, invariant, AmbientM.invariant]
  all_goals try exact ((⇓? _ w => ⌜rxQueues w = s⌝) : PostCond _ (.arg WGWorld (.arg Ambient (.except Stop .pure))))
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
  mvcgen [receivedWithKeypair, hg, hk, hp1, hp2, branch, AmbientM.branch, invariant, AmbientM.invariant]

end Leanux.Proofs.WG.Queues
