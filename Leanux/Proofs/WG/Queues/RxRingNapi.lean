import Leanux.Proofs.WG.Queues.RxRingCallbackFrames
import Leanux.Proofs.WG.Lifetimes.BatchNapi

/-! Concrete NAPI and GRO preserve the complete physical decrypt-ring cell.
Stack callbacks may enqueue TX or delete peers. This is a ring frame only;
source inspection establishes that these helpers contain no decrypt-ring cut. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem groNormalList_cell (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView cell (cb xs)) (g : GroState) : SameView cell (groNormalList cb g) := by
  unfold groNormalList
  split
  · exact SameView.pure _ _
  · exact (hc _).bind (fun _ => SameView.pure _ _)

theorem groNormalOne_cell (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView cell (cb xs)) (g : GroState) (pkt : List UInt8) (segs : Nat) :
    SameView cell (groNormalOne cb g pkt segs) := by
  unfold groNormalOne
  dsimp only
  split
  · exact groNormalList_cell cb hc _
  · exact SameView.pure _ _

theorem napiGroReceive_cell (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView cell (cb xs)) (g : GroState) (pkt : List UInt8) :
    SameView cell (napiGroReceive cb g pkt) := by
  apply SameView.of_wp
  intro s
  have hn := fun g pkt segs => (groNormalOne_cell cb hc g pkt segs).wp (fun t => t = s)
  mvcgen [napiGroReceive, hn, unsupported, AmbientM.unsupported]

theorem napiGroFlushAll_cell (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView cell (cb xs)) (g : GroState) :
    SameView cell (napiGroFlushAll cb g) := by
  apply SameView.of_wp
  intro s
  have hn := fun g pkt segs => (groNormalOne_cell cb hc g pkt segs).wp (fun t => t = s)
  have hl := fun g => (groNormalList_cell cb hc g).wp (fun t => t = s)
  mvcgen [napiGroFlushAll, hn, hl]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem rxPoll_cell (pid : PeerId) (budget : Nat) (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView cell (cb xs)) : SameView cell (rxPoll pid budget cb) := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have native {α : Type} (a : WG.M α) (ha : SameView nativeCell a) :
      Hoare (liftWG a)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    (sameView_liftWG cell nativeCell a ha (fun _ _ _ h => h)).wp P
  have packets {α : Type} (a : SkbM α) : SameView nativeCell (liftSkb a) := by
    intro initial
    apply hoare_liftSkb
    intro g d store hg hd
    simpa [nativeCell, hd] using hg
  have skb {α : Type} (a : SkbM α) := native (liftSkb a) (packets a)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have hp := native (getPeer pid) (getPeer_frame pid)
  have hs := fun p => native (setPeer pid p) (setPeer_frame pid p)
  have hpeek := fun (q : PrevQueue SkbId) =>
    native q.peek (kernel (prevQueuePeek_sameWGStore q))
  have hctr := fun key nonce => native (counterValidate key nonce) (counterValidate_cell key nonce)
  have he := fun src => native (endpointFromSkb src) (kernel (endpointFromSkb_sameWGStore src))
  have hd := fun pkt ep => native (consumeDataDone pid pkt ep) (consumeDataDone_cell pid pkt ep)
  have hg := fun g pkt => (napiGroReceive_cell cb hc g pkt).wp P
  have hf := fun g => (napiGroFlushAll_cell cb hc g).wp P
  have hk := fun kp => native (keypairPut kp false) (keypairPut_frame kp false)
  have hu := native (peerPut (some pid)) (peerPut_frame (some pid))
  have hgo (a b : WG.M Bool) (ha : SameView nativeCell (WG.andM a b)) :
      Hoare (liftWG (WG.andM a b)) (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    native _ ha
  have hl (α β : Type) := list_view_spec (m := Except Stop) cell (α := α) (β := β) P
  unfold Hoare at skb ambient hp hs hpeek hctr he hd hk hu hgo
  have lift {α : Type} (a : WG.M α) : (liftM a : Leanux.M α) = liftWG a := rfl
  simp only [rxPoll, Std.Legacy.Range.forIn_eq_forIn_range', lift]
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT,
    hgo, hl, hp, hs, skb, ambient, hpeek, hctr, he, hd, hg, hf, hk, hu,
    getRxSkb, freeRxSkb, branch, invariant, unsupported, liftM]
  all_goals try exact ((⇓? _ w => ⌜P (cell w)⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try
    apply SameView.of_wp
    intro initial
    have hs := fun (a : SkbM RxPacket) => (packets a).wp (fun v => v = initial)
    mvcgen [WG.andM, getRxSkb, hs, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals first | assumption | rfl


theorem napiSoftirq_cell : SameView cell Leanux.Env.napiSoftirq := by
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hp := fun pid => (rxPoll_cell pid NAPI_POLL_WEIGHT _ stackForM_cell).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev : SameView nativeCell getDev := by
    apply SameView.of_wp
    intro initial
    mvcgen [getDev, invariant, AmbientM.invariant]
  have hg := (sameView_liftWG cell nativeCell getDev dev (fun _ _ _ h => h)).wp P
  unfold Hoare at ambient
  have hw (body : Leanux.M Unit)
      (hb : ⦃fun w => ⌜P (cell w)⌝⦄ body ⦃⇓? _ w => ⌜P (cell w)⌝⦄) :
      ⦃fun w => ⌜P (cell w)⌝⦄ Leanux.Env.runWorker .netRx body
      ⦃⇓? _ w => ⌜P (cell w)⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, Leanux.Env.runWorker, hidden, modifyAmbient, ambient, hb]
  have hl (α β : Type) := list_view_spec (m := Except Stop) cell (α := α) (β := β) P
  have hd (α : Type) := discard_view_spec (m := Except Stop) cell (α := α) P
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, -Std.Do.Spec.monadLift_StateT,
    hl, Leanux.Env.napiSoftirq, hp, ambient, hw, hd, hg, getAmbient, peekHiddenSite, invariant, unsupported]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals simp_all [cell]

theorem napiIrqExit_cell : SameView cell Leanux.Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  apply SameView.of_wp
  intro s
  let P := fun t => t = s
  have hn := napiSoftirq_cell.wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : Leanux.M α)
        (fun w => P (cell w)) (fun _ w => P (cell w)) :=
    productAmbient_spec a _ (fun _ _ h => h)
  have dev : SameView nativeCell getDev := by
    apply SameView.of_wp
    intro initial
    mvcgen [getDev, invariant, AmbientM.invariant]
  have hg := (sameView_liftWG cell nativeCell getDev dev (fun _ _ _ h => h)).wp P
  have hc : ⦃fun w => ⌜P (cell w)⌝⦄ chooseNapiHere ⦃⇓? _ w => ⌜P (cell w)⌝⦄ := by
    mvcgen [chooseNapiHere, getEnv, modifyEnv]
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, napiIrqExitSource,
    hn, ambient, hc, hg, getAmbient, peekHiddenSite, invariant]

end Leanux.Proofs.WG.Queues.RxRing
