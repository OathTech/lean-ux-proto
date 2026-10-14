import Leanux.Proofs.WG.Queues.RxRingCallbackFrames

/-! Concrete NAPI and GRO preserve the complete physical decrypt-ring cell.
Stack callbacks may enqueue TX or delete peers. This is a ring frame only;
source inspection establishes that these helpers contain no decrypt-ring cut. -/
set_option maxHeartbeats 2000000
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Queues.RxRing
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

theorem groNormalList_cell (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, SameView cell (cb xs)) (g : GroState) : SameView cell (groNormalList cb g) := by
  unfold groNormalList
  split
  · exact SameView.pure _ _
  · exact (hc _).bind (fun _ => SameView.pure _ _)

theorem groNormalOne_cell (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, SameView cell (cb xs)) (g : GroState) (pkt : List UInt8) (segs : Nat) :
    SameView cell (groNormalOne cb g pkt segs) := by
  unfold groNormalOne
  dsimp only
  split
  · exact groNormalList_cell cb hc _
  · exact SameView.pure _ _

theorem napiGroReceive_cell (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, SameView cell (cb xs)) (g : GroState) (pkt : List UInt8) :
    SameView cell (napiGroReceive cb g pkt) := by
  apply SameView.of_wp
  intro s
  have hn := fun g pkt segs => (groNormalOne_cell cb hc g pkt segs).wp (fun t => t = s)
  mvcgen [napiGroReceive, hn, unsupported]

theorem napiGroFlushAll_cell (cb : List (List UInt8) → M Unit)
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

theorem rxPoll_cell (pid : PeerId) (budget : Nat) (cb : List (List UInt8) → M Unit)
    (hc : ∀ xs, SameView cell (cb xs)) : SameView cell (rxPoll pid budget cb) := by
  apply SameView.of_wp
  intro s
  have hp := (getPeer_frame pid).wp (fun t => t = s)
  have hs := fun p => (setPeer_frame pid p).wp (fun t => t = s)
  have hr := fun id => (getRx_frame id).wp (fun t => t = s)
  have hpeek := fun (q : PrevQueue SkbId) => (kernel (prevQueuePeek_sameKernel q)).wp (fun t => t = s)
  have hctr := fun key nonce => (counterValidate_cell key nonce).wp (fun t => t = s)
  have he := fun src => (kernel (endpointFromSkb_sameKernel src)).wp (fun t => t = s)
  have hd := fun pkt ep => (consumeDataDone_cell pid pkt ep).wp (fun t => t = s)
  have hg := fun g pkt => (napiGroReceive_cell cb hc g pkt).wp (fun t => t = s)
  have hf := fun g => (napiGroFlushAll_cell cb hc g).wp (fun t => t = s)
  have hk := fun kp => (keypairPut_frame kp false).wp (fun t => t = s)
  have hu := (peerPut_frame (some pid)).wp (fun t => t = s)
  have hx := fun id => (freeRx_frame id).wp (fun t => t = s)
  have hl (α β : Type) := list_view_spec cell (α := α) (β := β) (fun t => t = s)
  simp only [rxPoll, Std.Legacy.Range.forIn_eq_forIn_range']
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl,
    hp, hs, hr, hpeek, hctr, he, hd, hg, hf, hk, hu, hx, WG.andM, branch, invariant, unsupported]
  all_goals try exact ((⇓? _ w => ⌜cell w = s⌝) : PostCond _ (.arg World (.except Stop .pure)))
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

theorem napiSoftirq_cell : SameView cell Leanux.Env.napiSoftirq := by
  apply SameView.of_wp
  intro s
  have hp := fun pid => (rxPoll_cell pid NAPI_POLL_WEIGHT _ stackForM_cell).wp (fun t => t = s)
  have hh := (kernel peekHiddenSite_sameKernel).wp (fun t => t = s)
  have hw (body : M Unit) (hb : ⦃fun w => ⌜cell w = s⌝⦄ body ⦃⇓? _ w => ⌜cell w = s⌝⦄) :
      ⦃fun w => ⌜cell w = s⌝⦄ Leanux.Env.runWorker .netRx body ⦃⇓? _ w => ⌜cell w = s⌝⦄ := by
    have hr := fun site => (kernel (hidden_sameKernel site)).wp (fun t => t = s)
    mvcgen [Leanux.Env.runWorker, hr, hb]
  have hl (α β : Type) := list_view_spec cell (α := α) (β := β) (fun t => t = s)
  have hd (α : Type) := discard_view_spec cell (α := α) (fun t => t = s)
  mvcgen [-Std.Do.Spec.forIn_list, -Std.Do.Spec.forIn'_list, hl, Leanux.Env.napiSoftirq,
    hp, hh, hw, hd, getDev, getK, invariant, unsupported]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [cell]

theorem napiIrqExit_cell : SameView cell Leanux.Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  apply SameView.of_wp
  intro s
  have hn := napiSoftirq_cell.wp (fun t => t = s)
  have hh := (kernel peekHiddenSite_sameKernel).wp (fun t => t = s)
  have hc := (kernel chooseNapiHere_sameKernel).wp (fun t => t = s)
  mvcgen [napiIrqExitSource, hn, hh, hc, getDev, getK, invariant]

end Leanux.Proofs.WG.Queues.RxRing
