import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueCallbacks
import Leanux.Proofs.WG.Queues.RxRingNapi

/-! Native NAPI and GRO retain the physical handshake ring, including actual
stack callbacks. Readiness and packet ownership are not premises. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Std.Do

theorem groNormalList_cell (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView productView (cb xs)) (g : GroState) : SameView productView (groNormalList cb g) := by
  unfold groNormalList
  split
  · exact SameView.pure _ _
  · exact (hc _).bind (fun _ => SameView.pure _ _)

theorem groNormalOne_cell (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView productView (cb xs)) (g : GroState) (pkt : List UInt8) (segs : Nat) :
    SameView productView (groNormalOne cb g pkt segs) := by
  unfold groNormalOne
  dsimp only
  split
  · exact groNormalList_cell cb hc _
  · exact SameView.pure _ _

/-- Product poll composition retains arbitrary stack callbacks. Native work
is framed only through the actual WireGuard adapter. -/
macro "handshake_poll_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]"
    "with" "[" natives:ident,* "]" : tactic => do
  let expand ← if fs.getElems.isEmpty then `(tactic| skip) else `(tactic| unfold $fs:ident*)
  let mut use ← `(tactic| fail "no named product ring frame")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | env_operation_fact $fact | ($use:tactic))
  `(tactic|
    (have ambient {α : Type} (a : AmbientM α) : SameView productView (monadLift a : Leanux.M α) :=
       fun initial => productAmbient_spec a (fun w => productView w = initial) (fun _ _ h => h)
     have native {α : Type} (a : WG.M α) (ha : SameView view a) :
         SameView productView (liftWG a) := sameView_liftWG productView view a ha (fun _ _ _ h => h)
     have choice {α : Type} (p : Prop) [Decidable p] (yes no : Leanux.M α)
         (hy : p → SameView productView yes) (hn : ¬p → SameView productView no) :
         SameView productView (if p then yes else no) := by
       by_cases h : p
       · simpa only [ite_eq_left h] using hy h
       · simpa only [ite_eq_right h] using hn h
     have loop {α β : Type} (xs : List α) (b : β) (f : α → β → Leanux.M (ForInStep β))
         (hf : ∀ x b, SameView productView (f x b)) : SameView productView (forIn xs b f) :=
       fun initial => list_view_spec productView (fun s => s = initial) xs b f (fun x b => hf x b initial)
     have ignored {α : Type} (a : Leanux.M α) (ha : SameView productView a) : SameView productView (Functor.discard a) :=
       fun initial => discard_view_spec productView (fun s => s = initial) a (ha initial)
     $expand
     repeat' first
       | ($use:tactic)
       | (snapshot_head MonadLiftT.monadLift; first
           | (ring_lift_source AmbientM; exact ambient _)
           | (ring_lift_source WG.M; apply native; simp only [monadLift_self]; handshake_cell_source [] using [$natives,*]))
       | (snapshot_head MonadLift.monadLift; first
           | (ring_lift_source AmbientM; exact ambient _)
           | (ring_lift_source WG.M; apply native; simp only [monadLift_self]; handshake_cell_source [] using [$natives,*]))
       | (snapshot_head liftWG; apply native; handshake_cell_source [] using [$natives,*])
       | (snapshot_head ForIn.forIn; first | apply loop | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
       | (snapshot_head Functor.discard; apply ignored)
       | (snapshot_head ite; apply choice)
       | (snapshot_head branch; unfold branch)
       | (snapshot_head invariant; unfold invariant)
       | (snapshot_head unsupported; unfold unsupported)
       | (snapshot_head getAmbient; unfold getAmbient)
       | (snapshot_head hidden; unfold hidden)
       | (snapshot_head peekHiddenSite; unfold peekHiddenSite)
       | (snapshot_head modifyAmbient; unfold modifyAmbient)
       | env_operation_step))

theorem napiGroReceive_cell (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView productView (cb xs)) (g : GroState) (pkt : List UInt8) :
    SameView productView (napiGroReceive cb g pkt) := by
  have normal := fun g pkt segs => groNormalOne_cell cb hc g pkt segs
  handshake_poll_source [napiGroReceive] using [normal] with []

theorem napiGroFlushAll_cell (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView productView (cb xs)) (g : GroState) :
    SameView productView (napiGroFlushAll cb g) := by
  have normal := fun g pkt segs => groNormalOne_cell cb hc g pkt segs
  have flush := fun g => groNormalList_cell cb hc g
  handshake_poll_source [napiGroFlushAll] using [normal, flush] with []

theorem rxPoll_cell (pid : PeerId) (budget : Nat) (cb : List (List UInt8) → Leanux.M Unit)
    (hc : ∀ xs, SameView productView (cb xs)) : SameView productView (rxPoll pid budget cb) := by
  have peek := fun (q : PrevQueue SkbId) => kernel (prevQueuePeek_sameWGStore q)
  have endpoint := fun src => kernel (endpointFromSkb_sameWGStore src)
  have gro := fun g pkt => napiGroReceive_cell cb hc g pkt
  have flush := fun g => napiGroFlushAll_cell cb hc g
  handshake_poll_source [rxPoll] using [gro, flush]
    with [peek, endpoint, counterValidate_cell, consumeDataDone_cell, keypairPut_frame, peerPut_frame]

theorem napiSoftirq_cell : SameView productView Leanux.Env.napiSoftirq := by
  have poll := fun pid => rxPoll_cell pid NAPI_POLL_WEIGHT _ stackForM_cell
  have worker (body : Leanux.M Unit) (hb : SameView productView body) :
      SameView productView (Leanux.Env.runWorker .netRx body) := by
    handshake_poll_source [Leanux.Env.runWorker] using [hb] with []
  handshake_poll_source [Leanux.Env.napiSoftirq] using [poll, worker] with []

theorem napiIrqExit_cell : SameView productView Leanux.Env.napiIrqExit := by
  rw [← napiIrqExitSource_eq]
  have choose : SameView productView chooseNapiHere := by
    apply (ProjectedAction.iff_run _ _ _).mpr
    intro w x v hr
    cases hr
    rfl
  handshake_poll_source [napiIrqExitSource] using [choose, napiSoftirq_cell] with []

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
