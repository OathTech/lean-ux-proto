import Leanux.Proofs.WG.RetirementSecurity.HandshakeRingValidity
import Leanux.Proofs.WG.Queues.RxRingFrames

/-! Exact native handshake-ring frames. Mutations to peer/keypair/index and
packet storage are independent of this queue; consumed and produced ring cells
are handled separately by physical validity, not hidden behind these frames. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues.RxRing Std.Do
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.WGFrames

theorem kernel {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (ha : SameView (fun w => wgStoreView (project w)) a) :
    SameView (fun w => view (project w)) a :=
  ha.of_factor (fun store : WGStoreView => store.dev.map (·.handshakeQueue))
    (fun w => view (project w)) (fun _ => rfl)

theorem modify (f : Device → Device)
    (hq : ∀ d, (f d).handshakeQueue = d.handshakeQueue) : SameView view (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [view, Option.map_map, Function.comp_def, hq]

theorem getPeer_frame (pid : PeerId) : SameView view (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hr
  exact congrArg view (Leanux.Proofs.WG.Peers.getPeer_current pid w v p ambient ambient' hr).1

theorem getKeypair_frame (id : KeypairId) : SameView view (getKeypair id) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient k v ambient' hr
  exact congrArg view (Leanux.Proofs.WG.Keypairs.getKeypair_current id w v ambient ambient' k hr).1

theorem setPeer_frame (pid : PeerId) (p : Peer) : SameView view (setPeer pid p) :=
  modify _ (fun _ => rfl)
/-- Source-head composition for the native device ring observation. -/
macro "handshake_queue_source" "[" fs:ident,* "]" : tactic => do
  let expand ← if fs.getElems.isEmpty then `(tactic| skip) else `(tactic| unfold $fs:ident*)
  `(tactic|
    (have ambient {α : Type} (a : AmbientM α) : SameView view (monadLift a : WG.M α) :=
       fun initial => hoare_liftAmbient a (fun w => view w = initial)
     have index {α : Type} (a : IndexM α) : SameView view (monadLift a : WG.M α) := by
       intro initial
       apply hoare_liftIndex
       intro g d table hg hd
       simpa [view, hd] using hg
     have read : SameView view (get : WG.M WGWorld) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w a x v a' hr
       cases hr
       rfl
     have stopped {α : Type} (e : Stop) : SameView view (throw e : WG.M α) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w a x v a' hr
       cases hr
     have edit (f : WGWorld → WGWorld) (hf : ∀ w, view (f w) = view w) :
         SameView view (_root_.modify f : WG.M Unit) := by
       intro initial
       apply hoare_modify
       intro w hw
       exact (hf w).trans hw
     have choice {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
         (hy : p → SameView view yes) (hn : ¬p → SameView view no) :
         SameView view (if p then yes else no) := by
       by_cases h : p
       · simpa only [ite_eq_left h] using hy h
       · simpa only [ite_eq_right h] using hn h
     have loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
         (hf : ∀ x b, SameView view (f x b)) : SameView view (forIn xs b f) :=
       fun initial => list_view_spec view (fun s => s = initial) xs b f (fun x b => hf x b initial)
     $expand
     repeat' first
       | ring_base_join
       | contradiction
       | (snapshot_head getPeer; exact getPeer_frame _)
       | (snapshot_head getKeypair; exact getKeypair_frame _)
       | (snapshot_head setPeer; exact setPeer_frame _ _)
       | (snapshot_head setKeypair; unfold setKeypair)
       | (snapshot_head IndexOwner.peerDeref; exact fun initial => indexOwner_peerDeref_preserves _ (fun w => view w = initial))
       | (snapshot_head modifyDev; exact modify _ (fun _ => rfl))
       | (snapshot_head _root_.modify; exact edit _ (fun _ => rfl))
       | (snapshot_head get; exact read)
       | (snapshot_head MonadStateOf.get; exact read)
       | (snapshot_head MonadLiftT.monadLift; first | (ring_base_lift AmbientM; exact ambient _) | (ring_base_lift IndexM; exact index _))
       | (snapshot_head MonadLift.monadLift; first | (ring_base_lift AmbientM; exact ambient _) | (ring_base_lift IndexM; exact index _))
       | (snapshot_head throw; exact stopped _)
       | (snapshot_head MonadExceptOf.throw; exact stopped _)
       | (snapshot_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).factor view)
       | (snapshot_head branch; unfold branch)
       | (snapshot_head branchCmp; unfold branchCmp)
       | (snapshot_head invariant; unfold invariant)
       | (snapshot_head unsupported; unfold unsupported)
       | (snapshot_head hiddenAlloc; unfold hiddenAlloc)
       | (snapshot_head refcountInc; unfold refcountInc)
       | (snapshot_head refcountIncNotZero; unfold refcountIncNotZero)
       | (snapshot_head refcountDecAndTest; unfold refcountDecAndTest)
       | (snapshot_head getDev; unfold getDev)
       | (snapshot_head requireNotPending; unfold requireNotPending)
       | (snapshot_head retirePeerUnits; unfold retirePeerUnits)
       | (snapshot_head modifyAmbient; unfold modifyAmbient)
       | (snapshot_head WG.orM; unfold WG.orM)
       | (snapshot_head liftM; unfold liftM)
       | (snapshot_head Pure.pure; exact SameView.pure _ _)
       | (snapshot_head Bind.bind; refine SameView.bind ?_ ?_)
       | (snapshot_head ForIn.forIn; apply loop)
       | (snapshot_head ite; apply choice)
       | keypairs_intro_forall
       | snapshot_head_reduce
       | snapshot_head_match))

theorem keypairGet_frame (id : Option KeypairId) : SameView view (keypairGet id) := by
  cases id <;> handshake_queue_source [keypairGet]

theorem keypairPut_frame (id : Option KeypairId) (now : Bool) : SameView view (keypairPut id now) := by
  cases id <;> handshake_queue_source [keypairPut]

theorem peerGet_frame (id : PeerId) : SameView view (peerGet id) := by
  handshake_queue_source [peerGet]

theorem peerGetMaybeZero_frame (id : Option PeerId) : SameView view (peerGetMaybeZero id) := by
  cases id <;> handshake_queue_source [peerGetMaybeZero]

theorem peerPut_frame (id : Option PeerId) : SameView view (peerPut id) := by
  cases id <;> handshake_queue_source [peerPut]

theorem indexLookup_frame (kinds : List IndexKind) (index : Nat) : SameView view (indexLookup kinds index) := by
  have peer (p : Option PeerId) : SameView view (peerGetMaybeZero p) := peerGetMaybeZero_frame p
  unfold indexLookup
  handshake_queue_source [IndexOwner.peerWord, IndexOwner.setPeerWord]
  all_goals exact peer _

theorem decryptPacket_frame (pkt : RxPacket) : SameView view (decryptPacket pkt) := by
  handshake_queue_source [decryptPacket]

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
