import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationErrorFrames
import Leanux.Proofs.WG.Queues.RxRingFrames

/-! The transmit prelude preserves the invocation-level error counter. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Packets Queues.RxRing Std.Do
open Leanux.Proofs.WG.Keypairs Leanux.Proofs.WG.Keypairs.WGFrames
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem modify_errors (f : Device → Device)
    (hq : ∀ d, (f d).txErrors = d.txErrors) : SameView errors (modifyDev f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  simp [errors, Option.map_map, Function.comp_def, hq]

theorem getPeer_errors (pid : PeerId) : SameView errors (getPeer pid) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient p v ambient' hr
  exact congrArg errors (Leanux.Proofs.WG.Peers.getPeer_current pid w v p ambient ambient' hr).1

theorem setPeer_errors (pid : PeerId) (p : Peer) : SameView errors (setPeer pid p) :=
  modify_errors _ (fun _ => rfl)

macro "error_counter_source" "[" fs:ident,* "]" : tactic => do
  let expand ← if fs.getElems.isEmpty then `(tactic| skip) else `(tactic| unfold $fs:ident*)
  `(tactic|
    (have ambient {α : Type} (a : AmbientM α) : SameView errors (monadLift a : WG.M α) :=
       fun initial => hoare_liftAmbient a (fun w => errors w = initial)
     have index {α : Type} (a : IndexM α) : SameView errors (monadLift a : WG.M α) := by
       intro initial
       apply hoare_liftIndex
       intro g d table hg hd
       simpa [errors, hd] using hg
     have read : SameView errors (get : WG.M WGWorld) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w a x v a' hr
       cases hr
       rfl
     have stopped {α : Type} (e : Stop) : SameView errors (throw e : WG.M α) := by
       apply (ProjectedAction.iff_run_ambient _ _ _).mpr
       intro w a x v a' hr
       cases hr
     have edit (f : WGWorld → WGWorld) (hf : ∀ w, errors (f w) = errors w) :
         SameView errors (_root_.modify f : WG.M Unit) := by
       intro initial
       apply hoare_modify
       intro w hw
       exact (hf w).trans hw
     have choice {α : Type} (p : Prop) [Decidable p] (yes no : WG.M α)
         (hy : p → SameView errors yes) (hn : ¬p → SameView errors no) :
         SameView errors (if p then yes else no) := by
       by_cases h : p
       · simpa only [ite_eq_left h] using hy h
       · simpa only [ite_eq_right h] using hn h
     have loop {α β : Type} (xs : List α) (b : β) (f : α → β → WG.M (ForInStep β))
         (hf : ∀ x b, SameView errors (f x b)) : SameView errors (forIn xs b f) :=
       fun initial => list_view_spec errors (fun s => s = initial) xs b f (fun x b => hf x b initial)
     $expand
     repeat' first
       | ring_base_join
       | contradiction
       | (snapshot_head getPeer; exact getPeer_errors _)
       | (snapshot_head setPeer; exact setPeer_errors _ _)
       | (snapshot_head IndexOwner.peerDeref; exact fun initial => indexOwner_peerDeref_preserves _ (fun w => errors w = initial))
       | (snapshot_head modifyDev; exact modify_errors _ (fun _ => rfl))
       | (snapshot_head _root_.modify; exact edit _ (fun _ => rfl))
       | (snapshot_head get; exact read)
       | (snapshot_head MonadStateOf.get; exact read)
       | (snapshot_head MonadLiftT.monadLift; first | (ring_base_lift AmbientM; exact ambient _) | (ring_base_lift IndexM; exact index _))
       | (snapshot_head MonadLift.monadLift; first | (ring_base_lift AmbientM; exact ambient _) | (ring_base_lift IndexM; exact index _))
       | (snapshot_head throw; exact stopped _)
       | (snapshot_head MonadExceptOf.throw; exact stopped _)
       | (snapshot_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).factor errors)
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

theorem peerPut_errors (id : Option PeerId) : SameView errors (peerPut id) := by
  cases id <;> error_counter_source [peerPut]

theorem headers_errors (family addr : Nat) (pkts : List Packet) :
    SameView errors (txHeaders family addr pkts) := by
  error_counter_source [txHeaders]

theorem walk_errors (pkts : List Packet) (mtu : Nat) (acc : List Packet) :
    SameView errors (txWalk pkts mtu acc) := by
  error_counter_source [txWalk]

theorem trim_errors (pid : PeerId) : SameView errors (xmitTrim pid) := by
  unfold xmitTrim
  apply SameView.bind (getPeer_errors pid)
  intro peer
  apply SameView.bind
  · rw [Std.Legacy.Range.forIn_eq_forIn_range']
    error_counter_source []
  · intro _; exact SameView.pure _ _

theorem splice_errors (pid : PeerId) (pkts : List Packet) :
    SameView errors (xmitSplice pid pkts) := by
  error_counter_source [xmitSplice]


theorem envOk_errors (site : EnvSite) : SameView errors (envOk site : WG.M Bool) := by
  error_counter_source [envOk]


theorem lookup_errors (family addr : Nat) : SameView errors (lookupDst family addr) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (Queues.RxBorrow.lookupDst_spec family addr (wgStoreView w)) w a result v b rfl run
  cases result with
  | none => exact congrArg (fun s => s.dev.map Device.txErrors) borrowed
  | some pid =>
    obtain ⟨d,p,device,_,_,after⟩ := borrowed
    change w.dev = some d at device
    have endpoint : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount+1}} :=
      congrArg WGStoreView.dev after
    simp only [errors,endpoint,Option.map_some,device]


end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Front
