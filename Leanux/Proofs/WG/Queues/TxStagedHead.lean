import Leanux.Proofs.WG.Queues.TxItemSeparation
import Leanux.Proofs.WG.Queues.TxSelectedEncrypt

/-! The full original staged-send prefix preserves packet boundedness until
its actual fresh allocation. The resulting native source cut retains any
previously resident head, including DEAD heads. -/
namespace Leanux.Proofs.WG.Queues.TxDisposition.StagedHead
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do RxCredits

private abbrev Ready (target : SkbId) (state : PacketState) (w : WGWorld) : Prop :=
  Packets.Inv w ∧ HeadState target state w

private theorem modify_ready (target : SkbId) (state : PacketState) (f : Device→Device)
    (frontier : ∀d,(f d).nextSkb=d.nextSkb)
    (tx : ∀d,(f d).txSkbs=d.txSkbs) (rx : ∀d,(f d).rxSkbs=d.rxSkbs) :
    Preserves (Ready target state) (modifyDev f) := by
  apply hoare_modify
  intro w hi
  cases hd:w.dev <;>
    simpa only [Ready,Packets.Inv,Packets.snapshot,Packets.deviceStore,HeadState,
      txPackets,hd,Option.map_none,Option.map_some,Option.bind_none,Option.bind_some,
      frontier,tx,rx] using hi

private theorem read_peer (target : SkbId) (state : PacketState) (pid : PeerId) :
    Preserves (Ready target state) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b hi run
  simpa only [(Peers.getPeer_current pid w v p a b run).1] using hi

private theorem read_key (target : SkbId) (state : PacketState) (kid : KeypairId) :
    Preserves (Ready target state) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a k v b hi run
  simpa only [(KeyTimes.getKeypair_return kid w v k a b run).1] using hi

private theorem index_ready (target : SkbId) (state : PacketState) (a : IndexM α) :
    Preserves (Ready target state) (liftIndex a) := by
  apply hoare_liftIndex
  intro w d table hi hd
  simpa only [Ready,Packets.Inv,Packets.snapshot,Packets.deviceStore,HeadState,
    txPackets,hd,Option.bind_some] using hi

macro "staged_head_base " target:term "," state:term : tactic => `(tactic| first
  | rxstack_preserves_join
  | (allocation_release_head getPeer; exact read_peer $target $state _)
  | (allocation_release_head getKeypair; exact read_key $target $state _)
  | (allocation_release_head getDev; unfold getDev)
  | (allocation_release_head setPeer; unfold setPeer)
  | (allocation_release_head setKeypair; unfold setKeypair)
  | (allocation_release_head modifyDev
     apply modify_ready $target $state
     all_goals intro d; rfl)
  | (allocation_release_head get; exact hoare_consequence (hoare_get _)
      (fun _ h=>h) (fun _ _ h=>h.2))
  | (allocation_release_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (allocation_release_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (Ready $target $state))
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (allocation_release_lift_from IndexM; exact index_ready $target $state _)
  | (allocation_release_head ForIn.forIn
     apply list_view_spec id (Ready $target $state)
     intro x b
     change Preserves (Ready $target $state) _)
  | (allocation_release_head modify; apply hoare_modify; intro w hi; exact hi)
  | allocation_release_step)

private theorem peer_get (target : SkbId) (state : PacketState) (pid : PeerId) :
    Preserves (Ready target state) (peerGet pid) := by
  unfold peerGet refcountInc
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,unsupported]
  repeat' staged_head_base target, state

private theorem peer_put (target : SkbId) (state : PacketState) (pid : Option PeerId) :
    Preserves (Ready target state) (peerPut pid) := by
  unfold peerPut refcountDecAndTest retirePeerUnits
  simp (config := {zeta := false}) only [requireNotPending,pure_bind,branch,branchCmp,
    invariant,unsupported,modifyAmbient]
  repeat' staged_head_base target, state

private theorem key_get (target : SkbId) (state : PacketState) (kid : Option KeypairId) :
    Preserves (Ready target state) (keypairGet kid) := by
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' staged_head_base target, state

private theorem key_put (target : SkbId) (state : PacketState) (kid : Option KeypairId) (now : Bool) :
    Preserves (Ready target state) (keypairPut kid now) := by
  unfold keypairPut refcountDecAndTest
  simp (config := {zeta := false}) only [branch,branchCmp,invariant,unsupported]
  repeat' staged_head_base target, state

private theorem queued (target : SkbId) (state : PacketState) (pid : PeerId) (retry : Bool) :
    Preserves (Ready target state) (sendQueuedHandshakeInitiation pid retry) := by
  unfold sendQueuedHandshakeInitiation
  simp (config := {zeta := false}) only [branch,peekQueuedUnit,recordQueued]
  repeat' first
    | (allocation_release_head peerGet; exact peer_get target state _)
    | (allocation_release_head peerPut; exact peer_put target state _)
    | staged_head_base target, state

private theorem no_key (target : SkbId) (state : PacketState) (pid : PeerId)
    (packets : List WG.Packet) (keypair : Option KeypairId) (invalid : Bool) :
    Preserves (Ready target state) (stagedOutNokey pid packets keypair invalid) := by
  unfold stagedOutNokey
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head keypairPut; exact key_put target state _ _)
    | (allocation_release_head sendQueuedHandshakeInitiation; exact queued target state _ _)
    | staged_head_base target, state

/-- The actual key-selected staging continuation preserves the saved head;
its no-key returns, nonce loop and final fresh submission remain in source order. -/
theorem key_source (target : SkbId) (state : PacketState) (pid kid : Nat)
    (packets : List WG.Packet) :
    Hoare (stagedKeySource pid kid packets) (Ready target state) (fun _=>HeadState target state) := by
  let P := Ready target state
  have getter := read_key target state kid
  have setter (id : KeypairId) (key : Keypair) : Preserves P (setKeypair id key) := by
    apply modify_ready target state <;> intro d <;> rfl
  have expired := fun date=>
    (branchExpired_sameWGWorld .stagedBirthdateExpired date REJECT_AFTER_TIME).wp P
  have ecn := fun pkt=>(ipTunnelEcnEncap_sameWGWorld pkt).wp P
  have out := no_key target state pid packets (some kid)
  have submit := ItemSeparation.staged_submit_head pid kid
  have weaken {α : Type} (a : WG.M α) (h : Preserves P a) :
      Hoare a P (fun _=>HeadState target state) :=
    hoare_consequence h (fun _ h=>h) (fun _ _ h=>h.2)
  have step {α β : Type} (a : WG.M α) (f : α→WG.M β)
      (Q : β→WGWorld→Prop) (ha : Preserves P a)
      (hf : ∀x,Hoare (f x) P Q) : Hoare (a>>=f) P Q := hoare_bind a f ha hf
  unfold stagedKeySource
  change Hoare _ P (fun _=>HeadState target state)
  simp (config := {zeta := false}) only [branch,branchCmp]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getKeypair; exact getter)
    | (index_material_head setKeypair; exact setter _ _)
    | (index_material_head branchExpired; exact expired _)
    | (index_material_head ipTunnelEcnEncap; exact ecn _)
    | (index_material_head stagedOutNokey; first | exact out _ | exact weaken _ (out _))
    | (index_material_head stagedSubmit; exact submit _ target state)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | (index_material_head Pure.pure; first | exact preserves_pure _ | exact weaken _ (preserves_pure _))
    | (index_material_head Bind.bind; apply step)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

/-- Full native staged send, including all normal refusal/no-key arms,
retains an old resident head using actual allocation-frontier validity. -/
theorem send (pid : PeerId) (target : SkbId) (state : PacketState) :
    Hoare (sendStagedPackets pid) (fun w=>Packets.Inv w ∧ HeadState target state w)
      (fun _=>HeadState target state) := by
  let P := Ready target state
  have read := read_peer target state
  have write (id : PeerId) (peer : Peer) : Preserves P (setPeer id peer) := by
    apply modify_ready target state <;> intro d <;> rfl
  have key := key_get target state
  have out := no_key target state
  have weaken {α : Type} (a : WG.M α) (h : Preserves P a) :
      Hoare a P (fun _=>HeadState target state) :=
    hoare_consequence h (fun _ h=>h) (fun _ _ h=>h.2)
  have step {α β : Type} (a : WG.M α) (f : α→WG.M β)
      (Q : β→WGWorld→Prop) (ha : Preserves P a)
      (hf : ∀x,Hoare (f x) P Q) : Hoare (a>>=f) P Q := hoare_bind a f ha hf
  rw [← stagedFullSource_eq]
  unfold stagedFullSource
  change Hoare _ P (fun _=>HeadState target state)
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head getPeer; exact read _)
    | (index_material_head setPeer; exact write _ _)
    | (index_material_head keypairGet; exact key _)
    | (index_material_head stagedOutNokey; first | exact out _ _ _ _ | exact weaken _ (out _ _ _ _))
    | (index_material_head stagedKeySource; exact key_source target state _ _ _)
    | (index_material_head Pure.pure; first | exact preserves_pure _ | exact weaken _ (preserves_pure _))
    | (index_material_head Bind.bind; apply step)
    | material_component
    | material_intro
    | (index_material_head ite; split)
    | material_reduce
    | material_match

end Leanux.Proofs.WG.Queues.TxDisposition.StagedHead
