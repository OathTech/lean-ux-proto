import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCreateTailSource

/-! The original create return tests and repayments retain TX allocation
material. Their separate append proof keeps source history on Stop; their
physical frame applies at the actual successful repayment cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedDisposal HandshakeSecurity.StagedConservation
open PacketOrigins

theorem beforeFree_native_frame (pid : PeerId) (first : SkbId) (ret : Int) :
    SameView snapshot (beforeFreeNative pid first ret) := by
  intro initial
  have read (skb : SkbId) : SameView snapshot (getTxSkb skb) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a packet v b run
    exact congrArg snapshot (Packets.getTxSkb_current skb w v packet a b run).1
  have key (kid : Option KeypairId) := snapshot_pair
    (epoch_ring (TxRing.keypairPut_frame kid false)) (PacketMaterial.of_packets (TxDisposition.keyPut_packets kid false))
  have peer (p : Option PeerId) := snapshot_pair
    (epoch_ring (TxRing.peerPut_frame p)) (PacketMaterial.of_packets (TxDisposition.peerPut_packets p))
  change Preserves (fun w => snapshot w = initial) _
  unfold beforeFreeNative
  repeat' first
    | (allocation_release_head getTxSkb; exact (read _).wp (fun s => s = initial))
    | (allocation_release_head keypairPut; exact (key _).wp (fun s => s = initial))
    | (allocation_release_head peerPut; exact (peer _).wp (fun s => s = initial))
    | (allocation_release_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | allocation_release_step

theorem beforeFree_appends (pid : PeerId) (first : SkbId) (ret : Int) :
    Appends (beforeFree pid first ret) := by
  have step {α : Type} (action : WG.M α) : Appends (Admission.actualOps.step action) := Appends.focus _ _ _
  have access {α : Type} (action : MixedM α) : Appends (Admission.actualOps.access action) := Appends.focus _ _ _
  have release (peer : Option PeerId) : Appends (Admission.actualOps.release peer) :=
    (CausalJournal.CallbackQuiet.release (fun _ => (none : Option Unit))
      (fun _ => rfl) (fun _ => rfl) peer).1
  unfold beforeFree
  apply Appends.bind (step _)
  intro accepted
  cases accepted with
  | true => exact Appends.pure _
  | false =>
    simp only [Bool.false_eq_true,ite_false]
    apply Appends.bind (step _)
    intro pipe
    cases pipe with
    | true => exact Appends.pure _
    | false =>
      simp only [Bool.false_eq_true,ite_false]
      apply Appends.bind (access (getTxSkbPrefix first))
      intro packet
      apply Appends.bind (access (keypairPutPrefix (some packet.keypair) false))
      intro _
      apply Appends.bind (release (some pid))
      intro _
      exact Appends.pure _

theorem beforeFree_normal {cleanup : Bool} (pid : PeerId) (first : SkbId) (ret : Int)
    (performed : runPrefix (beforeFree pid first ret) w history = (.ok (cleanup,u),history ++ suffix))
    (support : FirstTerminal.Support births history ledger debts w.wg) :
    FirstTerminal.Support births (history ++ suffix) ledger debts u.wg := by
  have full := (beforeFree_erases pid first ret w history).symm.trans (congrArg Prod.fst performed)
  rw [liftWG_run] at full
  cases native : ((beforeFreeNative pid first ret).run w.wg).run w.ambient with
  | error stop => simp [native,Except.map] at full
  | ok out =>
    obtain ⟨⟨result,g⟩,ambient⟩ := out
    simp only [native,Except.map,Except.ok.injEq,Prod.mk.injEq] at full
    obtain ⟨rfl,rfl⟩ := full
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (beforeFree_native_frame pid first ret) w.wg w.ambient _ g ambient native
    exact (support.views (congrArg Prod.fst same) (congrArg Prod.snd same)).append suffix

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
