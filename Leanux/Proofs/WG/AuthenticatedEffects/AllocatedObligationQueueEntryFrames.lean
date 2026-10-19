import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueEntrySource
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedCreationFrames

/-! The pre-installation prefix preserves the same fixed allocation cells,
staged queues and unpublished ownership. A returned peer is its actual
resident peer at the installation cut. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open Staged.Obligations
set_option pp.structureInstances false

theorem before_appends (pid : PeerId) (items : List SkbId) : Appends (before pid items) := by
  unfold before
  repeat' first
    | exact Appends.focus _ _ _
    | exact Appends.lift _
    | exact Appends.pure _
    | apply Appends.bind
    | maintenance_intro
    | dsimp (config := {failIfUnchanged := true}) only
    | split

theorem offered_appends (items : List SkbId) (ret : Int) : Appends (offered items ret) := by
  unfold offered
  split <;> try split
  all_goals first
    | exact Appends.pure _
    | exact Appends.bind (fun _ _ => ⟨[_],rfl⟩) (fun _ => Appends.pure _)

theorem before_native_views (pid : PeerId) (items : List SkbId) :
    SameView (fun w => (PacketOrigins.snapshot w,Staged.stagedAt w)) (beforeNative pid items) := by
  intro initial
  have mark (first : SkbId) :=
    (PacketOrigins.snapshot_pair (PacketOrigins.skb_epoch _)
      (PacketMaterial.set_tx first (fun p => {p with state := .uncrypted}) (fun _ => rfl))).wp
      (fun s => s = initial.1)
  have queues (first : SkbId) := (Staged.Exact.skb (SkbStore.setTx first fun p => {p with state := .uncrypted})).wp (fun q => q = initial.2)
  have read : SameView (fun w => (PacketOrigins.snapshot w,Staged.stagedAt w)) (getPeer pid) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a p v b run
    exact congrArg (fun w => (PacketOrigins.snapshot w,Staged.stagedAt w))
      (Peers.getPeer_current pid w v p a b run).1
  change Preserves (fun w => (PacketOrigins.snapshot w,Staged.stagedAt w) = initial) _
  unfold beforeNative
  repeat' first
    | (allocation_release_head setTxSkb
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a value v b before run
       have hp := (hoare_iff_run_ambient _ _ _).mp (mark _) w a value v b (congrArg Prod.fst before) run
       have hq := (hoare_iff_run_ambient _ _ _).mp (queues _) w a value v b (congrArg Prod.snd before) run
       exact Prod.ext hp hq)
    | (allocation_release_head getPeer; exact read.wp (· = initial))
    | (allocation_release_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | allocation_release_step

theorem before_native_entry
    (coverage : TxCoverage (⟨.unpublished,pid,items⟩ :: locals) w)
    (inventory : TxInventory (⟨.unpublished,pid,items⟩ :: locals) w)
    (a b : Ambient)
    (run : ((beforeNative pid items).run w).run a = .ok ((candidate,v),b)) :
    TxCoverage (⟨.unpublished,pid,items⟩ :: locals) v ∧
    TxInventory (⟨.unpublished,pid,items⟩ :: locals) v ∧
    ∀ p, candidate = some p → ∃ d, v.dev = some d ∧ d.peers[pid]? = some p := by
  unfold beforeNative at run
  cases head : items.head? with
  | none => simp only [head] at run; cases run
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨_,u,c,markRun,p,t,e,peerRun,full,s,f,branchRun,tail⟩ := run
    have marked := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ownershipPoints_holderStore _
        (setTx_holderStore first (fun p => {p with state := .uncrypted}) (fun _ => rfl)))
      w a () u c markRun
    obtain ⟨same,_,d,device,found⟩ := Origins.getPeer_return pid u t p c e peerRun
    subst t
    have same : s = u := (hoare_iff_run_ambient _ _ _).mp
      (hoare_liftAmbient (AmbientM.branch .enqueuePeerQueueFull
        (decide (p.txQueue.count ≥ MAX_QUEUED_PACKETS))) (fun s => s = u))
      u e full s f rfl branchRun
    subst s
    cases full with
    | true =>
      simp only [ite_true] at tail
      cases tail
      exact ⟨coverage.points marked,inventory.points marked,by intro p same; cases same⟩
    | false =>
      simp only [Bool.false_eq_true,ite_false] at tail
      cases tail
      refine ⟨coverage.points marked,inventory.points marked,?_⟩
      intro q same
      cases same
      exact ⟨d,device,found⟩

theorem after_native_views (items : List SkbId) :
    SameView (fun w => (PacketOrigins.snapshot w,Staged.stagedAt w)) (RxCredits.enqueueTailItem items) := by
  intro initial
  have store {α : Type} {action : WG.M α} (same : SameWGStore action) :
      SameView (fun w => (PacketOrigins.snapshot w,Staged.stagedAt w)) action :=
    same.of_factor (fun s => (PacketOrigins.snapshot {dev := s.dev},Staged.stagedAt {dev := s.dev})) _
      (fun _ => rfl)
  have edit (f : Device → Device) (epochs : ∀ d, (f d).ifindex = d.ifindex)
      (packets : ∀ d, (f d).txSkbs = d.txSkbs) (peers : ∀ d, (f d).peers = d.peers) :=
    ((PacketOrigins.modify f epochs packets).product (Staged.Exact.modify_device f peers)).wp (· = initial)
  change Preserves (fun w => (PacketOrigins.snapshot w,Staged.stagedAt w) = initial) _
  unfold RxCredits.enqueueTailItem
  repeat' first
    | (allocation_release_head getDev; exact (store getDev_sameWGStore).wp (· = initial))
    | (allocation_release_head cpumaskNextOnlineFrom; exact (store (cpumaskNextOnlineFrom_sameStore _)).wp (· = initial))
    | (allocation_release_head modifyDev; exact edit _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl))
    | (allocation_release_head branch; exact hoare_liftAmbient (AmbientM.branch _ _) _)
    | (allocation_release_head queueDeviceWork; exact hoare_liftAmbient (AmbientM.queueDeviceWork _) _)
    | allocation_release_step

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.QueueHandoff
