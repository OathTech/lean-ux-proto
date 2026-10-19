import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationQueueFrontier
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationAdmissionFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationPublicationSource

/-! DEAD publication borrows its actual key owner before publication and
repays that borrow afterward. Its repayment cannot erase staged obligations:
the source itself supplies the extra reference. These are native contracts,
not an assumption that every resident peer has a positive reference count. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Publication
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity Std.Do
set_option maxHeartbeats 1200000
set_option pp.structureInstances false

def stagedBorrow (pid : PeerId) (w : WGWorld) :=
  (Staged.stagedAt w,(PeerBorrow.resident (wgStoreView w) pid).map (·.refcount))

theorem cpu_staged (pid : PeerId) : SameView Staged.stagedAt (cpumaskChooseOnline pid) := by
  intro initial
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  cases hd : w.dev with
  | none =>
    simp [cpumaskChooseOnline,getPeer,getDev,hd,invariant,AmbientM.invariant] at hr
    cases hr
  | some d =>
    cases hp : d.peers[pid]? with
    | none =>
      simp [cpumaskChooseOnline,getPeer,getDev,hd,hp,invariant,AmbientM.invariant] at hr
      cases hr
    | some p =>
      by_cases invalid : 1 ≤ p.serialWorkCpu.getD 1 <;>
        simp [cpumaskChooseOnline,getPeer,getDev,setPeer,modifyDev,hd,hp,
          branch,AmbientM.branch,invalid,Nat.mod_one,List.foldlM] at hr
      all_goals rcases hr with ⟨⟨rfl,rfl⟩,rfl⟩
      all_goals first
        | exact hi
        | (rw [← hi]; funext id; by_cases same : pid = id <;>
            simp_all [Staged.stagedAt,Std.TreeMap.getElem?_insert])

theorem middle_staged (pid : PeerId) (first : SkbId) (state : PacketState) :
    SameView Staged.stagedAt (TxDisposition.publicationMiddle pid first state) := by
  intro initial
  change Preserves (fun w => Staged.stagedAt w = initial) _
  unfold TxDisposition.publicationMiddle
  repeat' first
    | (allocation_release_head getPeer; exact (Staged.Exact.read_peer _).wp (· = initial))
    | (allocation_release_head getDev; exact (getDev_sameWGStore.of_factor
        (fun s => Staged.stagedAt {dev := s.dev}) Staged.stagedAt (fun _ => rfl)).wp (· = initial))
    | (allocation_release_head setTxSkb; exact (Staged.Exact.skb _).wp (· = initial))
    | (allocation_release_head cpumaskChooseOnline; exact (cpu_staged _).wp (· = initial))
    | (allocation_release_head modifyDev; apply Staged.Exact.modify_preserves; intro d; rfl)
    | (allocation_release_head invariant; exact hoare_liftAmbient (AmbientM.invariant _) _)
    | (allocation_release_head peekQueuedUnit; exact hoare_liftAmbient (AmbientM.peekQueuedUnit _ _) _)
    | (allocation_release_head recordQueued; exact hoare_liftAmbient (AmbientM.recordQueued _ _) _)
    | allocation_release_step

theorem middle_borrow (pid : PeerId) (first : SkbId) (state : PacketState) :
    SameView (stagedBorrow pid) (TxDisposition.publicationMiddle pid first state) :=
  (middle_staged pid first state).product
    ((TxDisposition.publicationMiddle_frame pid first state).factor Prod.snd)

theorem acquire_staged (pid : PeerId) (q : PeerId → Option (Nat × List Packet)) :
    ⦃fun w => ⌜Staged.stagedAt w = q⌝⦄ peerGet pid
    ⦃⇓? _ w => ⌜Staged.stagedAt w = q ∧ ∃ n, 1 < n ∧
      (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount) = some n⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hi hr
  have same := (ProjectedAction.iff_run_ambient _ _ _).mp (Staged.Exact.peer_get pid)
    w ambient result v ambient' hr
  have hb := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.strict_acquire_spec pid (wgStoreView w)) w ambient result v ambient' rfl hr
  obtain ⟨d,p,_,_,positive,current⟩ := hb
  exact ⟨same.trans hi,p.refcount+1,by omega,by simp [current,PeerBorrow.resident]⟩

theorem nonfinal_put_staged (pid : PeerId) (q : PeerId → Option (Nat × List Packet)) :
    ⦃fun w => ⌜Staged.stagedAt w = q ∧ ∃ n, 1 < n ∧
      (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount) = some n⌝⦄ peerPut (some pid)
    ⦃⇓? _ w => ⌜Staged.stagedAt w = q⌝⦄ := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w ambient u v ambient' hb hr
  obtain ⟨hq,n,hn,href⟩ := hb
  cases hd : w.dev with
  | none => simp [PeerBorrow.resident,wgStoreView,hd] at href
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [PeerBorrow.resident,wgStoreView,hd,hp] at href
    | some p =>
      have hc : 1 < p.refcount := by
        have he : p.refcount = n := by simpa [PeerBorrow.resident,wgStoreView,hd,hp] using href
        omega
      have pos : 0 < p.refcount := by omega
      have nz : p.refcount ≠ 0 := by omega
      have notone : p.refcount ≠ 1 := by omega
      simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,hd,hp,
        refcountDecAndTest,branch,branchCmp,AmbientM.branch,AmbientM.branchCmp,pos,nz,notone] at hr
      rcases hr with ⟨rfl,rfl⟩
      rw [← hq]
      funext id
      by_cases same : pid = id <;>
        simp_all [Staged.stagedAt,Std.TreeMap.getElem?_insert]

/-- Every completed native publication preserves all staged queues exactly,
including absent peers. Its paired reference repayment is nonfinal. -/
theorem staged (item : List SkbId) (state : PacketState) :
    SameView Staged.stagedAt (enqueuePerPeerTx item state) := by
  intro q
  rw [TxDisposition.publication_factor]
  cases item.head? with
  | none => exact hoare_liftAmbient (AmbientM.invariant _) _
  | some first =>
    apply hoare_bind _ _ ((Staged.Exact.skb (SkbStore.getTx first)).wp (· = q))
    intro packet
    apply hoare_bind _ _ (indexOwner_peerDeref_preserves _ (fun w => Staged.stagedAt w = q))
    intro pid
    apply hoare_bind _ _ (acquire_staged pid q)
    intro _
    apply hoare_bind _ _ ((middle_borrow pid first state).wp
      (fun t => t.1 = q ∧ ∃ n, 1 < n ∧ t.2 = some n))
    intro _
    exact nonfinal_put_staged pid q

/-- The actual borrow prefix supplies the extra reference at its returned
owner, irrespective of the caller's peer parameter. -/
theorem borrow_funded (items : List SkbId) (a b : Ambient)
    (run : ((borrowNative items).run w).run a = .ok (((first,pid),v),b)) :
    ∃ n, 1 < n ∧ (PeerBorrow.resident (wgStoreView v) pid).map (·.refcount) = some n := by
  unfold borrowNative at run
  cases head : items.head? with
  | none => simp only [head] at run; cases run
  | some chosen =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨packet,u,c,_,owner,t,e,_,_,z,f,acquired,done⟩ := run
    cases done
    have funded := (hoare_iff_run_ambient _ _ _).mp
      (acquire_staged pid (Staged.stagedAt t)) t e () v b rfl acquired
    exact funded.2

/-- The reached middle cannot spend the publication borrow. -/
theorem middle_funded (pid : PeerId) (first : SkbId) (state : PacketState)
    (funded : ∃ n, 1 < n ∧ (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount) = some n)
    (a b : Ambient)
    (run : ((TxDisposition.publicationMiddle pid first state).run w).run a = .ok (((),v),b)) :
    ∃ n, 1 < n ∧ (PeerBorrow.resident (wgStoreView v) pid).map (·.refcount) = some n := by
  have same := congrArg Prod.snd ((ProjectedAction.iff_run_ambient _ _ _).mp
    (TxDisposition.publicationMiddle_frame pid first state) w a () v b run)
  change (PeerBorrow.resident (wgStoreView v) pid).map (·.refcount) =
    (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount) at same
  rw [same]
  exact funded

/-- At the final source repayment cut the paired publication reference is
nonfinal. The exact native cut returns `none`; it cannot erase staged packets
or run final-release cleanup, even when those staged packets are nonempty. -/
theorem release_cut_nonfinal (pid : PeerId)
    (funded : ∃ n, 1 < n ∧ (PeerBorrow.resident (wgStoreView w) pid).map (·.refcount) = some n)
    (a : Ambient) :
    ∃ v b, ((HandshakeSecurity.StagedDisposal.releaseCut (some pid)).run w).run a =
      .ok ((none,v),b) := by
  obtain ⟨n,hn,href⟩ := funded
  cases hd : w.dev with
  | none => simp [PeerBorrow.resident,wgStoreView,hd] at href
  | some d =>
    cases hp : d.peers[pid]? with
    | none => simp [PeerBorrow.resident,wgStoreView,hd,hp] at href
    | some p =>
      have hc : 1 < p.refcount := by
        have he : p.refcount = n := by simpa [PeerBorrow.resident,wgStoreView,hd,hp] using href
        omega
      have pos : 0 < p.refcount := by omega
      have nz : p.refcount ≠ 0 := by omega
      have notone : p.refcount ≠ 1 := by omega
      simp [HandshakeSecurity.StagedDisposal.releaseCut,requireNotPending,getPeer,getDev,
        setPeer,modifyDev,hd,hp,refcountDecAndTest,branch,branchCmp,AmbientM.branch,
        AmbientM.branchCmp,pos,nz,notone]

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.Publication
