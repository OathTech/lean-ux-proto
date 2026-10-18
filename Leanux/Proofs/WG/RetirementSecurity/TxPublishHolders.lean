import Leanux.Proofs.WG.RetirementSecurity.WorkerHolderClosure
import Leanux.Proofs.WG.RetirementSecurity.TxEnqueueHolders

/-! Device completion publishes a packet state while borrowing its peer.
The borrow creates no key reference, and its own positive count prevents the
matching put from removing any physical key-holder group. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem HolderAccount.peer_get (account : HolderAccount temporary w)
    (pid : PeerId) (a b : Ambient)
    (run : ((peerGet pid).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v ∧ ∃ p, peerAt v pid = some p ∧ 1 < p.refcount := by
  obtain ⟨d,p,device,stored,positive,current⟩ := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.strict_acquire_spec pid (wgStoreView w)) w a () v b rfl run
  have after : v.dev = some {d with peers := d.peers.insert pid {p with refcount := p.refcount + 1}} :=
    congrArg WGStoreView.dev current
  have moved := account.peer_fields device stored
    (q := {p with refcount := p.refcount + 1}) ⟨rfl,rfl,rfl⟩
  refine ⟨moved.store ?_,{p with refcount := p.refcount + 1},?_,by simpa using positive⟩
  · simp [holderStore,Origins.view,peersAt,packetKeyWords,replacePeer,after]
  · simp [peerAt,after]

theorem cpu_holders (pid : PeerId) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (cpumaskChooseOnline pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  cases device : w.dev with
  | none =>
    simp [cpumaskChooseOnline,getPeer,getDev,device,invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases stored : d.peers[pid]? with
    | none =>
      simp [cpumaskChooseOnline,getPeer,getDev,device,stored,invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      by_cases invalid : 1 ≤ p.serialWorkCpu.getD 1 <;>
        simp [cpumaskChooseOnline,getPeer,getDev,setPeer,modifyDev,device,stored,
          branch,AmbientM.branch,invalid,Nat.mod_one,List.foldlM] at run
      all_goals rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
      all_goals first
        | exact account
        | exact account.peer_fields device stored ⟨rfl,rfl,rfl⟩

theorem publication_middle_holders (pid : PeerId) (first : SkbId) (state : PacketState)
    (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (Queues.TxDisposition.publicationMiddle pid first state) := by
  let P : WGWorld → Prop := HolderAccount temporary
  have ambient {α : Type} (action : AmbientM α) :
      Preserves P (monadLift action : WG.M α) := hoare_liftAmbient action P
  have getter : Preserves P getDev :=
    holderStore_preserves _ (holderStore_kernel _ getDev_sameWGStore) temporary
  have mark : Preserves P (setTxSkb first (fun p => {p with state})) :=
    holderStore_preserves _ (setTx_holderStore first (fun p => {p with state}) (fun _ => rfl)) temporary
  have queued : Preserves P (modifyDev fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]}) :=
    holderStore_preserves _ (modifyDev_holderStore
      (fun d => {d with txWorkQueue := d.txWorkQueue ++ [pid]})
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) temporary
  change Preserves P (Queues.TxDisposition.publicationMiddle pid first state)
  unfold Queues.TxDisposition.publicationMiddle
  simp only [invariant,peekQueuedUnit,recordQueued]
  repeat' first
    | (allocation_release_head cpumaskChooseOnline; exact cpu_holders pid temporary)
    | (allocation_release_head setTxSkb; exact mark)
    | (allocation_release_head modifyDev; exact queued)
    | (allocation_release_head getPeer; exact getPeer_preserves _ P)
    | (allocation_release_head getDev; exact getter)
    | (allocation_release_lift_from AmbientM; exact ambient _)
    | allocation_release_step

theorem HolderAccount.publish_tx (account : HolderAccount temporary w)
    (item : List SkbId) (state : PacketState) (a b : Ambient)
    (run : ((enqueuePerPeerTx item state).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  rw [Queues.TxDisposition.publication_factor] at run
  cases head : item.head? with
  | none => simp only [head] at run; cases run
  | some first =>
    simp only [head,MaterialOrigin.bind_ok_ambient] at run
    obtain ⟨packet,u,aa,readRun,pid,t,ab,ownerRun,_,s,ac,getRun,_,e,ae,middleRun,putRun⟩ := run
    have hu : HolderAccount temporary u :=
      (Packets.getTxSkb_current first w u packet a aa readRun).1 ▸ account
    have ht := (hoare_iff_run_ambient _ _ _).mp
      (indexOwner_peerDeref_preserves (.keypair packet.keypair) (HolderAccount temporary))
      u aa pid t ab hu ownerRun
    obtain ⟨hs,p,found,positive⟩ := ht.peer_get pid ab ac getRun
    have he := (hoare_iff_run_ambient _ _ _).mp
      (publication_middle_holders pid first state temporary) s ac () e ae hs middleRun
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (Queues.TxDisposition.publicationMiddle_frame pid first state) s ac () e ae middleRun
    have count : (peerAt e pid).map (·.refcount) = some p.refcount := by
      have equation := congrArg (fun shape => shape.2) same
      change (peerAt e pid).map (·.refcount) = (peerAt s pid).map (·.refcount) at equation
      simpa only [found,Option.map_some] using equation
    have ready : PeerReleaseReady pid e := by
      intro q resident final
      rw [resident] at count
      simp only [Option.map_some,Option.some.injEq] at count
      omega
    exact he.peer_put ready ae b putRun

end Leanux.Proofs.WG.RetirementSecurity
