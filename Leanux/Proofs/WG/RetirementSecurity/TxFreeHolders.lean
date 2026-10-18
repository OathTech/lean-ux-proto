import Leanux.Proofs.WG.RetirementSecurity.HolderStoreFrames

/-! Native packet disposal preserves the key-holder account when the freed
IDs are no longer heads of any durable TX batch. This is the concrete alias
condition that the queue/allocation history must supply at disposal cuts. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem mapM_congr_on (f g : α → Option β) (xs : List α)
    (same : ∀ x ∈ xs, f x = g x) : xs.mapM f = xs.mapM g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,same x (by simp),ih (fun y h => same y (by simp [h]))]

theorem HolderAccount.named_store (account : HolderAccount temporary w)
    (keys : Origins.view v = Origins.view w) (peers : peersAt v = peersAt w)
    (names : ∀ pid p, peerAt w pid = some p → peerLoans v pid p = peerLoans w pid p) :
    HolderAccount temporary v := by
  obtain ⟨loans,projected,credits⟩ := account
  refine ⟨loans,?_,credits.view keys⟩
  cases dw : w.dev <;> cases dv : v.dev
  all_goals simp only [peersAt,dw,dv,Option.map_none,Option.map_some,Option.some.injEq] at peers
  all_goals try contradiction
  · simpa [durableLoans,dw,dv] using projected
  · rename_i d e
    have mapped : d.peers.toList.mapM (fun (pid,p) => peerLoans v pid p) =
        d.peers.toList.mapM (fun (pid,p) => peerLoans w pid p) := by
      apply mapM_congr_on
      intro pair member
      apply names
      simp only [peerAt,dw,Option.bind_some]
      exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
    simpa only [durableLoans,dw,dv,peers,mapped] using projected

theorem HolderAccount.named_lists (account : HolderAccount temporary w)
    (keys : Origins.view v = Origins.view w)
    (peers : v.dev.map (fun d => d.peers.toList) = w.dev.map (fun d => d.peers.toList))
    (names : ∀ pid p, peerAt w pid = some p → peerLoans v pid p = peerLoans w pid p) :
    HolderAccount temporary v := by
  obtain ⟨loans,projected,credits⟩ := account
  refine ⟨loans,?_,credits.view keys⟩
  cases dw : w.dev <;> cases dv : v.dev
  all_goals simp only [dw,dv,Option.map_none,Option.map_some,Option.some.injEq] at peers
  all_goals try contradiction
  · simpa [durableLoans,dw,dv] using projected
  · rename_i d e
    have mapped : d.peers.toList.mapM (fun (pid,p) => peerLoans v pid p) =
        d.peers.toList.mapM (fun (pid,p) => peerLoans w pid p) := by
      apply mapM_congr_on
      intro pair member
      apply names
      simp only [peerAt,dw,Option.bind_some]
      exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
    simpa only [durableLoans,dw,dv,peers,mapped] using projected

def TxDetached (items : List SkbId) (w : WGWorld) : Prop :=
  ∀ pid p, peerAt w pid = some p → ∀ batch ∈ p.txQueue.all,
    ∀ head, batch.head? = some head → head ∉ items

theorem freeTx_peer_names {id : SkbId} (device : w.dev = some d) (pid : PeerId) (p : Peer)
    (absent : ∀ batch ∈ p.txQueue.all, batch.head? ≠ some id) :
    peerLoans (Packets.update w (fun d => {d with txSkbs := d.txSkbs.erase id})) pid p =
      peerLoans w pid p := by
  have names (holder : KeyHolder) :
      nameLoan (Packets.update w (fun d => {d with txSkbs := d.txSkbs.erase id})) holder =
        nameLoan w holder := by
    funext key
    simp [nameLoan,keyAt,Packets.update,device]
  have rx : receiveLoan (Packets.update w (fun d => {d with txSkbs := d.txSkbs.erase id})) pid =
      receiveLoan w pid := by
    funext packet
    simp only [receiveLoan,names]
    simp [Packets.update,device]
  have tx : p.txQueue.all.mapM
      (transmitLoan (Packets.update w (fun d => {d with txSkbs := d.txSkbs.erase id})) pid) =
      p.txQueue.all.mapM (transmitLoan w pid) := by
    apply mapM_congr_on
    intro batch member
    cases head : batch.head? with
    | none => simp [transmitLoan,head]
    | some first =>
      have different : id ≠ first := by intro eq; subst first; exact absent batch member head
      simp only [transmitLoan,names]
      simp [head,Packets.update,device,Std.TreeMap.getElem?_erase,different]
  simp only [peerLoans_eq,names,rx,tx]

theorem HolderAccount.free_tx {id : SkbId} (account : HolderAccount temporary w)
    (detached : TxDetached items w) (member : id ∈ items) (a b : Ambient)
    (run : ((freeTxSkb id).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v ∧ TxDetached items v := by
  cases device : w.dev with
  | none => simp [freeTxSkb,liftSkb_run,device] at run
  | some d =>
    cases packet : d.txSkbs[id]? with
    | none =>
      simp [freeTxSkb,liftSkb_run,SkbStore.freeTx,SkbStore.getTx,device,packet,
        invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      rw [Packets.freeTxSkb_run w a d id p device packet] at run
      cases run
      refine ⟨account.named_store ?_ ?_ ?_,?_⟩
      · simp [Origins.view,Packets.update,device]
      · simp [peersAt,Packets.update,device]
      · intro pid q found
        exact freeTx_peer_names device pid q (fun batch queued head =>
          detached pid q found batch queued id head member)
      · intro pid q found batch queued head first
        apply detached pid q _ batch queued head first
        simpa [peerAt,Packets.update,device] using found

theorem free_list_holders (items : List SkbId) (temporary : Credits.Ledger) :
    Hoare (Queues.TxDisposition.freeList items)
      (fun w => HolderAccount temporary w ∧ TxDetached items w)
      (fun _ w => HolderAccount temporary w) := by
  have walk (rest : List SkbId) (subset : ∀ id ∈ rest, id ∈ items) :
      Preserves (fun w => HolderAccount temporary w ∧ TxDetached items w)
        (Queues.TxDisposition.freeList rest) := by
    induction rest with
    | nil => exact preserves_pure ()
    | cons id rest ih =>
      rw [Queues.TxDisposition.freeList_cons]
      apply preserves_bind
      · apply (hoare_iff_run_ambient _ _ _).mpr
        intro w a result v b state run
        cases result
        exact state.1.free_tx state.2 (subset id (by simp)) a b run
      · intro _
        exact ih (fun id member => subset id (by simp [member]))
  exact hoare_consequence (walk items (fun _ h => h)) (fun _ h => h) (fun _ _ h => h.1)

end Leanux.Proofs.WG.RetirementSecurity
