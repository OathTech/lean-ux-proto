import Leanux.Proofs.WG.RetirementSecurity.TxDisposeHolders
import Leanux.Proofs.WG.RetirementSecurity.SlotProjection
import Leanux.Proofs.WG.Queues.TxItemSeparation

/-! The native staged allocator preserves all existing key holders and
derives separation of the new batch from every durable batch head. Its only
extra input is campaign 1's packet allocation bound, not an assumed fresh
packet list or a claimed credit obtained from the peer budget. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem HolderAccount.tx_head (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (queued : batch ∈ p.txQueue.all) :
    ∃ head packet, batch.head? = some head ∧ Queues.TxDisposition.txPackets w head = some packet := by
  obtain ⟨loans,named⟩ := account.peer_loans found
  obtain ⟨parts⟩ := peer_parts named
  obtain ⟨loan,named,_⟩ := mapM_member _ _ _ parts.txRun queued
  unfold transmitLoan at named
  cases head : batch.head? with
  | none => simp [head] at named
  | some id =>
    cases packet : Queues.TxDisposition.txPackets w id with
    | none => simp [head,show w.dev.bind (fun d => d.txSkbs[id]?) = none from packet] at named
    | some pkt => exact ⟨id,pkt,rfl,packet⟩

def allocationPerimeter (w : WGWorld) :=
  (Origins.view w,peersAt w,fun id : SkbId => w.dev.bind fun d => d.rxSkbs[id]?)

theorem allocate_perimeter (packets : List DataPacket) :
    SameView allocationPerimeter (packets.mapM newTxSkb) := by
  intro initial
  apply mapM_view_spec id (fun w : WGWorld => allocationPerimeter w = initial)
  intro packet
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases device : w.dev with
  | none => simp [newTxSkb,liftSkb_run,device] at run
  | some d =>
    rw [Packets.newTxSkb_run w a d packet device] at run
    cases run
    simpa [allocationPerimeter,Origins.view,peersAt,Packets.update,device] using before

theorem HolderAccount.allocate_tx (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (packets : List DataPacket) (a b : Ambient)
    (run : ((packets.mapM newTxSkb).run w).run a = .ok ((items,v),b)) :
    HolderAccount temporary v ∧ TxDetached items v := by
  have perimeter := (ProjectedAction.iff_run_ambient _ _ _).mp
    (allocate_perimeter packets) w a items v b run
  have keys : Origins.view v = Origins.view w := congrArg (fun shape => shape.1) perimeter
  have peers : peersAt v = peersAt w := congrArg (fun shape => shape.2.1) perimeter
  have rx : (fun id : SkbId => v.dev.bind fun d => d.rxSkbs[id]?) =
      (fun id : SkbId => w.dev.bind fun d => d.rxSkbs[id]?) := congrArg (fun shape => shape.2.2) perimeter
  have names (holder : KeyHolder) : nameLoan v holder = nameLoan w holder := by
    funext key
    have same : keyAt v key = keyAt w key := by
      simpa [Origins.view,keyAt,Option.bind_map,Function.comp_def] using
        congrArg (fun shape => shape.bind fun fields => fields.2 key) keys
    simp only [nameLoan,same]
  have rxNames (pid : PeerId) : receiveLoan v pid = receiveLoan w pid := by
    funext id
    simp only [receiveLoan,names,congrFun rx id]
  refine ⟨account.named_store keys peers ?_,?_⟩
  · intro pid p found
    have txNames : p.txQueue.all.mapM (transmitLoan v pid) =
        p.txQueue.all.mapM (transmitLoan w pid) := by
      apply mapM_congr_on
      intro batch queued
      obtain ⟨head,packet,first,resident⟩ := account.tx_head found queued
      have retained := (Queues.TxDisposition.ItemSeparation.allocate_resident bounded resident run).2
      simp only [transmitLoan,names]
      simp [first,show v.dev.bind (fun d => d.txSkbs[head]?) = some packet from retained,
        show w.dev.bind (fun d => d.txSkbs[head]?) = some packet from resident]
    simp only [peerLoans_eq,names,rxNames,txNames]
  · apply TxDetached.peers (w := w) (same := peers)
    intro pid p found batch queued head first
    obtain ⟨selected,packet,headSame,resident⟩ := account.tx_head found queued
    have eq : selected = head := Option.some.inj (headSame.symm.trans first)
    subst selected
    exact (Queues.TxDisposition.ItemSeparation.allocate_resident bounded resident run).1

end Leanux.Proofs.WG.RetirementSecurity
