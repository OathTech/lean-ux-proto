import Leanux.Proofs.WG.RetirementSecurity.RxHolderTransfer
import Leanux.Proofs.WG.RetirementSecurity.TxFreeHolders

/-! RX cells do not create a second key reference beside their peer-queue
occurrence. Allocation derives its detached status from actual resident
holders and campaign 1's initialized packet frontier; freeing requires that
the queue occurrence has already been selected or rejected. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

def RxDetached (id : SkbId) (w : WGWorld) : Prop :=
  ∀ pid p, peerAt w pid = some p → id ∉ p.rxQueue.all

theorem mapM_defined (f : α → Option β) (xs : List α) (ys : List β)
    (run : xs.mapM f = some ys) (member : x ∈ xs) : ∃ y, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons head tail ih =>
    cases first : f head with
    | none => simp [List.mapM_cons,first] at run
    | some y =>
      cases rest : tail.mapM f with
      | none => simp [List.mapM_cons,first,rest] at run
      | some remaining =>
        rcases List.mem_cons.mp member with same | inside
        · subst head; exact ⟨y,first⟩
        · exact ih remaining rest inside

theorem HolderAccount.rx_packet {id : SkbId} (account : HolderAccount temporary w)
    (found : peerAt w pid = some p) (member : id ∈ p.rxQueue.all) :
    ∃ packet, (w.dev.bind fun d => d.rxSkbs[id]?) = some packet := by
  obtain ⟨loans,named⟩ := account.peer_loans found
  obtain ⟨parts⟩ := peer_parts named
  obtain ⟨loan,namedPacket⟩ := mapM_defined _ _ _ parts.rxRun member
  cases packet : w.dev.bind (fun d => d.rxSkbs[id]?) with
  | none => simp [receiveLoan,packet] at namedPacket
  | some pkt => exact ⟨pkt,rfl⟩

theorem rx_change_peer_names {id : SkbId} (device : w.dev = some d)
    (store : Std.TreeMap SkbId RxPacket) (same : ∀ other, other ≠ id → store[other]? = d.rxSkbs[other]?)
    (pid : PeerId) (p : Peer) (absent : id ∉ p.rxQueue.all) :
    peerLoans (Packets.update w (fun current => {current with rxSkbs := store})) pid p =
      peerLoans w pid p := by
  have names (holder : KeyHolder) :
      nameLoan (Packets.update w (fun current => {current with rxSkbs := store})) holder =
        nameLoan w holder := by
    funext key
    simp [nameLoan,keyAt,Packets.update,device]
  have tx : transmitLoan (Packets.update w (fun current => {current with rxSkbs := store})) pid =
      transmitLoan w pid := by
    funext batch
    simp only [transmitLoan,names]
    simp [Packets.update,device]
  have rx : p.rxQueue.all.mapM
      (receiveLoan (Packets.update w (fun current => {current with rxSkbs := store})) pid) =
      p.rxQueue.all.mapM (receiveLoan w pid) := by
    apply mapM_congr_on
    intro other member
    have different : other ≠ id := by intro eq; subst other; exact absent member
    simp only [receiveLoan,names]
    simp [Packets.update,device,same other different]
  simp only [peerLoans_eq,names,tx,rx]

theorem HolderAccount.rx_change {id : SkbId} (account : HolderAccount temporary w)
    (device : w.dev = some d) (detached : RxDetached id w)
    (store : Std.TreeMap SkbId RxPacket) (same : ∀ other, other ≠ id → store[other]? = d.rxSkbs[other]?) :
    HolderAccount temporary (Packets.update w (fun current => {current with rxSkbs := store})) := by
  apply account.named_store
  · simp [Origins.view,Packets.update,device]
  · simp [peersAt,Packets.update,device]
  · intro pid p found
    exact rx_change_peer_names device store same pid p (detached pid p found)

theorem HolderAccount.free_rx {id : SkbId} (account : HolderAccount temporary w)
    (detached : RxDetached id w) (a b : Ambient)
    (run : ((freeRxSkb id).run w).run a = .ok (((),v),b)) : HolderAccount temporary v := by
  cases device : w.dev with
  | none => simp [freeRxSkb,liftSkb_run,device] at run
  | some d =>
    cases packet : d.rxSkbs[id]? with
    | none =>
      simp [freeRxSkb,liftSkb_run,SkbStore.freeRx,SkbStore.getRx,device,packet,
        invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      rw [Packets.freeRxSkb_run w a d id p device packet] at run
      cases run
      simpa only [Packets.update,device,Option.map_some] using
        account.rx_change device detached (d.rxSkbs.erase id)
          (fun other different => by simp [Std.TreeMap.getElem?_erase,Ne.symm different])

theorem setRx_holderStore (id : SkbId) (f : RxPacket → RxPacket)
    (key : ∀ p, (f p).keypair = p.keypair) : SameView holderStore (setRxSkb id f) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  cases result
  cases device : w.dev with
  | none => simp [setRxSkb,liftSkb_run,device] at run
  | some d =>
    cases packet : d.rxSkbs[id]? with
    | none =>
      simp [setRxSkb,liftSkb_run,SkbStore.setRx,SkbStore.getRx,device,packet,
        invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      rw [Packets.setRxSkb_run w a d id p f device packet] at run
      cases run
      apply Prod.ext
      · simp [holderStore,Origins.view,Packets.update,device]
      · apply Prod.ext
        · simp [holderStore,peersAt,Packets.update,device]
        · apply Prod.ext
          · simp [holderStore,packetKeyWords,Packets.update,device]
          · funext other
            by_cases eq : id = other
            · subst other
              simp [holderStore,packetKeyWords,Packets.update,device,packet,key]
            · simp [holderStore,packetKeyWords,Packets.update,device,
                Std.TreeMap.getElem?_insert,eq]

theorem HolderAccount.rx_frontier (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (device : w.dev = some d) : RxDetached d.nextSkb w := by
  intro pid p found member
  obtain ⟨packet,resident⟩ := account.rx_packet found member
  have slot : (Packets.snapshot w).slots (.inr d.nextSkb) = some (d.nextSkb + 1) := by
    simpa [Packets.snapshot,Packets.deviceStore,device] using
      congrArg (Option.map fun _ => d.nextSkb + 1) resident
  have bound := bounded (.inr d.nextSkb) (d.nextSkb + 1) slot
  have impossible : d.nextSkb + 1 ≤ d.nextSkb := by
    simpa only [Packets.snapshot,Packets.deviceStore,device] using bound
  exact Nat.not_succ_le_self _ impossible

theorem HolderAccount.allocate_rx {id : SkbId} (account : HolderAccount temporary w)
    (bounded : Packets.Inv w) (packet : RxPacket) (a b : Ambient)
    (run : ((newRxSkb packet).run w).run a = .ok ((id,v),b)) :
    HolderAccount temporary v ∧ RxDetached id v ∧
      (v.dev.bind fun d => d.rxSkbs[id]?) = some packet := by
  cases device : w.dev with
  | none => simp [newRxSkb,liftSkb_run,device] at run
  | some d =>
    rw [Packets.newRxSkb_run w a d packet device] at run
    cases run
    have detached := account.rx_frontier bounded device
    have updated := account.rx_change device detached (d.rxSkbs.insert d.nextSkb packet)
      (fun other different => by simp [Std.TreeMap.getElem?_insert,Ne.symm different])
    refine ⟨updated.store ?_,?_,?_⟩
    · simp [holderStore,Origins.view,peersAt,packetKeyWords,Packets.update,device]
    · intro pid p found
      exact detached pid p (by simpa [peerAt,Packets.update,device] using found)
    · simp [Packets.update,device]

end Leanux.Proofs.WG.RetirementSecurity
