import Leanux.Proofs.WG.RetirementSecurity.TxWorkObligationStep

/-! Exact transfers between the native pending TX queue and an explicit
active actor. These do not regard dispatch as dropping a packet obligation. -/
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem Obligations.actor_cover (before : Obligations crypt tx w)
    (coverage : ∀pid,pid∈queued w++tx→pid∈queued w++next) : Obligations crypt next w :=
  ⟨before.batches,fun pid p found batch first packet queue head resident terminal=>
    coverage pid (before.heads pid p found batch first packet queue head resident terminal)⟩

theorem Obligations.crypt_cover (before : Obligations crypt tx w)
    (coverage : ∀batch,batch∈txCryptItems w++crypt→batch∈txCryptItems w++next) :
    Obligations next tx w := by
  refine ⟨?_,before.heads⟩
  intro pid p found batch member
  obtain ⟨first,packet,head,resident,pending⟩:=before.batches pid p found batch member
  exact ⟨first,packet,head,resident,fun uncrypted=>coverage batch (pending uncrypted)⟩

/-- Removing a queued worker transfers its outstanding head obligation to
that actual actor; it does not make the queue obligation disappear. -/
theorem Obligations.dispatch (before : Obligations crypt tx w) (pid : PeerId) (a b : Ambient)
    (run : ((modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}).run w).run a=
      .ok (((),v),b)) : Obligations crypt (pid::tx) v := by
  cases run
  have cells:TxDisposition.txPackets
      {w with dev:=w.dev.map fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}}=
      TxDisposition.txPackets w := by funext id; simp [TxDisposition.txPackets,Option.bind_map,Function.comp_def]
  have peers:peerAt {w with dev:=w.dev.map fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}}=peerAt w := by funext id; simp [peerAt,Option.bind_map,Function.comp_def]
  have ring:txCryptItems {w with dev:=w.dev.map fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}}=txCryptItems w := by simp [txCryptItems,Option.map_map,Function.comp_def]
  have work:queued {w with dev:=w.dev.map fun d=>{d with txWorkQueue:=d.txWorkQueue.erase pid}}=
      (queued w).erase pid := by cases device:w.dev <;> simp [queued,device]
  constructor
  · intro q p found batch member
    obtain ⟨first,packet,head,resident,pending⟩:=before.batches q p (peers ▸ found) batch member
    exact ⟨first,packet,head,cells.symm ▸ resident,by simpa only [ring] using pending⟩
  · intro q p found batch first packet queue head resident terminal
    have pending:=before.heads q p (peers ▸ found) batch first packet queue head
      (cells ▸ resident) terminal
    rw [work]
    by_cases same:q=pid
    · subst q
      simp
    · rcases List.mem_append.mp pending with pending | active
      · exact List.mem_append_left _ ((List.mem_erase_of_ne same).mpr pending)
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ active)

/-- Requeueing an active actor can move the obligation back to the actual
pending list, including when a second occurrence was already pending. -/
theorem Obligations.requeue (before : Obligations crypt (pid::tx) w) (a b : Ambient)
    (run : ((modifyDev fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]}).run w).run a=
      .ok (((),v),b)) : Obligations crypt tx v := by
  cases device:w.dev with
  | none=>
    cases run
    constructor
    · intro q p found
      simp [peerAt,device] at found
    · intro q p found
      simp [peerAt,device] at found
  | some d=>
    cases run
    have cells:TxDisposition.txPackets
        {w with dev:=w.dev.map fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]}}=
        TxDisposition.txPackets w := by funext id; simp [TxDisposition.txPackets,Option.bind_map,Function.comp_def]
    have peers:peerAt {w with dev:=w.dev.map fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]}}=peerAt w := by funext id; simp [peerAt,Option.bind_map,Function.comp_def]
    have ring:txCryptItems {w with dev:=w.dev.map fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]}}=txCryptItems w := by simp [txCryptItems,Option.map_map,Function.comp_def]
    have work:queued {w with dev:=w.dev.map fun d=>{d with txWorkQueue:=d.txWorkQueue++[pid]}}=
        queued w++[pid] := by simp [queued,device]
    constructor
    · intro q p found batch member
      obtain ⟨first,packet,head,resident,pending⟩:=before.batches q p (peers ▸ found) batch member
      exact ⟨first,packet,head,cells.symm ▸ resident,by simpa only [ring] using pending⟩
    · intro q p found batch first packet queue head resident terminal
      have pending:=before.heads q p (peers ▸ found) batch first packet queue head
        (cells ▸ resident) terminal
      simpa only [work,List.mem_append,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,or_assoc] using pending

end Leanux.Proofs.WG.RetirementSecurity.TxWork
