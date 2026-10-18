import Leanux.Proofs.WG.RetirementSecurity.HolderStoreFrames
import Leanux.Proofs.WG.RetirementSecurity.HolderReassembly
import Leanux.Proofs.WG.RetirementSecurity.WorkerRetirement
import Leanux.Proofs.WG.RetirementSecurity.TxFreeHolders

/-! Peer release is a separate ownership step from key release. A nonfinal
peer put leaves all key holders in place. A final peer put needs empty key
slots as a caller premise; the native normal-return path itself checks that
both packet queues are empty. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem peer_erase_list (peers : Std.TreeMap PeerId Peer compare) (pid : PeerId) :
    (peers.erase pid).toList = peers.toList.filter (fun pair => decide (¬ (pid == pair.1))) := by
  have same : (peers.erase pid).Equiv (peers.filter fun other _ => decide (¬ (pid == other))) := by
    apply Std.TreeMap.Equiv.of_forall_constGet?_eq
    intro other
    rw [Std.TreeMap.getElem?_erase,Std.TreeMap.getElem?_filter']
    by_cases eq : pid = other
    · subst other
      simp
    · cases peers[other]? <;> simp [eq,Option.filter]
  exact same.toList_eq.trans Std.TreeMap.toList_filter

def erasePeer (w : WGWorld) (d : Device) (pid : PeerId) : WGWorld :=
  {w with dev := some {d with peers := d.peers.erase pid}}

theorem HolderAccount.erase_peer (account : HolderAccount temporary w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (empty : peerLoans w pid p = some []) : HolderAccount temporary (erasePeer w d pid) := by
  obtain ⟨entry⟩ := account.split_peer (show peerAt w pid = some p by simp [peerAt,device,found])
  have sameDevice : entry.device = d := Option.some.inj (entry.hasDevice.symm.trans device)
  have noLoans : entry.loans = [] := Option.some.inj (entry.named.symm.trans empty)
  have names (peer : PeerId) (q : Peer) :
      peerLoans (erasePeer w d pid) peer q = peerLoans w peer q := by
    have named (holder : KeyHolder) : nameLoan (erasePeer w d pid) holder = nameLoan w holder := by
      funext key
      simp [nameLoan,keyAt,erasePeer,device]
    simp only [peerLoans,named]
    simp [erasePeer,device]
  refine ⟨entry.rest.flatten,?_,?_⟩
  · have rest := entry.restRun
    rw [sameDevice] at rest
    change (do
      let groups ← (d.peers.erase pid).toList.mapM
        (fun (peer,q) => peerLoans (erasePeer w d pid) peer q)
      pure groups.flatten) = _
    simp only [peer_erase_list,names,rest]
    rfl
  · have exact := entry.credits
    rw [noLoans] at exact
    intro allocation
    simpa [Credits.balance,keyAt,erasePeer,device] using exact allocation

theorem HolderAccount.peer_fields (account : HolderAccount temporary w)
    (device : w.dev = some d) (found : d.peers[pid]? = some p)
    (same : slotFields q = slotFields p ∧ q.txQueue = p.txQueue ∧ q.rxQueue = p.rxQueue) :
    HolderAccount temporary (replacePeer w d pid q) := by
  have present : peerAt w pid = some p := by simp [peerAt,device,found]
  obtain ⟨loans,named⟩ := account.peer_loans present
  have next : q.keypairNext = p.keypairNext := congrArg Prod.fst same.1
  have previous : q.keypairPrevious = p.keypairPrevious := congrArg (fun fields => fields.2.1) same.1
  have current : q.keypairCurrent = p.keypairCurrent := congrArg (fun fields => fields.2.2) same.1
  have named' : peerLoans w pid q = some loans := by
    simpa only [peerLoans,next,previous,current,same.2.1,same.2.2] using named
  exact account.replace_peer device found named named' (List.Perm.refl _)

def PeerReleaseReady (pid : PeerId) (w : WGWorld) : Prop :=
  ∀ p, peerAt w pid = some p → p.refcount = 1 →
    p.keypairNext = none ∧ p.keypairPrevious = none ∧ p.keypairCurrent = none

theorem HolderAccount.peer_put (account : HolderAccount temporary w)
    (ready : PeerReleaseReady pid w) (a b : Ambient)
    (run : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) :
    HolderAccount temporary v := by
  cases device : w.dev with
  | none =>
    simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,
      invariant,AmbientM.invariant] at run
    cases run
  | some d =>
    cases stored : d.peers[pid]? with
    | none =>
      simp [peerPut,branch,AmbientM.branch,requireNotPending,getPeer,getDev,device,stored,
        invariant,AmbientM.invariant] at run
      cases run
    | some p =>
      have lift (action : IndexM Unit) : (liftM action : WG.M Unit) = liftIndex action := rfl
      by_cases positive : 0 < p.refcount
      · have nonzero : p.refcount ≠ 0 := by omega
        by_cases final : p.refcount = 1
        · have slots := ready p (by simp [peerAt,device,stored]) final
          have queueEmpty : (p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty ||
              p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty) = false := by
            by_cases no : (p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty ||
                p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty) = false
            · exact no
            have yes : (p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty ||
                p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty) = true := by
              cases value : p.txQueue.peeked.isSome || !p.txQueue.items.isEmpty ||
                p.rxQueue.peeked.isSome || !p.rxQueue.items.isEmpty <;> simp_all
            simp at yes
            simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
              refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
              lift,liftIndex_run,device,stored,final,yes,
              CounterWindow.branch_run,CounterWindow.branchCmp_run,
              StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
              CounterWindow.except_ok_bind,CounterWindow.except_pure,
              invariant,AmbientM.invariant] at run
            split at run <;> contradiction
          have queues : p.txQueue.all = [] ∧ p.rxQueue.all = [] := by
            simpa [PrevQueue.all,Bool.or_eq_false_iff,and_assoc] using queueEmpty
          have empty : peerLoans w pid p = some [] := by
            simp [peerLoans_eq,slots.1,slots.2.1,slots.2.2,queues.1,queues.2]
          have removed := account.erase_peer device stored empty
          simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,indexRemove_eq,indexUnhash,
            lift,liftIndex_run,retirePeerUnits,modifyAmbient,
            CounterWindow.branch_run,CounterWindow.branchCmp_run,
            device,stored,final,
            StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
            CounterWindow.except_ok_bind,CounterWindow.except_pure,
            invariant,AmbientM.invariant,unsupported,AmbientM.unsupported] at run
          repeat' first | split at run | contradiction
          all_goals rcases run with ⟨rfl,rfl⟩
          all_goals apply removed.named_lists
          all_goals solve
            | simp [Origins.view,erasePeer]
            | (simp only [erasePeer,Option.map_some,Option.some.injEq];
               apply Std.TreeMap.Equiv.toList_eq;
               apply Std.TreeMap.Equiv.of_forall_constGet?_eq;
               intro other;
               by_cases eq : pid = other <;>
                 simp [Std.TreeMap.getElem?_erase,Std.TreeMap.getElem?_insert,eq])
            | (intro other q _; rfl)
        · have retained := account.peer_fields device stored
            (q := {p with refcount := p.refcount - 1}) ⟨rfl,rfl,rfl⟩
          simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
            refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
            CounterWindow.branchCmp_run,device,stored,positive,nonzero,final,
            StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
            CounterWindow.except_ok_bind,CounterWindow.except_pure,
            unsupported,AmbientM.unsupported,invariant,AmbientM.invariant] at run
          repeat' first | split at run | contradiction
          all_goals rcases run with ⟨rfl,rfl⟩
          all_goals exact retained
      · have zero : p.refcount = 0 := by omega
        simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,
          refcountDecAndTest,branch,branchCmp,CounterWindow.branch_run,
          CounterWindow.branchCmp_run,device,stored,zero,
          StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
          CounterWindow.except_ok_bind,CounterWindow.except_pure,
          unsupported,AmbientM.unsupported] at run
        cases run

end Leanux.Proofs.WG.RetirementSecurity
