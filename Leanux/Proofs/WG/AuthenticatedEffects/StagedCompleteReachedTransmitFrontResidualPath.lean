import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontResidualFrames

/-! Actual ordered overflow iterations, including the cut between queue
removal and charging. The entry ledger remains fixed until the completed
native overflow receipt settles precisely its removed initial segment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open TransmitSecurity Staged.Obligations CausalJournal CompleteCarrier
set_option maxHeartbeats 600000

inductive Yields (pid : PeerId) (w : WGWorld) (a : Ambient) : Nat → WGWorld → Ambient → Prop where
  | zero : Yields pid w a 0 w a
  | step (path : Yields pid w a n u c)
      (next : ((Staged.trimBody pid).run u).run c=.ok ((.yield (),v),b)) :
      Yields pid w a (n+1) v b

theorem Yields.literal (path : Yields pid w a n v b) :
    ((trimPrefix pid n).run w).run a=.ok ((.yield (),v),b) := by
  induction path with
  | zero => rfl
  | step path next ih =>
    rw [prefix_add]
    rw [MaterialOrigin.bind_ok_ambient]
    refine ⟨_,_,_,ih,?_⟩
    change ((trimPrefix pid 1).run _).run _=_
    unfold trimPrefix
    rw [MaterialOrigin.bind_ok_ambient]
    exact ⟨_,_,_,next,rfl⟩

theorem Yields.continuation (path : Yields pid w a n v b) (remaining : Nat) :
    ((trimPrefix pid (n+remaining)).run w).run a=
      ((trimPrefix pid remaining).run v).run b := by
  rw [prefix_add]
  simp only [StateT.run_bind,path.literal]
  rfl

theorem Yields.geometry (path : Yields pid w a n v b)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    n≤p.staged.length ∧ Staged.stagedAt v pid=some (p.internalId,p.staged.drop n) ∧
      Staged.dropped v=some (d.txDropped+n) ∧
      ∀ other, pid≠other → Staged.stagedAt v other=Staged.stagedAt w other := by
  have initial : Staged.Trimmed pid p.internalId p.staged d.txDropped (Staged.stagedAt w) w :=
    ⟨0,by omega,by simp [Staged.stagedAt,device,resident],by simp [Staged.dropped,device],fun _ _=>rfl⟩
  have kept : Staged.Trimmed pid p.internalId p.staged d.txDropped (Staged.stagedAt w) v ∧
      Staged.dropped v=some (d.txDropped+n) := by
    induction path with
    | zero => exact ⟨initial,by simp [Staged.dropped,device]⟩
    | @step index middle beforeClock endpoint afterClock path next ih =>
      refine ⟨(hoare_iff_run_ambient _ _ _).mp
        (Staged.trim_body pid p.internalId p.staged d.txDropped (Staged.stagedAt w)) _ _ _ _ _ ih.1 next,?_⟩
      obtain ⟨current,peer,atDevice,_,_,rfl,_⟩:=body_yield next
      have count : current.txDropped=d.txDropped+index := by
        simpa only [Staged.dropped,atDevice,Option.map_some,Option.some.injEq] using ih.2
      simpa only [count,Nat.add_assoc] using (charged_geometry (pid:=pid) (p:=peer) (d:=current) (w:=middle)).2
  obtain ⟨⟨removed,bound,queue,counter,others⟩,charged⟩:=kept
  have equal : removed=n := by
    have same:=Option.some.inj (counter.symm.trans charged)
    omega
  subst removed
  exact ⟨bound,queue,counter,others⟩

/-- A fixed actual range-loop position, not a checkpoint world chosen from
an unrelated receipt. Accounted is retained only at the native entry. -/
structure TrimCut (h : List Event) (ledger : Ledger) (debts : List AllocatedObligation.CleanupDebt)
    (locals : List RetirementSecurity.TxLocalBatch) (pid : PeerId)
    (w : WGWorld) (a : Ambient) (n : Nat) (v : WGWorld) (b : Ambient) : Prop where
  entry : Accounted h ledger debts locals w
  path : Yields pid w a n v b
  read : ∃ d p, w.dev=some d ∧ d.peers[pid]?=some p

/-- The untouched source suffix is retained for success and failure alike. -/
theorem TrimCut.continuation
    (cut : TrimCut h ledger debts locals pid w a n v b) :
    ∃ d p, w.dev=some d ∧ d.peers[pid]?=some p ∧ n≤p.staged.length ∧
      ((xmitTrim pid).run w).run a=
        (((trimPrefix pid (p.staged.length+1-n) >>= finish).run v).run b) := by
  obtain ⟨d,p,device,resident⟩:=cut.read
  have bound:=(cut.path.geometry device resident).1
  refine ⟨d,p,device,resident,bound,?_⟩
  have read : ((getPeer pid).run w).run a=.ok ((p,w),a) := by
    simp [getPeer,getDev,device,resident]
  have sum : p.staged.length+1=n+(p.staged.length+1-n) := by omega
  have rest:=cut.path.continuation (p.staged.length+1-n)
  rw [←sum] at rest
  calc
    ((xmitTrim pid).run w).run a =
        (((trimPrefix pid (p.staged.length+1) >>= finish).run w).run a) := by
      rw [trim_factor]
      simp only [StateT.run_bind,read]
      rfl
    _ = _ := by simp only [StateT.run_bind,rest]

/-- This is the next real drop before its counter write. The complete old
ledger remains an entry fact, with no fabricated post-mutation account. -/
theorem TrimCut.drop_cut (cut : TrimCut h ledger debts locals pid w a n v b)
    (device : v.dev=some d) (resident : d.peers[pid]?=some p)
    (excess : p.staged.length>MAX_STAGED_PACKETS) :
    ((do let (peer,accepted) ← gate pid
         if accepted then drop pid peer else pure () : WG.M Unit).run v).run b=
      .ok (((),droppedWorld pid p d v),clock b true) ∧
    (charge.run (droppedWorld pid p d v)).run (clock b true)=
      .ok (((),chargedWorld pid p d v),clock b true) ∧
    Yields pid w a (n+1) (chargedWorld pid p d v) (clock b true) := by
  refine ⟨?_,charge_run,cut.path.step ?_⟩
  · simp only [StateT.run_bind,gate_run device resident,decide_eq_true excess ]
    exact drop_run device
  · simp only [body_run device resident,ite_eq_left excess]

/-- Every requested source iteration is reached, or the actual earlier
false guard has terminated the finite loop. This requires no whole-run
success premise. -/
theorem visit (device : w.dev=some d) (resident : d.peers[pid]?=some p) (limit : Nat) :
    (∃ v b, Yields pid w a limit v b) ∨
    (∃ n v b c, n<limit ∧ Yields pid w a n v b ∧
      ((Staged.trimBody pid).run v).run b=.ok ((.done (),v),c)) := by
  induction limit with
  | zero => exact Or.inl ⟨w,a,.zero⟩
  | succ limit ih =>
    rcases ih with ⟨v,b,path⟩ | ⟨n,v,b,c,bound,path,done⟩
    · have queue:=(path.geometry device resident).2.1
      obtain ⟨current,atDevice⟩ : ∃ current, v.dev=some current := by
        cases found : v.dev with
        | none => simp [Staged.stagedAt,found] at queue
        | some current => exact ⟨current,rfl⟩
      obtain ⟨peer,atPeer⟩ : ∃ peer, current.peers[pid]?=some peer := by
        cases found : current.peers[pid]? with
        | none => simp [Staged.stagedAt,atDevice,found] at queue
        | some peer => exact ⟨peer,rfl⟩
      by_cases excess : peer.staged.length>MAX_STAGED_PACKETS
      · exact Or.inl ⟨chargedWorld pid peer current v,clock b true,path.step (by simp only [body_run atDevice atPeer,ite_eq_left excess])⟩
      · exact Or.inr ⟨limit,v,b,clock b false,by omega,path,
          by simp only [body_run atDevice atPeer,ite_eq_right excess]⟩
    · exact Or.inr ⟨n,v,b,c,by omega,path,done⟩

/-- At its first false guard the remaining native range exits. In particular
no invisible failed mutation is hidden behind the completed trim receipt. -/
theorem break_continuation (path : Yields pid w a n v b)
    (done : ((Staged.trimBody pid).run v).run b=.ok ((.done (),v),c)) (remaining : Nat) :
    ((trimPrefix pid (n+(remaining+1))).run w).run a=.ok ((.done (),v),c) := by
  rw [path.continuation]
  unfold trimPrefix
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨_,_,_,done,rfl⟩

theorem trim_total (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ∃ n v b c, n≤p.staged.length ∧ Yields pid w a n v b ∧
      ((Staged.trimBody pid).run v).run b=.ok ((.done (),v),c) ∧
      ((xmitTrim pid).run w).run a=.ok (((),v),c) := by
  rcases visit (a:=a) device resident (p.staged.length+1) with reached | exited
  · obtain ⟨v,b,path⟩:=reached
    have impossible:=(path.geometry device resident).1
    omega
  · obtain ⟨n,v,b,c,bound,path,done⟩:=exited
    refine ⟨n,v,b,c,by omega,path,done,?_⟩
    have read : ((getPeer pid).run w).run a=.ok ((p,w),a) := by simp [getPeer,getDev,device,resident]
    have sum : p.staged.length+1=n+((p.staged.length-n)+1) := by omega
    have result:=break_continuation path done (p.staged.length-n)
    rw [←sum] at result
    rw [trim_factor,MaterialOrigin.bind_ok_ambient]
    exact ⟨_,_,_,read,by rw [MaterialOrigin.bind_ok_ambient]; exact ⟨_,_,_,result,rfl⟩⟩

/-- A failed overflow is the original initial peer read failing. After that
read succeeds all loop mutation positions and the false exit are total. -/
theorem trim_failed (run : ((xmitTrim pid).run w).run a=.error stop) :
    ((getPeer pid).run w).run a=.error stop := by
  cases read : ((getPeer pid).run w).run a with
  | error reason =>
    rw [trim_factor] at run
    simp only [StateT.run_bind,read] at run
    cases run
    rfl
  | ok out =>
    obtain ⟨⟨peer,v⟩,b⟩:=out
    obtain ⟨rfl,rfl,d,device,resident⟩:=Origins.getPeer_return pid w v peer a b read
    obtain ⟨_,_,_,_,_,_,_,normal⟩:=trim_total (a:=b) device resident
    rw [normal] at run
    cases run

/-- Removed and retained positions still refer to the same incoming ticket
list during the silent interval. The removed tickets have not been settled
or forgotten merely because their packet cells left the resident queue. -/
theorem TrimCut.tickets (cut : TrimCut h ledger debts locals pid w a n v b)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    Staged.Origins.Aligned (Staged.Origins.Born h d.ifindex pid p.internalId)
      ((pendingAt (.staged d.ifindex pid p.internalId) ledger).take n) (p.staged.take n) ∧
    Staged.Origins.Aligned (Staged.Origins.Born h d.ifindex pid p.internalId)
      ((pendingAt (.staged d.ifindex pid p.internalId) ledger).drop n) (p.staged.drop n) ∧
    (∀ ticket ∈ (pendingAt (.staged d.ifindex pid p.internalId) ledger).take n,
      (ticket,Status.pending (.staged d.ifindex pid p.internalId))∈ledger) ∧
    Staged.stagedAt v pid=some (p.internalId,p.staged.drop n) := by
  have aligned:=cut.entry.entry.core.queues d.ifindex pid p.internalId
  simp only [stagedPackets,Packets.epoch,device,Option.map_some,ite_true,
    Staged.stagedAt,Option.bind_some,resident,Option.map_some] at aligned
  refine ⟨HandshakeSecurity.StagedConservation.aligned_take aligned n,
    HandshakeSecurity.StagedConservation.aligned_drop aligned n,?_,(cut.path.geometry device resident).2.1⟩
  intro ticket member
  exact mem_pendingAt.mp (List.mem_of_mem_take member)

/-- The original initial range-bound read occurs before this actual prefix. -/
theorem TrimCut.literal (cut : TrimCut h ledger debts locals pid w a n v b) :
    ((trimTo pid n).run w).run a=.ok ((.yield (),v),b) := by
  obtain ⟨d,p,device,resident⟩:=cut.read
  unfold trimTo
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,w,a,by simp [getPeer,getDev,device,resident],cut.path.literal⟩

/-- A pending counter charge is reached by the fixed initial read, exactly
n yielded iterations, then the real guard and queue write. -/
theorem TrimCut.drop_literal (cut : TrimCut h ledger debts locals pid w a n v b)
    (device : v.dev=some d) (resident : d.peers[pid]?=some p)
    (excess : p.staged.length>MAX_STAGED_PACKETS) :
    ((dropTo pid n).run w).run a=
      .ok ((some p,droppedWorld pid p d v),clock b true) := by
  unfold dropTo
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨_,_,_,cut.literal,?_⟩
  rw [MaterialOrigin.bind_ok_ambient]
  refine ⟨(p,true),v,clock b true,by simpa only [decide_eq_true excess] using gate_run device resident,?_⟩
  dsimp only
  simp only [ite_true]
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨_,_,_,drop_run device,rfl⟩

/-- At the drop-before-charge cut, the ordered removed prefix has n+1
positions but the counter still records only n charges. Its tickets remain
pending in the same entry ledger until the actual overflow receipt. -/
theorem TrimCut.pending_drop {initial : Device} {old : Peer} (cut : TrimCut h ledger debts locals pid w a n v b)
    (original : w.dev=some initial) (oldPeer : initial.peers[pid]?=some old)
    (device : v.dev=some d) (resident : d.peers[pid]?=some p)
    (excess : p.staged.length>MAX_STAGED_PACKETS) :
    Staged.Origins.Aligned (Staged.Origins.Born h initial.ifindex pid old.internalId)
      ((pendingAt (.staged initial.ifindex pid old.internalId) ledger).take (n+1)) (old.staged.take (n+1)) ∧
    (∀ ticket ∈ (pendingAt (.staged initial.ifindex pid old.internalId) ledger).take (n+1),
      (ticket,Status.pending (.staged initial.ifindex pid old.internalId))∈ledger) ∧
    Staged.stagedAt (droppedWorld pid p d v) pid=some (old.internalId,old.staged.drop (n+1)) ∧
    Staged.dropped (droppedWorld pid p d v)=some (initial.txDropped+n) := by
  have next : TrimCut h ledger debts locals pid w a (n+1) (chargedWorld pid p d v) (clock b true) :=
    ⟨cut.entry,cut.path.step (by simp only [body_run device resident,ite_eq_left excess]),cut.read⟩
  have facts:=next.tickets original oldPeer
  refine ⟨facts.1,facts.2.2.1,?_,?_⟩
  · have same : Staged.stagedAt (droppedWorld pid p d v) pid=
        Staged.stagedAt (chargedWorld pid p d v) pid := by
      simp only [droppedWorld,chargedWorld,Staged.stagedAt,Option.bind_some,
        Std.TreeMap.getElem?_insert_self,Option.map_some]
    exact same.trans facts.2.2.2
  · exact (drop_geometry device).2.trans (cut.path.geometry original oldPeer).2.2.1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.Residual
