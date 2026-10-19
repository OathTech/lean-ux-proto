import Leanux.Proofs.WG.TransmitSecurity.StagedTrim
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalSource

/-! Overflow trimming has no partial stopped execution. Once its first peer
read succeeds, the finite native loop retains that peer and must complete. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Trim
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes
open TransmitSecurity.Staged

theorem body_total (pid : PeerId) (w : WGWorld) (a : Ambient) (d : Device) (p : Peer)
    (device : w.dev = some d) (resident : d.peers[pid]? = some p) :
    ∃ result v b next peer, ((trimBody pid).run w).run a = .ok ((result,v),b) ∧
      v.dev = some next ∧ next.peers[pid]? = some peer := by
  by_cases excess : p.staged.length > MAX_STAGED_PACKETS
  · let peer := {p with staged := p.staged.drop 1}
    let next := {d with peers := d.peers.insert pid peer,txDropped := d.txDropped+1}
    let v := {w with dev := some next}
    refine ⟨.yield (),v,CounterWindow.record a .xmitStagedTrimIter true,next,peer,?_,rfl,?_⟩
    · simp [trimBody,getPeer,getDev,device,resident,branch,AmbientM.branch,excess,
        setPeer,modifyDev,v,next,peer,CounterWindow.record]
    · simp [next]
  · refine ⟨.done (),w,CounterWindow.record a .xmitStagedTrimIter false,d,p,?_,device,resident⟩
    simp [trimBody,getPeer,getDev,device,resident,branch,AmbientM.branch,excess,CounterWindow.record]

theorem loop_total (indices : List Nat) (pid : PeerId) (w : WGWorld) (a : Ambient)
    (d : Device) (p : Peer) (device : w.dev = some d) (resident : d.peers[pid]? = some p) :
    ∃ v b next peer,
      ((forIn indices () (fun _ _ => trimBody pid)).run w).run a = .ok (((),v),b) ∧
      v.dev = some next ∧ next.peers[pid]? = some peer := by
  induction indices generalizing w a d p with
  | nil => exact ⟨w,a,d,p,rfl,device,resident⟩
  | cons index indices ih =>
    obtain ⟨result,v,b,next,peer,run,device',resident'⟩ := body_total pid w a d p device resident
    rw [List.forIn_cons]
    cases result with
    | done result =>
      cases result
      exact ⟨v,b,next,peer,by simp only [StateT.run_bind,run,CounterWindow.except_ok_bind]; rfl,device',resident'⟩
    | yield result =>
      cases result
      obtain ⟨z,c,last,final,tail,device'',resident''⟩ := ih v b next peer device' resident'
      exact ⟨z,c,last,final,by simpa only [StateT.run_bind,run,CounterWindow.except_ok_bind] using tail,device'',resident''⟩

/-- A resident peer makes the complete original overflow pass total; no
prefix of dropped packets can be hidden by a later Stop in this loop. -/
theorem total (pid : PeerId) (w : WGWorld) (a : Ambient) (d : Device) (p : Peer)
    (device : w.dev = some d) (resident : d.peers[pid]? = some p) :
    ∃ v b, ((xmitTrim pid).run w).run a = .ok (((),v),b) := by
  unfold xmitTrim
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  have read : ((getPeer pid).run w).run a = .ok ((p,w),a) := by
    simp [getPeer,getDev,device,resident]
  simp only [StateT.run_bind,read,CounterWindow.except_ok_bind]
  obtain ⟨v,b,next,peer,run,_,_⟩ := loop_total
    (List.range' 0 ([0:p.staged.length+1] : Std.Legacy.Range).size 1) pid w a d p device resident
  refine ⟨v,b,?_⟩
  change (((forIn _ () (fun _ _ => trimBody pid)).run w).run a >>= fun out => pure (((),out.1.2),out.2)) = _
  rw [run]
  rfl

/-- Every stopped overflow pass is precisely its first peer read, before any
branch record, queue write or dropped-counter increment. -/
theorem stopped_first (pid : PeerId) (w : WGWorld) (a : Ambient) (stop : Stop)
    (run : ((xmitTrim pid).run w).run a = .error stop) :
    ((getPeer pid).run w).run a = .error stop := by
  cases read : ((getPeer pid).run w).run a with
  | error err =>
    simp only [xmitTrim,StateT.run_bind,read] at run
    change Except.error err = Except.error stop at run
    cases run
    rfl
  | ok out =>
    obtain ⟨⟨p,v⟩,b⟩ := out
    obtain ⟨rfl,rfl,d,device,resident⟩ := Origins.getPeer_return pid w v p a b read
    obtain ⟨z,c,normal⟩ := total pid _ _ d p device resident
    rw [normal] at run
    cases run

/-- The whole-pass overflow receipt is emitted on every resident-peer path,
before any later splice or staging suffix can stop. -/
theorem observed_total (pid : PeerId) (w : WGWorld) (a : Ambient) (d : Device) (p : Peer)
    (device : w.dev = some d) (resident : d.peers[pid]? = some p)
    (h : List StagedDisposal.Event) :
    ∃ v b, runWGPrefix (StagedDisposal.overflowObserved pid) w a h =
      (.ok (((),v),b),h ++ [.overflow pid ⟨(),w,v,a,b⟩]) := by
  obtain ⟨v,b,run⟩ := total pid w a d p device resident
  refine ⟨v,b,?_⟩
  rw [StagedDisposal.overflowObserved,runWGPrefix_receiptWGObserved,runWGPrefix_lift,run]

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Trim
