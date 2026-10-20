import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontResidualReceipt

/-! Source-only positions in the original finite overflow loop. The initial
peer read fixes the loop bound; yielded iterations, the guard and the two
writes retain their actual worlds and remaining source. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.TrimPoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes TransmitSecurity
open Residual

theorem loop_remaining (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (path : Yields pid w a n v b) :
    ((xmitTrim pid).run w).run a=
      (((trimPrefix pid (p.staged.length+1-n) >>= finish).run v).run b) := by
  have bound:=(path.geometry device resident).1
  have read : ((getPeer pid).run w).run a=.ok ((p,w),a) := by
    simp [getPeer,getDev,device,resident]
  have sum : p.staged.length+1=n+(p.staged.length+1-n) := by omega
  have continued:=path.continuation (p.staged.length+1-n)
  rw [←sum] at continued
  rw [trim_factor]
  simp only [StateT.run_bind,read]
  change (((trimPrefix pid (p.staged.length+1) >>= finish).run w).run a)=_
  simp only [StateT.run_bind,continued]

def afterGuard (pid : PeerId) (peer : Peer) (excess : Bool) (remaining : Nat) : WG.M Unit := do
  if excess then
    drop pid peer
    charge
    let _ ← trimPrefix pid remaining
    pure ()
  else pure ()

theorem guarded_remaining (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (path : Yields pid w a n v b)
    (current : v.dev=some next) (peer : next.peers[pid]?=some q) :
    ((xmitTrim pid).run w).run a=
      ((afterGuard pid q (decide (q.staged.length>MAX_STAGED_PACKETS))
        (p.staged.length-n)).run v).run
          (clock b (decide (q.staged.length>MAX_STAGED_PACKETS))) := by
  have bound:=(path.geometry device resident).1
  rw [loop_remaining device resident path]
  have count : p.staged.length+1-n=(p.staged.length-n)+1 := by omega
  rw [count,trimPrefix,Residual.body_factor]
  simp only [bind_assoc,StateT.run_bind,gate_run current peer]
  cases decide (q.staged.length>MAX_STAGED_PACKETS) <;> rfl

theorem dropped_remaining (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (path : Yields pid w a n v b)
    (current : v.dev=some next) (peer : next.peers[pid]?=some q)
    (excess : q.staged.length>MAX_STAGED_PACKETS) :
    ((xmitTrim pid).run w).run a=
      (((charge >>= fun _=>trimPrefix pid (p.staged.length-n) >>= finish).run
        (droppedWorld pid q next v)).run (clock b true)) := by
  rw [guarded_remaining device resident path current peer,decide_eq_true excess]
  simp only [afterGuard,ite_true,StateT.run_bind,drop_run current]
  rfl

inductive Point (pid : PeerId) (w : WGWorld) (a : Ambient) : WGWorld → Ambient → Prop where
  | entry : Point pid w a w a
  | iteration (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (path : Yields pid w a n v b) : Point pid w a v b
  | guarded (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (path : Yields pid w a n v b)
      (current : v.dev=some next) (peer : next.peers[pid]?=some q) :
      Point pid w a v (clock b (decide (q.staged.length>MAX_STAGED_PACKETS)))
  | dropped (device : w.dev=some d) (resident : d.peers[pid]?=some p)
      (path : Yields pid w a n v b)
      (current : v.dev=some next) (peer : next.peers[pid]?=some q)
      (excess : q.staged.length>MAX_STAGED_PACKETS) :
      Point pid w a (droppedWorld pid q next v) (clock b true)
  | returned (performed : ((xmitTrim pid).run w).run a=.ok (((),v),b)) : Point pid w a v b

theorem Point.remaining (point : Point pid w a v b) :
    ∃remaining : WG.M Unit,((xmitTrim pid).run w).run a=(remaining.run v).run b := by
  cases point with
  | entry=>exact ⟨_,rfl⟩
  | iteration device resident path=>exact ⟨_,loop_remaining device resident path⟩
  | guarded device resident path current peer=>exact ⟨_,guarded_remaining device resident path current peer⟩
  | dropped device resident path current peer excess=>exact ⟨_,dropped_remaining device resident path current peer excess⟩
  | returned performed=>exact ⟨pure (),performed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Transmit.Front.TrimPoints
