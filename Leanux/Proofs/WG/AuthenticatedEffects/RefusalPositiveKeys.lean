import Leanux.Proofs.WG.AuthenticatedEffects.RefusalPositivePeers

/-! Full resident keypair records on actual cookie refusal. Successful index
acquisition writes back its own unchanged owner word; failed acquisition uses
the visible positive-resident entry condition. No key fields are masked. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.CounterWindow Leanux.Proofs.WG.Queues.RxCredits
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem acquire_keys (owner : IndexOwner) (w v : WGWorld) (pid : PeerId) (a b : Ambient)
    (run : ((Affiliation.acquireOwner owner).run w).run a = .ok ((some pid,v),b)) :
    residentKeys v = residentKeys w := by
  obtain ⟨word,u,q,c,d,read,borrow,write⟩ := Affiliation.acquireOwner_acquisition owner w v (some pid) a b run
  have world : u = w := (hoare_iff_run_ambient _ _ _).mp
    (indexOwner_peerWord_preserves owner (fun z => z = w))
    w a word u c rfl read
  subst u
  have readWord := ((hoare_iff_run_ambient _ _ _).mp
    (Affiliation.peerWord_spec owner (fun _ => True)) w a word w c True.intro read).2
  have borrowed := (hoare_iff_run_ambient _ _ _).mp
    (PeerBorrow.acquire_spec word (wgStoreView w)) w c (some pid) q d rfl borrow
  have sameWord : word = some pid := borrowed.1.resolve_left (by simp) |>.symm
  have affiliation := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (Affiliation.peerGetMaybeZero_view word) w c (some pid) q d borrow
  have currentWord : Affiliation.wordAt q owner = some (some pid) := by
    simpa only [Affiliation.wordAt,affiliation,sameWord] using readWord
  have frame := unchanged_owner_keys owner (some pid) q v d b currentWord write
  obtain ⟨device,p,hd,_hp,_positive,store⟩ := borrowed.2
  have hq := congrArg WGStoreView.dev store
  change q.dev = some {device with peers := device.peers.insert pid {p with refcount := p.refcount + 1}} at hq
  change w.dev = some device at hd
  apply frame.trans
  funext kid
  simp [residentKeys,hq,hd]

theorem index_success_keys (kinds : List IndexKind) (index : Nat)
    (w v : WGWorld) (owner : IndexOwner) (pid : PeerId) (a b : Ambient)
    (run : ((indexLookup kinds index).run w).run a = .ok ((some (owner,pid),v),b)) :
    residentKeys v = residentKeys w := by
  rw [lookup_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨⟨entry,stopped⟩,u,c,scanned,tail⟩ := run
  have same := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (scan_same_world kinds index) w a _ u c scanned
  change u = w at same
  subst u
  cases stopped <;> cases entry <;>
    simp [lookupTail,branch,StateT.run_bind,StateT.run_pure,StateT.run_monadLift,
      except_ok_bind,except_pure] at tail
  case false.some entry =>
    cases acquired : ((Affiliation.acquireOwner entry.owner).run w).run
        (record (record c .idxWalk false) .idxFound true) with
    | error err => simp [acquired] at tail
    | ok out =>
      rcases out with ⟨⟨result,u⟩,d⟩
      cases result <;> simp [acquired,except_ok_bind] at tail
      rcases tail with ⟨⟨⟨_,rfl⟩,rfl⟩,_⟩
      exact acquire_keys entry.owner w _ _ _ _ acquired
  case true.some entry =>
    cases acquired : ((Affiliation.acquireOwner entry.owner).run w).run
        (record c .idxFound true) with
    | error err => simp [acquired] at tail
    | ok out =>
      rcases out with ⟨⟨result,u⟩,d⟩
      cases result <;> simp [acquired,except_ok_bind] at tail
      rcases tail with ⟨⟨⟨_,rfl⟩,rfl⟩,_⟩
      exact acquire_keys entry.owner w _ _ _ _ acquired

theorem repay_keys (initial w v : WGWorld) (pid : PeerId) (a b : Ambient)
    (loan : Loan initial pid w)
    (run : ((peerPut (some pid)).run w).run a = .ok (((),v),b)) :
    residentKeys v = residentKeys w := by
  obtain ⟨p,_old,positive,peers⟩ := loan
  have selected : residents w pid = some {p with refcount := p.refcount + 1} := by
    simpa using peers pid
  obtain ⟨d,hd,hp⟩ := Option.bind_eq_some_iff.mp selected
  have nonzero : p.refcount ≠ 0 := by omega
  simp [peerPut,requireNotPending,getPeer,getDev,setPeer,modifyDev,refcountDecAndTest,
    branch,branchCmp,branch_run,branchCmp_run,hd,hp,nonzero,
    StateT.run_bind,StateT.run_pure,StateT.run_monadLift,except_ok_bind,except_pure] at run
  obtain ⟨rfl,_⟩ := run
  funext kid
  simp [residentKeys,hd]

theorem cookie_refusal_keys (msg : Key) (w v : WGWorld) (a b : Ambient)
    (positive : Positive w)
    (unaccepted : (runWGPrefix (acceptedCookie msg) w a []).2 = [])
    (run : ((cookieMessageConsume msg).run w).run a = .ok (((),v),b)) :
    residentKeys v = residentKeys w := by
  rw [cookieAuthFront_factor,native_bind_run] at run
  unfold acceptedCookie at unaccepted
  rw [liftWG_bind_run] at unaccepted
  cases lookup : ((indexLookup [.handshake,.keypair] (u32le msg 4)).run w).run a with
  | error err => simp [lookup] at run
  | ok out =>
    rcases out with ⟨⟨entry,u⟩,c⟩
    rw [lookup] at run unaccepted
    cases entry with
    | none =>
      change Except.ok (((),u),record c .cookieLookupMiss true) = _ at run
      cases run
      exact (index_none _ _ _ _ _ _ positive lookup).2
    | some entry =>
      rcases entry with ⟨owner,pid⟩
      have loan := index_success [.handshake,.keypair] (u32le msg 4) w u owner pid a c lookup
      have keys := index_success_keys [.handshake,.keypair] (u32le msg 4) w u owner pid a c lookup
      change ((cookieAuthFront msg pid >>= cookieAfterAuth pid).run u).run
        (record c .cookieLookupMiss false) = _ at run
      change (runWGPrefix (acceptedCookieTail msg pid) u
        (record c .cookieLookupMiss false) []).2 = [] at unaccepted
      rw [native_bind_run] at run
      rw [acceptedCookieTail_run] at unaccepted
      cases checked : ((cookieAuthFront msg pid).run u).run (record c .cookieLookupMiss false) with
      | error err => simp [checked] at run
      | ok checkedOut =>
        rcases checkedOut with ⟨⟨cookie,q⟩,d⟩
        rw [checked] at run unaccepted
        have world := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
          (cookieAuthFront_same_world msg pid) u _ cookie q d checked
        change q = u at world
        subst q
        cases cookie with
        | some bytes => simp at unaccepted
        | none =>
          change ((peerPut (some pid)).run u).run d = _ at run
          exact (repay_keys w u v pid d b loan run).trans keys

end Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
