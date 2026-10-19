import Leanux.Proofs.WG.AuthenticatedEffects.RefusalLookupLiveness
import Leanux.Proofs.WG.AuthenticatedEffects.CookieProtocol

/-! Complete peer records on response/cookie refusal, including actual failed
lookup arms. The native entry positivity condition stays visible until the
initialized driver provides it; successful lookup loans are source-derived. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.CounterWindow Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem response_refusal (msg : Key) (w v : WGWorld) (a b : Ambient)
    (positive : Positive w)
    (run : ((consumeResponse msg).run w).run a = .ok ((none,v),b)) :
    residents v = residents w := by
  rw [consumeResponse_factor] at run
  cases hd : w.dev with
  | none => simp [getDev,hd,invariant,AmbientM.invariant,StateT.run_bind] at run; cases run
  | some device =>
    cases identity : device.staticIdentity.hasIdentity with
    | false =>
      simp [getDev,hd,identity,branch,branch_run,StateT.run_bind] at run
      obtain ⟨rfl,_⟩ := run
      rfl
    | true =>
      simp [getDev,hd,identity,branch,branch_run,StateT.run_bind] at run
      cases lookup : ((indexLookup [.handshake] (u32le msg 8)).run w).run
          (record a .crespNoIdentity false) with
      | error err => simp [lookup] at run
      | ok out =>
        rcases out with ⟨⟨entry,u⟩,c⟩
        cases entry with
        | none =>
          simp [lookup] at run
          obtain ⟨rfl,_⟩ := run
          exact (index_none _ _ _ _ _ _ positive lookup).1
        | some entry =>
          rcases entry with ⟨owner,pid⟩
          have loan := index_success [.handshake] (u32le msg 8) w u owner pid _ c lookup
          cases owner with
          | keypair kid => simp [lookup,invariant,AmbientM.invariant] at run; cases run
          | handshake owner =>
            simp only [lookup,except_ok_bind,Option.isNone_some] at run
            exact (hoare_iff_run_ambient _ _ _).mp
              (response_tail msg device.staticIdentity pid w) u _ none v b loan run rfl

theorem cookie_after_lookup (msg : Key) (w u q v : WGWorld)
    (owner : IndexOwner) (pid : PeerId) (a b c d : Ambient)
    (lookup : ((indexLookup [.handshake,.keypair] (u32le msg 4)).run w).run a =
      .ok ((some (owner,pid),u),b))
    (front : ((cookieAuthFront msg pid).run u).run (record b .cookieLookupMiss false) =
      .ok ((none,q),c))
    (paid : ((peerPut (some pid)).run q).run c = .ok (((),v),d)) :
    residents v = residents w := by
  have same := (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
    (cookieAuthFront_same_world msg pid) u _ none q c front
  change q = u at same
  subst q
  exact repay w u v pid c d (index_success _ _ _ _ _ _ _ _ lookup) paid

theorem cookie_refusal (msg : Key) (w v : WGWorld) (a b : Ambient)
    (positive : Positive w)
    (unaccepted : (runWGPrefix (acceptedCookie msg) w a []).2 = [])
    (run : ((cookieMessageConsume msg).run w).run a = .ok (((),v),b)) :
    residents v = residents w := by
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
      exact (index_none _ _ _ _ _ _ positive lookup).1
    | some entry =>
      rcases entry with ⟨owner,pid⟩
      have loan := index_success [.handshake,.keypair] (u32le msg 4) w u owner pid a c lookup
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
          exact repay w u v pid d b loan run

end Leanux.Proofs.WG.AuthenticatedEffects.ResponseLoan
