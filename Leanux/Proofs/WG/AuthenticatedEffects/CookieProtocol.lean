import Leanux.Proofs.WG.AuthenticatedEffects.CookieAcceptance
import Leanux.Proofs.WG.AuthenticatedEffects.ResponseProtocol

/-! Cookie rejection preserves complete peer protocol records. Its absence of
acceptance means the exact source observer emitted no authentication receipt;
the real lookup and repayment establish the reference safety internally. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.CounterWindow Leanux.Proofs.WG.Queues.RxCredits

theorem cookie_refusal_protocol (msg : Key) (w v : WGWorld) (a b : Ambient)
    (unaccepted : (runWGPrefix (acceptedCookie msg) w a []).2 = [])
    (run : ((cookieMessageConsume msg).run w).run a = .ok (((),v),b)) :
    peerProtocolView v = peerProtocolView w := by
  rw [cookieAuthFront_factor,native_bind_run] at run
  unfold acceptedCookie at unaccepted
  rw [liftWG_bind_run] at unaccepted
  cases lookup : ((indexLookup [.handshake,.keypair] (u32le msg 4)).run w).run a with
  | error err => simp [lookup] at run
  | ok out =>
    rcases out with ⟨⟨entry,u⟩,c⟩
    rw [lookup] at run unaccepted
    have frame := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
      (indexLookup_protocol [.handshake,.keypair] (u32le msg 4)) w a entry u c lookup
    have loan := (hoare_iff_run_ambient _ _ _).mp
      (indexLookup_loan [.handshake,.keypair] (u32le msg 4) w) w a entry u c rfl lookup
    cases entry with
    | none =>
      change Except.ok (((),u),record c .cookieLookupMiss true) = _ at run
      cases run
      exact frame
    | some entry =>
      rcases entry with ⟨owner,pid⟩
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
        have world := (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mp
          (cookieAuthFront_same_world msg pid) u _ cookie q d checked
        change q = u at world
        subst q
        cases cookie with
        | some bytes => simp at unaccepted
        | none =>
          change ((peerPut (some pid)).run u).run d = _ at run
          exact (peerPut_protocol pid u v d b (loan_repay_safe w u pid loan) run).trans frame

theorem receive_unaccepted_cookie_protocol (msg : Key) (src : SkbSource)
    (w v : WGWorld) (a b : Ambient)
    (kind : messageType msg = MESSAGE_HANDSHAKE_COOKIE)
    (unaccepted : (runWGPrefix (acceptedCookie msg) w (record a .hsCookie true) []).2 = [])
    (run : ((receiveHandshakePacket msg src).run w).run a = .ok (((),v),b)) :
    peerProtocolView v = peerProtocolView w ∧ v.sent = w.sent := by
  have silent := receive_cookie_sent msg src w v a b kind run
  rw [receive_cookie_run msg src w a kind] at run
  exact ⟨cookie_refusal_protocol msg w v _ b unaccepted run,silent⟩

end Leanux.Proofs.WG.AuthenticatedEffects
