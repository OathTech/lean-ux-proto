import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRetiredPeerHandshakeFrames

/-! The actual cookie consumer acquires and pays one identical stamped loan.
Normal refusal and normal success both preserve the same complete account. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes
open Queues Queues.RxCredits DurableHolders
set_option maxHeartbeats 600000

theorem read (pid : PeerId) : Preserves (Account holders cs loans) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a p v b account run
  exact (getPeer_normal pid w v p a b run).1 ▸ account

theorem store {action : WG.M α} (same : SameWGStore action) :
    Preserves (Account holders cs loans) action :=
  Account.native_fields (HolderEncrypt.store_fields same)

theorem payment (owner : Owner) : Hoare (peerPut (some owner.slot))
    (Account holders cs (owner :: loans)) (fun _ => Account holders cs loans) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a x v b account run
  cases x
  exact account.payment run

theorem cookie_update (msg : List UInt8) (pid : PeerId) :
    Preserves (Account holders cs loans) (HandshakeCookiePayment.update msg pid) := by
  unfold HandshakeCookiePayment.update
  apply preserves_bind (read pid)
  intro p
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .cookieNoMac1Sent (!p.haveSentMac1)) (Account holders cs loans))
  intro missing
  cases missing with
  | true => exact preserves_pure ()
  | false =>
    cases hc : xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
        ((msg.drop 32).take 32) p.lastMac1Sent with
    | none =>
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .cookieDecryptOk _) (Account holders cs loans))
      intro ok
      cases ok with
      | false => exact preserves_pure ()
      | true => exact hoare_liftAmbient (AmbientM.invariant "unreachable") (Account holders cs loans)
    | some c =>
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .cookieDecryptOk _) (Account holders cs loans))
      intro ok
      cases ok with
      | false => exact preserves_pure ()
      | true =>
        apply preserves_bind (show Preserves (Account holders cs loans) (hiddenClock64 .cookieBirthdate : WG.M Int64) from
          hoare_liftAmbient (AmbientM.hiddenClock64 .cookieBirthdate) (Account holders cs loans))
        intro now
        exact Account.update pid _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl)

/-- The source-selected nullable lookup adds no unexplained reference slack,
and both actual cookie update outcomes repay the very same added loan. -/
theorem cookie (msg : List UInt8) : Preserves (Account holders cs loans) (cookieMessageConsume msg) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  cases result
  rw [HandshakeCookiePayment.factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨entry,u,c,lookup,tail⟩ := run
  cases entry with
  | none =>
    have post := account.lookup_none a c lookup
    change Except.ok (((),u),CounterWindow.record c .cookieLookupMiss true) = .ok (((),v),b) at tail
    cases tail
    exact post
  | some entry =>
    obtain ⟨kind,pid⟩ := entry
    obtain ⟨d,p,_,_,_,post⟩ := account.lookup a c lookup
    change ((do HandshakeCookiePayment.update msg pid; peerPut (some pid) : WG.M Unit).run u).run
      (CounterWindow.record c .cookieLookupMiss false) = .ok (((),v),b) at tail
    exact (hoare_iff_run_ambient _ _ _).mp
      (hoare_bind _ _ (cookie_update msg pid) (fun _ => payment ⟨d.ifindex,pid,p.internalId⟩))
      u _ () v b post tail

theorem cookie_boundary (msg : List UInt8) : Preserves (ExactBoundary cs loans) (cookieMessageConsume msg) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b account run
  obtain ⟨holders,account⟩ := account
  exact ⟨holders,(hoare_iff_run_ambient _ _ _).mp (cookie msg) w a result v b account run⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.RetiredPeer.Handshake
