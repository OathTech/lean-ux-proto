import Leanux.Proofs.WG.Queues.HandshakeResponse

/-! The cookie consumer uses the actual index-acquired owner, retains that
single reservation through cookie writes, and pays it on both return paths. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HandshakeCookiePayment
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

theorem lookup_funded (kinds : List IndexKind) (index : Nat) {holders : DurableHolders}
    (funded : holders.Funded cs loans w) (stable : StableRx cs w) (a b : Ambient)
    (run : ((indexLookup kinds index).run w).run a = .ok ((entry,v),b)) :
    HandshakeLoans.FundedResult holders cs loans (entry.map Prod.snd) v :=
  (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeLoans.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans.funded_result)
    funded.aligned
    ((hoare_iff_run_ambient _ _ _).mp
      ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeLoans.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeLoans.lookup_frame) kinds index w)
      w a entry v b (Frame.refl w) run)
    (HandshakeLoans.indexLookup_result kinds index ⟨funded.carriers,stable⟩ a b run)

def update (msg : List UInt8) (pid : PeerId) : WG.M Unit := do
  let p ← getPeer pid
  if ← branch .cookieNoMac1Sent !p.haveSentMac1 then return
  let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 32) p.lastMac1Sent
  if ← branch .cookieDecryptOk cookie.isSome then
    let some c := cookie | invariant "unreachable"
    let birthdate ← hiddenClock64 .cookieBirthdate
    setPeer pid {(←getPeer pid) with cookie:=c,cookieBirthdate:=birthdate,cookieIsValid:=true,haveSentMac1:=false}

theorem update_spec (msg : List UInt8) (pid : PeerId) : Preserves (Boundary cs loans) (update msg pid) := by
  unfold update
  apply preserves_bind ((pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceive.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive.read) pid)
  intro p
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .cookieNoMac1Sent (!p.haveSentMac1)) (Boundary cs loans))
  intro missing
  cases missing with
  | true => exact preserves_pure ()
  | false =>
    cases hc : xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
        ((msg.drop 32).take 32) p.lastMac1Sent with
    | none =>
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .cookieDecryptOk _) (Boundary cs loans))
      intro ok
      cases ok with
      | false => exact preserves_pure ()
      | true => exact hoare_liftAmbient (AmbientM.invariant "unreachable") (Boundary cs loans)
    | some c =>
      apply preserves_bind (hoare_liftAmbient (AmbientM.branch .cookieDecryptOk _) (Boundary cs loans))
      intro ok
      cases ok with
      | false => exact preserves_pure ()
      | true =>
        apply preserves_bind (show Preserves (Boundary cs loans) (hiddenClock64 .cookieBirthdate : WG.M Int64) from
          hoare_liftAmbient (AmbientM.hiddenClock64 .cookieBirthdate) (Boundary cs loans))
        intro now
        exact (pinned_const _private.Leanux.Proofs.WG.Queues.HandshakeReceive.«0».Leanux.Proofs.WG.Queues.RxCredits.HandshakeReceive.update)
          pid _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ h => h) (fun _ => rfl)

theorem factor (msg : List UInt8) : cookieMessageConsume msg = (do
    let entry ← indexLookup [.handshake,.keypair] (u32le msg 4)
    if ← branch .cookieLookupMiss entry.isNone then return
    let some (_,pid) := entry | invariant "unreachable"
    update msg pid
    peerPut (some pid)) := by
  have stopped {α β : Type} (why : String) (next : α → WG.M β) :
      ((invariant why : WG.M α) >>= next) = (invariant why : WG.M β) := rfl
  unfold cookieMessageConsume update
  apply congrArg (Bind.bind (indexLookup [.handshake,.keypair] (u32le msg 4)))
  funext entry
  apply congrArg (Bind.bind (branch .cookieLookupMiss entry.isNone : WG.M Bool))
  funext missing
  cases missing with
  | true => rfl
  | false =>
    cases entry with
    | none => rfl
    | some entry =>
      obtain ⟨kind,pid⟩ := entry
      simp only [Bool.false_eq_true,ite_false,bind_assoc]
      apply congrArg (Bind.bind (getPeer pid))
      funext p
      apply congrArg (Bind.bind (branch .cookieNoMac1Sent (!p.haveSentMac1) : WG.M Bool))
      funext noMac
      cases noMac with
      | true => simp only [ite_true,pure_bind,bind_pure_unit]
      | false =>
        simp only [Bool.false_eq_true,ite_false,bind_assoc]
        apply congrArg (Bind.bind (branch .cookieDecryptOk
          (xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 32) p.lastMac1Sent).isSome : WG.M Bool))
        funext ok
        cases ok <;> cases hc : xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
            ((msg.drop 32).take 32) p.lastMac1Sent
        all_goals simp only [Bool.false_eq_true,ite_false,ite_true,pure_bind,bind_assoc,stopped]

theorem consume (msg : List UInt8) : Preserves (Boundary cs loans) (cookieMessageConsume msg) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  cases result
  rw [factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨entry,u,c,lookup,tail⟩ := run
  obtain ⟨holders,funded,stable⟩ := hi
  have post := lookup_funded [.handshake,.keypair] (u32le msg 4) funded stable a c lookup
  cases entry with
  | none =>
    change Except.ok (((),u),CounterWindow.record c .cookieLookupMiss true)=.ok (((),v),b) at tail
    cases tail
    exact ⟨holders,post⟩
  | some entry =>
    obtain ⟨kind,pid⟩ := entry
    change ((do update msg pid;peerPut (some pid) : WG.M Unit).run u).run
      (CounterWindow.record c .cookieLookupMiss false)=.ok (((),v),b) at tail
    obtain ⟨o,slot,funded,stable⟩ := post
    change o.slot = pid at slot
    subst pid
    exact (hoare_iff_run_ambient _ _ _).mp
      (hoare_bind _ _ (update_spec msg o.slot) (fun _ => HandshakeReceive.pay o))
      u _ () v b ⟨holders,funded,stable⟩ tail

end Leanux.Proofs.WG.Queues.RxCredits.HandshakeCookiePayment
