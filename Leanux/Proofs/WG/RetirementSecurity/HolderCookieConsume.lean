import Leanux.Proofs.WG.RetirementSecurity.HolderReceiveArms

/-! The cookie consumer's actual index acquisition also protects its final
peer put. Even rejected cookies preserve exact key credit without assuming
the peer's base reference or a global holder-account theorem. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderConsume
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

def cookieTail (msg : List UInt8) (pid : PeerId) : WG.M Unit := do
  let p ← getPeer pid
  if ← branch .cookieNoMac1Sent !p.haveSentMac1 then
    peerPut (some pid)
    return
  let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 32) p.lastMac1Sent
  if ← branch .cookieDecryptOk cookie.isSome then
    let some c := cookie | invariant "unreachable"
    let birthdate ← hiddenClock64 .cookieBirthdate
    setPeer pid {(←getPeer pid) with cookie:=c,cookieBirthdate:=birthdate,cookieIsValid:=true,haveSentMac1:=false}
  peerPut (some pid)

theorem cookie_factor (msg : List UInt8) : cookieMessageConsume msg = (do
    let entry ← indexLookup [.handshake,.keypair] (u32le msg 4)
    if ← branch .cookieLookupMiss entry.isNone then return
    let some (_,pid) := entry | invariant "unreachable"
    cookieTail msg pid) := rfl

theorem cookie_tail (msg : List UInt8) (pid : PeerId) : Hoare (cookieTail msg pid)
    (Inv temporary pid) (fun _ => HolderAccount temporary) := by
  have paid : Hoare (do peerPut (some pid); pure () : WG.M Unit)
      (Inv temporary pid) (fun _ => HolderAccount temporary) :=
    hoare_bind _ _ (payment pid) (fun _ => preserves_pure ())
  unfold cookieTail
  simp (config := {zeta := false}) only [branch,hiddenClock64]
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (loan_update_head
       apply update_bind
       · intro p; rfl
       · intro p; rfl
       intro x)
    | (loan_bind_head peerPut; exact paid)
    | (index_material_head peerPut; exact payment pid)
    | (index_material_head invariant; exact stop _)
    | (index_material_head getPeer; exact getPeer_preserves _ _)
    | loan_crypto (Inv temporary pid)
    | (index_material_head Bind.bind; apply hoare_bind)
    | material_component
    | material_intro
    | material_reduce
    | (index_material_head ite; split)
    | material_match
  all_goals exact HolderConsume.stop _

theorem cookie (msg : List UInt8) : Preserves (HolderAccount temporary) (cookieMessageConsume msg) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  rw [cookie_factor,MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨entry,u,c,lookup,tail⟩ := run
  have account := (hoare_iff_run_ambient _ _ _).mp
    (indexLookup_holders [.handshake,.keypair] (u32le msg 4) temporary)
    w a entry u c before lookup
  have loan := (hoare_iff_run_ambient _ _ _).mp
    (indexLookup_loan [.handshake,.keypair] (u32le msg 4) w)
    w a entry u c rfl lookup
  cases entry with
  | none =>
    change Except.ok (((),u),CounterWindow.record c .cookieLookupMiss true)=.ok ((result,v),b) at tail
    cases tail
    exact account
  | some entry =>
    obtain ⟨owner,pid⟩ := entry
    change ((cookieTail msg pid).run u).run (CounterWindow.record c .cookieLookupMiss false)=
      .ok ((result,v),b) at tail
    exact (hoare_iff_run_ambient _ _ _).mp (cookie_tail msg pid) u _ result v b
      ⟨account,strong_loan loan⟩ tail

end Leanux.Proofs.WG.RetirementSecurity.HolderConsume
