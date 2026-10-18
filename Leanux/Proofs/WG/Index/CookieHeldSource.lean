import Leanux.WG.Receive
import Leanux.Proofs.WG.Index.OwnerCoherencePeerLookupClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceHeldFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

theorem cookieMessageConsume_preserves_held_source (msg : List UInt8)
    (safe : WGWorld → Prop) (held : PeerId → WGWorld → Prop)
    (lookup : Ensures (indexLookup [.handshake,.keypair] (u32le msg 4)) safe
      (fun result g => safe g ∧ ∀ owner pid,result=some (owner,pid) → held pid g))
    (written : ∀ pid bytes birthdate, Ensures (do
      setPeer pid {(← getPeer pid) with cookie:=bytes,cookieBirthdate:=birthdate,cookieIsValid:=true,haveSentMac1:=false})
      (held pid) (fun _ => held pid))
    (paid : ∀ pid,Ensures (peerPut (some pid)) (held pid) (fun _ => safe)) :
    Ensures (cookieMessageConsume msg) safe (fun _ => safe) := by
  have hpure {α : Type} (P : WGWorld → Prop) (x : α) :
      Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g a r out after pre run; cases run; exact pre
  have hambient {α : Type} (P : WGWorld → Prop) (a : AmbientM α) :
      Ensures (StateT.lift a : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant a P)
  have hbranch (P : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    hambient P (AmbientM.branch site value)
  let tail (pid : PeerId) : WG.M Unit := do
    let p ← getPeer pid
    if ← branch .cookieNoMac1Sent !p.haveSentMac1 then
      peerPut (some pid)
      return
    let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
      ((msg.drop 32).take 32) p.lastMac1Sent
    if ← branch .cookieDecryptOk cookie.isSome then
      let some c := cookie | invariant "unreachable"
      let birthdate ← hiddenClock64 .cookieBirthdate
      setPeer pid {(← getPeer pid) with cookie := c, cookieBirthdate := birthdate, cookieIsValid := true, haveSentMac1 := false}
    peerPut (some pid)
  let selected (entry : Option (IndexOwner × PeerId)) : WG.M Unit := do
    if ← branch .cookieLookupMiss entry.isNone then return
    let some (_,pid) := entry | invariant "unreachable"
    tail pid
  have factor : cookieMessageConsume msg = (do
      let entry ← indexLookup [.handshake,.keypair] (u32le msg 4)
      selected entry) := by rfl
  have htail (pid : PeerId) : Ensures (tail pid) (held pid) (fun _ => safe) := by
    have hread : Ensures (getPeer pid) (held pid) (fun _ => held pid) := by
      intro g a r out after pre run
      exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (held pid))
        g a r out after pre run).1
    unfold tail
    refine ensures_bind _ _ hread ?_
    intro p
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro absent
    cases absent with
    | true =>
      exact ensures_bind _ _ (paid pid) (fun _ => hpure safe ())
    | false =>
      refine ensures_bind _ _ (hbranch _ _ _) ?_
      intro decrypted
      cases decrypted with
      | false => exact paid pid
      | true =>
        cases cookie : xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
            ((msg.drop 32).take 32) p.lastMac1Sent with
        | none =>
          intro g a r out after pre run
          cases run
        | some bytes =>
          refine ensures_bind _ _ (hambient _ (AmbientM.hiddenClock64 .cookieBirthdate)) ?_
          intro birthdate
          rw [← bind_assoc]
          exact ensures_bind _ _ (written pid bytes birthdate) (fun _ => paid pid)
  change Ensures (cookieMessageConsume msg) safe (fun _ => safe)
  rw [factor]
  refine ensures_bind _ _ lookup ?_
  intro entry g ambient result out after pre run
  cases entry with
  | none =>
    simp [selected, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact pre.1
  | some pair =>
    rcases pair with ⟨owner,pid⟩
    have acquired : held pid g := pre.2 owner pid rfl
    have chosen : Ensures (selected (some (owner,pid))) (held pid)
        (fun _ => safe) := by
      unfold selected
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (Config.branch_state_spec (held pid) .cookieLookupMiss false)) ?_
      intro value g a r final inputs h actual
      rcases h with ⟨rfl,h⟩
      exact htail pid g a r final inputs h actual
    exact chosen g ambient result out after acquired run


end Leanux.Proofs.WG.Index
