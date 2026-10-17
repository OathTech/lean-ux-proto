import Leanux.WG.Receive
import Leanux.Proofs.WG.Index.OwnerCoherencePeerLookupClaims
import Leanux.Proofs.WG.Index.OwnerCoherenceHeldFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Std.Do

/-- The actual cookie-reply consumer preserves hashed-owner coherence. Its
lookup supplies the reference released on every normal exit; cookie writes
retain owner metadata. No crypto, clock or reference-readiness is assumed. -/
theorem cookieMessageConsume_owner_coherent (msg : List UInt8) :
    Campaign2.Ensures (cookieMessageConsume msg) View.OwnerCoherentSafe
      (fun _ => View.OwnerCoherentSafe) := by
  let safe : WGWorld → Prop := fun g => ∀ d, g.dev = some d → HashedOwnersCoherent d
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
  have htail (pid : PeerId) : Ensures (tail pid) (OwnerPeerHeldWG pid) (fun _ => safe) := by
    have hread : Ensures (getPeer pid) (OwnerPeerHeldWG pid) (fun _ => OwnerPeerHeldWG pid) := by
      intro g a r out after pre run
      exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (OwnerPeerHeldWG pid))
        g a r out after pre run).1
    unfold tail
    refine ensures_bind _ _ hread ?_
    intro p
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro absent
    cases absent with
    | true =>
      exact ensures_bind _ _ (peerPut_ownerHeld pid) (fun _ => hpure safe ())
    | false =>
      refine ensures_bind _ _ (hbranch _ _ _) ?_
      intro decrypted
      cases decrypted with
      | false => exact peerPut_ownerHeld pid
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
          have write : Ensures (do setPeer pid {(← getPeer pid) with cookie := bytes, cookieBirthdate := birthdate, cookieIsValid := true, haveSentMac1 := false})
              (OwnerPeerHeldWG pid) (fun _ => OwnerPeerHeldWG pid) :=
            modifyPeer_ownerHeld pid pid _ (fun _ => rfl) (fun _ => rfl)
          exact ensures_bind _ _ write (fun _ => peerPut_ownerHeld pid)
  change Ensures (cookieMessageConsume msg) safe (fun _ => safe)
  rw [factor]
  have hlookup : Ensures (indexLookup [.handshake,.keypair] (u32le msg 4)) safe
      (fun result g => safe g ∧ ∀owner pid, result = some (owner,pid) →
        ∃d p, g.dev = some d ∧ d.peers[pid]? = some p ∧ 1 < p.refcount) :=
    indexLookup_peer_held [.handshake,.keypair] (u32le msg 4)
  refine ensures_bind _ _ hlookup ?_
  intro entry g ambient result out after pre run
  cases entry with
  | none =>
    simp [selected, branch, AmbientM.branch] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact pre.1
  | some pair =>
    rcases pair with ⟨owner,pid⟩
    have held : OwnerPeerHeldWG pid g := ⟨pre.1,pre.2 owner pid rfl⟩
    have chosen : Ensures (selected (some (owner,pid))) (OwnerPeerHeldWG pid)
        (fun _ => safe) := by
      unfold selected
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (Config.branch_state_spec (OwnerPeerHeldWG pid) .cookieLookupMiss false)) ?_
      intro value g a r final inputs h actual
      rcases h with ⟨rfl,h⟩
      exact htail pid g a r final inputs h actual
    exact chosen g ambient result out after held run

end Leanux.Proofs.WG.Index
