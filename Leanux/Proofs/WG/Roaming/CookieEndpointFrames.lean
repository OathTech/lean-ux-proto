import Leanux.Proofs.WG.Roaming.ResponseRejectionFrames

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.Roaming
open Leanux Leanux.WG Noise Std.Do

/-- Every normal cookie-consumption return preserves every optional endpoint.
The actual lookup supplies its cleanup reference; no residency, owner-word,
coherence, reference-budget, decryption or clock premise is imposed. -/
theorem cookieMessageConsume_endpoints (msg : List UInt8) (entry : Option Device) :
    Ensures (cookieMessageConsume msg)
      (fun g => responseEndpointMap g.dev = responseEndpointMap entry)
      (fun _ g => responseEndpointMap g.dev = responseEndpointMap entry) := by
  let safe : WGWorld → Prop := fun g => responseEndpointMap g.dev = responseEndpointMap entry
  have hpure {α : Type} (P : WGWorld → Prop) (value : α) :
      Ensures (pure value : WG.M α) P (fun _ => P) := by
    intro g a r out after pre run; cases run; exact pre
  have hambient {α : Type} (P : WGWorld → Prop) (action : AmbientM α) :
      Ensures (StateT.lift action : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant action P)
  have hbranch (P : WGWorld → Prop) (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    hambient P (AmbientM.branch site value)
  have hwrite (pid : PeerId) (bytes : List UInt8) (birthdate : Int64) :
      Ensures (do setPeer pid {(← getPeer pid) with cookie := bytes, cookieBirthdate := birthdate, cookieIsValid := true, haveSentMac1 := false})
        (ResponseEndpointHeld entry pid) (fun _ => ResponseEndpointHeld entry pid) := by
    intro g ambient result final after pre run
    obtain ⟨same,d,p,device,resident,retained⟩ := pre
    simp [getPeer,getDev,device,resident,setPeer,modifyDev] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    refine ⟨?_,_,{p with cookie := bytes, cookieBirthdate := birthdate, cookieIsValid := true, haveSentMac1 := false},rfl,by simp,retained⟩
    refine Eq.trans ?_ same
    rw [device]
    funext target
    by_cases hit : pid = target
    · subst target; simp [responseEndpointMap,resident]
    · simp [responseEndpointMap,Std.TreeMap.getElem?_insert,hit]
  let tail (pid : PeerId) : WG.M Unit := do
    let p ← getPeer pid
    if ← branch .cookieNoMac1Sent !p.haveSentMac1 then
      peerPut (some pid)
      return
    let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
      ((msg.drop 32).take 32) p.lastMac1Sent
    if ← branch .cookieDecryptOk cookie.isSome then
      let some bytes := cookie | invariant "unreachable"
      let birthdate ← hiddenClock64 .cookieBirthdate
      setPeer pid {(← getPeer pid) with cookie := bytes, cookieBirthdate := birthdate, cookieIsValid := true, haveSentMac1 := false}
    peerPut (some pid)
  let selected (found : Option (IndexOwner × PeerId)) : WG.M Unit := do
    if ← branch .cookieLookupMiss found.isNone then return
    let some (_,pid) := found | invariant "unreachable"
    tail pid
  have factor : cookieMessageConsume msg = (do
      let found ← indexLookup [.handshake,.keypair] (u32le msg 4)
      selected found) := by rfl
  have htail (pid : PeerId) :
      Ensures (tail pid) (ResponseEndpointHeld entry pid) (fun _ => safe) := by
    have hread : Ensures (getPeer pid) (ResponseEndpointHeld entry pid)
        (fun _ => ResponseEndpointHeld entry pid) := by
      intro g a r out after pre run
      exact ((ensures_iff _ _ _).mpr (getPeer_spec pid (ResponseEndpointHeld entry pid))
        g a r out after pre run).1
    unfold tail
    refine ensures_bind _ _ hread ?_
    intro p
    refine ensures_bind _ _ (hbranch _ _ _) ?_
    intro absent
    cases absent with
    | true => exact ensures_bind _ _ (peerPut_responseEndpoints entry pid) (fun _ => hpure safe ())
    | false =>
      refine ensures_bind _ _ (hbranch _ _ _) ?_
      intro decrypted
      cases decrypted with
      | false => exact peerPut_responseEndpoints entry pid
      | true =>
        cases cookie : xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
            ((msg.drop 32).take 32) p.lastMac1Sent with
        | none => intro g a r out after pre run; cases run
        | some bytes =>
          refine ensures_bind _ _ (hambient _ (AmbientM.hiddenClock64 .cookieBirthdate)) ?_
          intro birthdate
          rw [← bind_assoc]
          exact ensures_bind _ _ (hwrite pid bytes birthdate)
            (fun _ => peerPut_responseEndpoints entry pid)
  change Ensures (cookieMessageConsume msg) safe (fun _ => safe)
  rw [factor]
  refine ensures_bind _ _ (indexLookup_responseEndpoints [.handshake,.keypair] (u32le msg 4) entry) ?_
  intro found g ambient result final after pre run
  cases found with
  | none =>
    simp [selected,branch,AmbientM.branch] at run
    rcases run with ⟨⟨rfl,rfl⟩,rfl⟩
    exact pre.1
  | some pair =>
    rcases pair with ⟨owner,pid⟩
    have held : ResponseEndpointHeld entry pid g := ⟨pre.1,pre.2 owner pid rfl⟩
    have chosen : Ensures (selected (some (owner,pid))) (ResponseEndpointHeld entry pid)
        (fun _ => safe) := by
      unfold selected
      refine ensures_bind _ _ ((ensures_iff _ _ _).mpr
        (Config.branch_state_spec (ResponseEndpointHeld entry pid) .cookieLookupMiss false)) ?_
      intro value current inputs r out remaining h actual
      rcases h with ⟨rfl,h⟩
      exact htail pid current inputs r out remaining h actual
    exact chosen g ambient result final after held run

end Leanux.Proofs.WG.Roaming
