import Leanux.Proofs.WG.Config.EndpointSetSource
import Leanux.Proofs.WG.Roaming.EndpointSource
import Leanux.Proofs.WG.Noise.ResponseSuffixTagFrames
import Leanux.Proofs.WG.Noise.ResponseTagSource
import Leanux.Proofs.WG.Queues.HandshakeCookiePayment

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise.ReceptionTagSupport
open Leanux Leanux.WG Std.Do

theorem endpointStores_tags (d : Device) (pid : PeerId) (p : Peer)
    (e : Endpoint) (reset : Option UInt64) (resident : d.peers[pid]? = some p) :
    responseTagMap (some (Config.endpointStores d pid p e reset)) =
      responseTagMap (some d) := by
  unfold Config.endpointStores
  split
  · rfl
  · cases reset with
    | none => exact tagMap_write d pid p _ resident rfl
    | some ts =>
      let written := {p with endpoint := some e}
      let updated := {written with dstCache := {written.dstCache with resetTs := ts}}
      exact (tagMap_write (Config.withPeer d pid written) pid written updated
        (by simp [Config.withPeer]) rfl).trans
        (tagMap_write d pid p written resident rfl)

theorem setPeerEndpoint_tag_frame (pid : PeerId) (e : Endpoint)
    (valid : e.family = AF_INET ∨ e.family = AF_INET6) (entry : Option Device) :
    Ensures (setPeerEndpoint pid e)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  cases device : g.dev with
  | none =>
    simp [setPeerEndpoint, requireNotPending, getPeer, getDev, device,
      invariant, AmbientM.invariant] at run
    cases run
  | some d =>
    cases resident : d.peers[pid]? with
    | none =>
      simp [setPeerEndpoint, requireNotPending, getPeer, getDev, device, resident,
        invariant, AmbientM.invariant] at run
      cases run
    | some p =>
      obtain ⟨reset, effect, _, _⟩ := Config.setPeerEndpoint_exact pid e d p resident
        valid g.nlSock7 g.fixtureNetDevices g ambient result final after
        ⟨device, rfl, rfl⟩ run
      rw [effect, endpointStores_tags d pid p e reset resident]
      simpa [device] using pre

theorem setPeerEndpointFromSkb_tag_frame (pid : PeerId) (src : SkbSource)
    (entry : Option Device) :
    Ensures (setPeerEndpointFromSkb pid src)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  let P : WGWorld → Prop := fun g => responseTagMap g.dev = responseTagMap entry
  unfold setPeerEndpointFromSkb
  refine ensures_bind _ _ ((ensures_iff _ _ _).mpr (Roaming.endpointFromSkb_exact src P)) ?_
  intro endpoint g ambient result final after pre run
  obtain ⟨hp, rfl, _⟩ := pre
  have valid : (Roaming.sourceEndpoint src).family = AF_INET ∨
      (Roaming.sourceEndpoint src).family = AF_INET6 := by
    unfold Roaming.sourceEndpoint
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have continuation : Ensures (do
      if ← branch .epFromSkbOk (some (Roaming.sourceEndpoint src)).isSome then
        setPeerEndpoint pid (Roaming.sourceEndpoint src)) P (fun _ => P) := by
    refine ensures_bind _ _
      ((ensures_iff _ _ _).mpr
        (hoare_liftAmbient_variant (AmbientM.branch .epFromSkbOk true) P)) ?_
    intro ok
    cases ok with
    | false => intro _ _ _ _ _ h r; cases r; exact h
    | true => exact setPeerEndpoint_tag_frame pid _ valid entry
  exact continuation g ambient result final after hp run

private theorem modifyPeer_tags (entry : Option Device) (pid : PeerId)
    (f : Peer → Peer) (tag : ∀p, (f p).handshakeState = p.handshakeState) :
    Ensures (modifyPeer pid f)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  have point := modifyPeer_spec_creationTagMap_variant entry pid f id
    (fun p => congrArg some (tag p)) g ambient result final after pre run
  funext target
  simpa only [id_eq, ite_self] using point target

theorem handshakeComplete_tag_frame (pid : PeerId) (site : HiddenSite)
    (entry : Option Device) :
    Ensures (timersHandshakeComplete pid site)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  let P : WGWorld → Prop := fun g => responseTagMap g.dev = responseTagMap entry
  have updateFactor (f : Peer → Peer) :
      modifyPeer pid f = (do let p ← getPeer pid; setPeer pid (f p)) := rfl
  have factor : timersHandshakeComplete pid site = (do
      delTimer pid .retransmitHandshake
      modifyPeer pid (fun p => {p with timerHandshakeAttempts := 0, sentLastminuteHandshake := false})
      let now ← hidden site
      modifyPeer pid (fun p => {p with walltimeLastHandshake := now})) := by
    simp only [timersHandshakeComplete, updateFactor, bind_assoc]
  rw [factor]
  change Ensures _ P (fun _ => P)
  refine ensures_bind _ _ (ResponseSuffix.delTimer_tag_frame pid .retransmitHandshake entry) ?_
  intro _
  refine ensures_bind _ _ (modifyPeer_tags entry pid _ (fun _ => rfl)) ?_
  intro _
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.hidden site) P)) ?_
  intro now
  exact modifyPeer_tags entry pid _ (fun _ => rfl)

private theorem modifyPeer_held (entry : Option Device) (pid : PeerId)
    (f : Peer → Peer) (tag : ∀p, (f p).handshakeState = p.handshakeState)
    (count : ∀p, (f p).refcount = p.refcount) :
    Ensures (modifyPeer pid f) (ResponseTagHeld entry pid)
      (fun _ => ResponseTagHeld entry pid) := by
  intro g ambient result final after pre run
  obtain ⟨same, d, p, device, resident, retained⟩ := pre
  change (((do let p ← getPeer pid; setPeer pid (f p)) : WG.M Unit).run g).run ambient = _ at run
  simp [getPeer, getDev, device, resident, setPeer, modifyDev] at run
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
  refine ⟨?_, _, f p, rfl, by simp, ?_⟩
  · exact (tagMap_write d pid p (f p) resident (tag p)).trans
      (by simpa [device] using same)
  · simpa only [count] using retained

theorem cookieUpdate_held (msg : List UInt8) (pid : PeerId) (entry : Option Device) :
    Ensures (Queues.RxCredits.HandshakeCookiePayment.update msg pid)
      (ResponseTagHeld entry pid) (fun _ => ResponseTagHeld entry pid) := by
  let P := ResponseTagHeld entry pid
  have read : Ensures (getPeer pid) P (fun _ => P) := by
    intro g a r final after pre run
    exact (((ensures_iff _ _ _).mpr (getPeer_spec pid P)) g a r final after pre run).1
  have branchF (site : Decision) (value : Bool) :
      Ensures (branch site value : WG.M Bool) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant (AmbientM.branch site value) P)
  have pureF : Ensures (pure () : WG.M Unit) P (fun _ => P) := by
    intro _ _ _ _ _ h r; cases r; exact h
  unfold Queues.RxCredits.HandshakeCookiePayment.update
  refine ensures_bind _ _ read ?_
  intro p
  refine ensures_bind _ _ (branchF _ _) ?_
  intro missing
  cases missing with
  | true => exact pureF
  | false =>
    cases hc : xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24)
        ((msg.drop 32).take 32) p.lastMac1Sent with
    | none =>
      refine ensures_bind _ _ (branchF _ _) ?_
      intro ok
      cases ok with
      | false => exact pureF
      | true => intro _ _ _ _ _ _ r; cases r
    | some c =>
      refine ensures_bind _ _ (branchF _ _) ?_
      intro ok
      cases ok with
      | false => exact pureF
      | true =>
        refine ensures_bind _ _
          ((ensures_iff _ _ _).mpr
            (hoare_liftAmbient_variant (AmbientM.hiddenClock64 .cookieBirthdate) P)) ?_
        intro now
        exact modifyPeer_held entry pid _ (fun _ => rfl) (fun _ => rfl)

theorem cookieMessageConsume_tag_frame (msg : List UInt8) (entry : Option Device) :
    Ensures (cookieMessageConsume msg)
      (fun g => responseTagMap g.dev = responseTagMap entry)
      (fun _ g => responseTagMap g.dev = responseTagMap entry) := by
  intro g ambient result final after pre run
  cases result
  rw [Queues.RxCredits.HandshakeCookiePayment.factor,
    MaterialOrigin.bind_ok_ambient] at run
  obtain ⟨found, middle, inputs, lookup, tail⟩ := run
  obtain ⟨same, held⟩ := indexLookup_spec_responseTagMap_variant
    [.handshake, .keypair] (u32le msg 4) entry g ambient found middle inputs pre lookup
  cases found with
  | none =>
    change Except.ok (((),middle),CounterWindow.record inputs .cookieLookupMiss true) =
      .ok (((),final),after) at tail
    cases tail
    exact same
  | some pair =>
    obtain ⟨owner,pid⟩ := pair
    change ((do Queues.RxCredits.HandshakeCookiePayment.update msg pid; peerPut (some pid) : WG.M Unit).run middle).run
      (CounterWindow.record inputs .cookieLookupMiss false) = .ok (((),final),after) at tail
    exact (ensures_bind _ _ (cookieUpdate_held msg pid entry)
      (fun _ => peerPut_spec_responseTagMap_variant entry pid))
      middle _ () final after ⟨same, held owner pid rfl⟩ tail

end Leanux.Proofs.WG.Noise.ReceptionTagSupport
