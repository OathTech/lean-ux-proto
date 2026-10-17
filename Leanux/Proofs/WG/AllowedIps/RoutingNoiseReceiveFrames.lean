import Leanux.Proofs.WG.AllowedIps.RoutingSessionFrames
import Leanux.Proofs.Framing.WGCookie
import Leanux.Proofs.WG.AllowedIps.RoutingAcquire
import Leanux.Proofs.WG.AllowedIps.RoutingAdmissionFrames
import Leanux.Proofs.WG.Lifetimes.CookieAccess

/-! Original incoming Noise and cookie routing frames. Actual peer reference
release may retire a resident slot, so the endpoint relation preserves only
surviving lists. The source getters justify every peer write; no initial
residency, public-key affiliation or reference-credit premise is needed. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

theorem pubkeyLookup_routing (key : Key) : SameView routingView (pubkeyLookup key) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient result v ambient' hr
  exact (pubkeyLookup_routed key hr).1

/-- Arbitrary product actions retain the original cookie-masked store premise. -/
theorem cookie_routing (a : Leanux.M α) (ha : SameView productCookieView a) :
    SameView (fun w : World => routingView w.wg) a := by
  apply ha.of_factor (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg)
  intro w
  simp only [productCookieView, cookieStoreView, cookieView, wgOwnedView,
    wgStoreView, cookieDevice, routingView, Option.map_map, Function.comp_def]
  rfl

/-- Concrete cookie calls execute in the WireGuard world. -/
theorem cookie_routing_native (a : WG.M α) (ha : SameCookie a) :
    SameView routingView a := by
  apply ha.of_factor (fun store : WGOwnedView => store.dev.map routingState) routingView
  intro w
  simp only [cookieView, wgOwnedView, wgStoreView, cookieDevice, routingView,
    Option.map_map, Function.comp_def]
  rfl

theorem consumeInitiation_routing (msg : List UInt8) : RetainsRoutingCall (consumeInitiation msg) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have put (pid : Option PeerId) : Preserves P (peerPut pid) := RetainsRoutingCall.wp (peerPut_retainsRouting pid) s
  let write (pid : PeerId) (f : Peer → Peer) : WG.M Unit := do
    let p ← getPeer pid
    setPeer pid (f p)
  have edit (pid : PeerId) (f : Peer → Peer) (hf : ∀ p, (f p).allowedipsList = p.allowedipsList) :
      Preserves P (write pid f) := (modifyPeer_routing pid f hf).wp Q
  have ephemeral := fun b e ck h => show Preserves P _ from (messageEphemeral_sameWGWorld b e ck h).wp P
  have dh := fun b ck p q => show Preserves P _ from (mixDh_sameWGWorld b ck p q).wp P
  have decrypt := fun a k h => show Preserves P _ from (messageDecrypt_sameWGWorld a k h).wp P
  have precomputed := fun ck p => show Preserves P _ from (mixPrecomputedDh_sameWGWorld ck p).wp P
  have lookup (k : Key) : Preserves P (pubkeyLookup k) := (pubkeyLookup_routing k).wp Q
  let out (peer : Option PeerId) (ret : Option PeerId) : WG.M (Option PeerId) := do
    if ← branch .consumeFailedPut ret.isNone then peerPut peer
    return ret
  have done (peer : Option PeerId) (ret : Option PeerId) : Preserves P (out peer ret) := by
    routing_tx_source [out] using [put, ambient]
  have source : consumeInitiation msg = (do
      let identity := (← getDev).staticIdentity
      if ← branch .consumeNoIdentity !identity.hasIdentity then return ← out none none
      -- handshake_init: the precomputed initial chaining key and hash
      let hash := noiseHash (handshakeInitHash ++ identity.staticPublic)
      let e := (msg.drop 8).take 32
      let (ck, hash) ← messageEphemeral true e handshakeInitChainingKey hash
      let es ← mixDh true ck identity.staticPrivate e
      if ← branch .consumeEsFailed es.isNone then return ← out none none
      let some (ck, key) := es | invariant "unreachable"
      let st ← messageDecrypt ((msg.drop 40).take 48) key hash
      if ← branch .consumeStaticFailed st.isNone then return ← out none none
      let some (s, hash) := st | invariant "unreachable"
      let peer ← pubkeyLookup s
      if ← branch .consumeNoPeer peer.isNone then return ← out none none
      let some pid := peer | invariant "unreachable"
      let ss ← mixPrecomputedDh ck (← getPeer pid).precomputedStaticStatic
      if ← branch .consumeSsFailed ss.isNone then return ← out peer none
      let some (ckSs, key) := ss | invariant "unreachable"
      let ts ← messageDecrypt ((msg.drop 88).take 28) key hash
      if ← branch .consumeTimestampFailed ts.isNone then return ← out peer none
      let some (t, hashT) := ts | invariant "unreachable"
      let p ← getPeer pid
      let replay := memcmp t p.latestTimestamp != .gt
      -- `(s64)last_initiation_consumption + NSEC_PER_SEC / INITIATIONS_PER_SECOND
      -- > (s64)ktime_get_coarse_boottime_ns()`, computed before the test
      let floodLhs : Int64 := p.lastInitiationConsumption + NSEC_PER_SEC64 / INITIATIONS_PER_SECOND.toInt64
      let now ← hiddenClock64 .floodNow
      if ← WG.orM (branch .consumeReplay replay) (branchCmp .consumeFlood (floodLhs > now) floodLhs.toInt now.toInt) then
        return ← out peer none
      -- Success! Copy everything to peer
      write pid (fun p => {p with remoteEphemeral := e })
      if ← branch .consumeNewerTimestamp (memcmp t p.latestTimestamp == .gt) then
        write pid (fun p => {p with latestTimestamp := t })
      write pid (fun p => {p with hash := hashT, chainingKey := ckSs, remoteIndex := u32le msg 4 })
      -- `(s64)(last_initiation_consumption - (initiation_consumption = now)) < 0`
      let consumption ← hiddenClock64 .consumptionNow
      let last := (← getPeer pid).lastInitiationConsumption
      let diff : Int64 := last - consumption
      if ← branchCmp .consumeLaterTime (diff < 0) diff.toInt 0 then
        write pid (fun p => {p with lastInitiationConsumption := consumption })
      write pid (fun p => {p with handshakeState := HANDSHAKE_CONSUMED_INITIATION })
      out peer (some pid)
    ) := by
    simp only [consumeInitiation, write, out, bind_assoc]
    all_goals rfl
  have conditional {α : Type} (test : Prop) [Decidable test] (yes no : WG.M α)
      (hy : Preserves P yes) (hn : Preserves P no) : Preserves P (if test then yes else no) := by
    split <;> assumption
  have main : Preserves P (consumeInitiation msg) := by
    rw [source]
    routing_tx_source [hiddenClock64] using [conditional, done, edit, peer, device, put, ephemeral, dh, decrypt, precomputed, lookup, ambient]
    all_goals rfl
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem consumeResponse_routing (msg : List UInt8) : RetainsRoutingCall (consumeResponse msg) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have put (pid : Option PeerId) : Preserves P (peerPut pid) := RetainsRoutingCall.wp (peerPut_retainsRouting pid) s
  let write (pid : PeerId) (f : Peer → Peer) : WG.M Unit := do
    let p ← getPeer pid
    setPeer pid (f p)
  have edit (pid : PeerId) (f : Peer → Peer) (hf : ∀ p, (f p).allowedipsList = p.allowedipsList) :
      Preserves P (write pid f) := (modifyPeer_routing pid f hf).wp Q
  have ephemeral := fun b e ck h => show Preserves P _ from (messageEphemeral_sameWGWorld b e ck h).wp P
  have dh := fun b ck p q => show Preserves P _ from (mixDh_sameWGWorld b ck p q).wp P
  have decrypt := fun a k h => show Preserves P _ from (messageDecrypt_sameWGWorld a k h).wp P
  have lookup := fun ks i => show Preserves P _ from (indexLookup_routing ks i).wp Q
  have derive := fun b c ck d => show Preserves P _ from (Framing.kdf_sameWGWorld b c ck d).wp P
  have output := fun xs i => show Preserves P _ from (Framing.kdfOut_sameWGWorld xs i).wp P
  have source : consumeResponse msg = (do
      let identity := (← getDev).staticIdentity
      if ← branch .crespNoIdentity !identity.hasIdentity then return none
      -- `src->receiver_index`, of a handshake
      let entry ← indexLookup [.handshake] (u32le msg 8)
      if ← branch .crespNoHandshake entry.isNone then return none
      -- `handshake = (struct noise_handshake *)entry` (the owner, a peer's
      -- handshake), `peer` the lookup's reference (peerlookup.c:220)
      let some (IndexOwner.handshake _, pid) := entry | invariant "a keypair entry under the handshake mask"
      let fail : WG.M (Option PeerId) := do
        peerPut (some pid)
        return none
      -- the copies taken under the read lock
      let p ← getPeer pid
      let state := p.handshakeState
      if ← branch .crespNotCreatedInitiation (state != HANDSHAKE_CREATED_INITIATION) then return ← fail
      -- e
      let eph := (msg.drop 12).take 32
      let (ck, h) ← messageEphemeral true eph p.chainingKey p.hash
      -- ee
      let ee ← mixDh false ck p.ephemeralPrivate eph
      if ← branch .crespEeFailed ee.isNone then return ← fail
      let some (ck, _) := ee | invariant "unreachable"
      -- se
      let se ← mixDh false ck identity.staticPrivate eph
      if ← branch .crespSeFailed se.isNone then return ← fail
      let some (ck, _) := se | invariant "unreachable"
      -- psk: mix_psk (kdf with three outputs, then mix_hash of the second)
      let outs ← kdf true true ck p.presharedKey
      let (ck, tempHash, key) := (← kdfOut outs 0, ← kdfOut outs 1, ← kdfOut outs 2)
      let h := noiseHash (h ++ tempHash)
      -- {}
      let dec ← messageDecrypt ((msg.drop 44).take 16) key h
      if ← branch .crespDecryptFailed dec.isNone then return ← fail
      let some (_, h) := dec | invariant "unreachable"
      -- the state recheck under the write lock (one CPU: nothing ran meanwhile)
      if ← branch .crespStateChanged ((← getPeer pid).handshakeState != state) then return ← fail
      write pid (fun p => {p with remoteEphemeral := eph, hash := h, chainingKey := ck,
                                         remoteIndex := u32le msg 4, handshakeState := HANDSHAKE_CONSUMED_RESPONSE })
      return some pid
    ) := by
    simp only [consumeResponse, write, bind_assoc]
    all_goals rfl
  have main : Preserves P (consumeResponse msg) := by
    rw [source]
    routing_tx_source [] using [edit, peer, device, put, ephemeral, dh, decrypt, lookup, derive, output, ambient]
    all_goals rfl
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem cookieMessageConsume_routing (msg : List UInt8) :
    RetainsRoutingCall (cookieMessageConsume msg) := by
  intro s
  let Q : Option RoutingState → Prop := RetainsRouting s
  let P := fun w : WGWorld => Q (routingView w)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : WG.M α) := hoare_liftAmbient a P
  have peer (pid : PeerId) : Preserves P (getPeer pid) := (getPeer_routing pid).wp Q
  have device : Preserves P getDev := (routing_kernel _ getDev_sameWGStore).wp Q
  have put (pid : Option PeerId) : Preserves P (peerPut pid) := RetainsRoutingCall.wp (peerPut_retainsRouting pid) s
  let write (pid : PeerId) (f : Peer → Peer) : WG.M Unit := do
    let p ← getPeer pid
    setPeer pid (f p)
  have edit (pid : PeerId) (f : Peer → Peer) (hf : ∀ p, (f p).allowedipsList = p.allowedipsList) :
      Preserves P (write pid f) := (modifyPeer_routing pid f hf).wp Q
  have lookup := fun ks i => show Preserves P _ from (indexLookup_routing ks i).wp Q
  have source : cookieMessageConsume msg = (do
      -- `src->receiver_index`, of a handshake or a keypair
      let entry ← indexLookup [.handshake, .keypair] (u32le msg 4)
      if ← branch .cookieLookupMiss entry.isNone then return
      let some (_, pid) := entry | invariant "unreachable"   -- `peer`, the lookup's reference (peerlookup.c:220)
      let p ← getPeer pid
      if ← branch .cookieNoMac1Sent !p.haveSentMac1 then
        peerPut (some pid)   -- goto out
        return
      -- xchacha20poly1305_decrypt(cookie, encrypted_cookie, 32, last_mac1_sent,
      -- COOKIE_LEN, nonce, cookie_decryption_key)
      let cookie := xchachaDecrypt p.cookieDecryptionKey ((msg.drop 8).take 24) ((msg.drop 32).take 32) p.lastMac1Sent
      if ← branch .cookieDecryptOk cookie.isSome then
        let some c := cookie | invariant "unreachable"
        let birthdate ← hiddenClock64 .cookieBirthdate
        write pid (fun p => {p with cookie := c, cookieBirthdate := birthdate, cookieIsValid := true,
                                           haveSentMac1 := false })
      peerPut (some pid)   -- out:
    ) := by
    simp only [cookieMessageConsume, write, bind_assoc]
    all_goals rfl
  have main : Preserves P (cookieMessageConsume msg) := by
    rw [source]
    routing_tx_source [hiddenClock64] using [edit, peer, device, put, lookup, ambient]
    all_goals rfl
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s _
    dsimp only [id] at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.AllowedIps
